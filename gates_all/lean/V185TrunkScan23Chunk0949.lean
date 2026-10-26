import V185TrunkScan23Chunk0948

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5617848 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 2, 2, 5]
def baseStart_5617848 : Nat := 118140960795 + 5617848 * 2 ^ 59
def prefixEnd_5617848 : Nat := 4983230072969 + 3 ^ 40 * 5617848 * 2
def baseEnd_5617848 : Nat := 2884656267899641377563993

theorem tailTrace_5617848 : CollatzResearch.WordTrace tailWord_5617848 prefixEnd_5617848 2884656267899641377563993 := by
  unfold tailWord_5617848
  simp only [CollatzResearch.WordTrace]
  refine ⟨102449874875751811448815099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136599833167669081931753465 102449874875751811448815099)
  ·
    refine ⟨153674812313627717173222649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102449874875751811448815099 153674812313627717173222649)
    ·
      refine ⟨115256109235220787879916987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153674812313627717173222649 115256109235220787879916987)
      ·
        refine ⟨172884163852831181819875481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115256109235220787879916987 172884163852831181819875481)
        ·
          refine ⟨129663122889623386364906611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172884163852831181819875481 129663122889623386364906611)
          ·
            refine ⟨194494684334435079547359917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129663122889623386364906611 194494684334435079547359917)
            ·
              refine ⟨72935506625413154830259969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194494684334435079547359917 72935506625413154830259969)
              ·
                refine ⟨54701629969059866122694977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72935506625413154830259969 54701629969059866122694977)
                ·
                  refine ⟨41026222476794899592021233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54701629969059866122694977 41026222476794899592021233)
                  ·
                    refine ⟨30769666857596174694015925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41026222476794899592021233 30769666857596174694015925)
                    ·
                      refine ⟨2884656267899641377563993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30769666857596174694015925 2884656267899641377563993)
                      ·
                        rfl

theorem cell23_5617848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_5617848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617848 prefixEnd_5617848 := by exact prefixLift 5617848
  have htrace : WordTrace (prefixWord ++ tailWord_5617848) baseStart_5617848 baseEnd_5617848 := by
    simpa [prefixWord, tailWord_5617848, baseEnd_5617848] using wordTrace_append hprefix tailTrace_5617848
  have hstable : (prefixWord ++ tailWord_5617848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617848).length < 2 ^ (prefixWord ++ tailWord_5617848).sum := by decide
  have hdescent : baseEnd_5617848 < baseStart_5617848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617890 : List Nat := [3, 3, 4, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_5617890 : Nat := 118140960795 + 5617890 * 2 ^ 59
def prefixEnd_5617890 : Nat := 4983230072969 + 3 ^ 40 * 5617890 * 2
def baseEnd_5617890 : Nat := 2884677834087130213238801

theorem tailTrace_5617890 : CollatzResearch.WordTrace tailWord_5617890 prefixEnd_5617890 2884677834087130213238801 := by
  unfold tailWord_5617890
  simp only [CollatzResearch.WordTrace]
  refine ⟨51225320404337866017664781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136600854411567642713772749 51225320404337866017664781)
  ·
    refine ⟨19209495151626699756624293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51225320404337866017664781 19209495151626699756624293)
    ·
      refine ⟨3601780340930006204367055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19209495151626699756624293 3601780340930006204367055)
      ·
        refine ⟨5402670511395009306550583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3601780340930006204367055 5402670511395009306550583)
        ·
          refine ⟨8104005767092513959825875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5402670511395009306550583 8104005767092513959825875)
          ·
            refine ⟨12156008650638770939738813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8104005767092513959825875 12156008650638770939738813)
            ·
              refine ⟨4558503243989539102402055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12156008650638770939738813 4558503243989539102402055)
              ·
                refine ⟨6837754865984308653603083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4558503243989539102402055 6837754865984308653603083)
                ·
                  refine ⟨10256632298976462980404625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6837754865984308653603083 10256632298976462980404625)
                  ·
                    refine ⟨7692474224232347235303469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10256632298976462980404625 7692474224232347235303469)
                    ·
                      refine ⟨2884677834087130213238801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7692474224232347235303469 2884677834087130213238801)
                      ·
                        rfl

theorem cell23_5617890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_5617890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617890 prefixEnd_5617890 := by exact prefixLift 5617890
  have htrace : WordTrace (prefixWord ++ tailWord_5617890) baseStart_5617890 baseEnd_5617890 := by
    simpa [prefixWord, tailWord_5617890, baseEnd_5617890] using wordTrace_append hprefix tailTrace_5617890
  have hstable : (prefixWord ++ tailWord_5617890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617890).length < 2 ^ (prefixWord ++ tailWord_5617890).sum := by decide
  have hdescent : baseEnd_5617890 < baseStart_5617890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617896 : List Nat := [2, 1, 4, 1, 2, 3, 3, 1, 1, 3, 2]
def baseStart_5617896 : Nat := 118140960795 + 5617896 * 2 ^ 59
def prefixEnd_5617896 : Nat := 4983230072969 + 3 ^ 40 * 5617896 * 2
def baseEnd_5617896 : Nat := 2884680914971057189763773

theorem tailTrace_5617896 : CollatzResearch.WordTrace tailWord_5617896 prefixEnd_5617896 2884680914971057189763773 := by
  unfold tailWord_5617896
  simp only [CollatzResearch.WordTrace]
  refine ⟨102450750227664863547688771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136601000303553151396918361 102450750227664863547688771)
  ·
    refine ⟨153676125341497295321533157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102450750227664863547688771 153676125341497295321533157)
    ·
      refine ⟨28814273501530742872787467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153676125341497295321533157 28814273501530742872787467)
      ·
        refine ⟨43221410252296114309181201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28814273501530742872787467 43221410252296114309181201)
        ·
          refine ⟨32416057689222085731885901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43221410252296114309181201 32416057689222085731885901)
          ·
            refine ⟨12156021633458282149457213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32416057689222085731885901 12156021633458282149457213)
            ·
              refine ⟨4558508112546855806046455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12156021633458282149457213 4558508112546855806046455)
              ·
                refine ⟨6837762168820283709069683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4558508112546855806046455 6837762168820283709069683)
                ·
                  refine ⟨10256643253230425563604525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6837762168820283709069683 10256643253230425563604525)
                  ·
                    refine ⟨3846241219961409586351697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10256643253230425563604525 3846241219961409586351697)
                    ·
                      refine ⟨2884680914971057189763773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3846241219961409586351697 2884680914971057189763773)
                      ·
                        rfl

theorem cell23_5617896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_5617896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617896 prefixEnd_5617896 := by exact prefixLift 5617896
  have htrace : WordTrace (prefixWord ++ tailWord_5617896) baseStart_5617896 baseEnd_5617896 := by
    simpa [prefixWord, tailWord_5617896, baseEnd_5617896] using wordTrace_append hprefix tailTrace_5617896
  have hstable : (prefixWord ++ tailWord_5617896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617896).length < 2 ^ (prefixWord ++ tailWord_5617896).sum := by decide
  have hdescent : baseEnd_5617896 < baseStart_5617896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617922 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_5617922 : Nat := 118140960795 + 5617922 * 2 ^ 59
def prefixEnd_5617922 : Nat := 4983230072969 + 3 ^ 40 * 5617922 * 2
def baseEnd_5617922 : Nat := 2884694265468074088038653

theorem tailTrace_5617922 : CollatzResearch.WordTrace tailWord_5617922 prefixEnd_5617922 2884694265468074088038653 := by
  unfold tailWord_5617922
  simp only [CollatzResearch.WordTrace]
  refine ⟨51225612188308883383956005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136601632502157022357216013 51225612188308883383956005)
  ·
    refine ⟨9604802285307915634491751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51225612188308883383956005 9604802285307915634491751)
    ·
      refine ⟨14407203427961873451737627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9604802285307915634491751 14407203427961873451737627)
      ·
        refine ⟨21610805141942810177606441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14407203427961873451737627 21610805141942810177606441)
        ·
          refine ⟨16208103856457107633204831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21610805141942810177606441 16208103856457107633204831)
          ·
            refine ⟨24312155784685661449807247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16208103856457107633204831 24312155784685661449807247)
            ·
              refine ⟨36468233677028492174710871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24312155784685661449807247 36468233677028492174710871)
              ·
                refine ⟨54702350515542738262066307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36468233677028492174710871 54702350515542738262066307)
                ·
                  refine ⟨82053525773314107393099461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54702350515542738262066307 82053525773314107393099461)
                  ·
                    refine ⟨15385036082496395136206149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82053525773314107393099461 15385036082496395136206149)
                    ·
                      refine ⟨2884694265468074088038653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15385036082496395136206149 2884694265468074088038653)
                      ·
                        rfl

theorem cell23_5617922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_5617922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617922 prefixEnd_5617922 := by exact prefixLift 5617922
  have htrace : WordTrace (prefixWord ++ tailWord_5617922) baseStart_5617922 baseEnd_5617922 := by
    simpa [prefixWord, tailWord_5617922, baseEnd_5617922] using wordTrace_append hprefix tailTrace_5617922
  have hstable : (prefixWord ++ tailWord_5617922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617922).length < 2 ^ (prefixWord ++ tailWord_5617922).sum := by decide
  have hdescent : baseEnd_5617922 < baseStart_5617922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617960 : List Nat := [2, 1, 5, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_5617960 : Nat := 118140960795 + 5617960 * 2 ^ 59
def prefixEnd_5617960 : Nat := 4983230072969 + 3 ^ 40 * 5617960 * 2
def baseEnd_5617960 : Nat := 2884713777732944939363479

theorem tailTrace_5617960 : CollatzResearch.WordTrace tailWord_5617960 prefixEnd_5617960 2884713777732944939363479 := by
  unfold tailWord_5617960
  simp only [CollatzResearch.WordTrace]
  refine ⟨102451917363548933012853667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136602556484731910683804889 102451917363548933012853667)
  ·
    refine ⟨153677876045323399519280501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102451917363548933012853667 153677876045323399519280501)
    ·
      refine ⟨14407300879249068704932547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153677876045323399519280501 14407300879249068704932547)
      ·
        refine ⟨21610951318873603057398821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14407300879249068704932547 21610951318873603057398821)
        ·
          refine ⟨4052053372288800573262279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21610951318873603057398821 4052053372288800573262279)
          ·
            refine ⟨6078080058433200859893419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4052053372288800573262279 6078080058433200859893419)
            ·
              refine ⟨9117120087649801289840129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6078080058433200859893419 9117120087649801289840129)
              ·
                refine ⟨6837840065737350967380097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9117120087649801289840129 6837840065737350967380097)
                ·
                  refine ⟨5128380049303013225535073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6837840065737350967380097 5128380049303013225535073)
                  ·
                    refine ⟨3846285036977259919151305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5128380049303013225535073 3846285036977259919151305)
                    ·
                      refine ⟨2884713777732944939363479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3846285036977259919151305 2884713777732944939363479)
                      ·
                        rfl

theorem cell23_5617960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_5617960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617960 prefixEnd_5617960 := by exact prefixLift 5617960
  have htrace : WordTrace (prefixWord ++ tailWord_5617960) baseStart_5617960 baseEnd_5617960 := by
    simpa [prefixWord, tailWord_5617960, baseEnd_5617960] using wordTrace_append hprefix tailTrace_5617960
  have hstable : (prefixWord ++ tailWord_5617960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617960).length < 2 ^ (prefixWord ++ tailWord_5617960).sum := by decide
  have hdescent : baseEnd_5617960 < baseStart_5617960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617982 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_5617982 : Nat := 118140960795 + 5617982 * 2 ^ 59
def prefixEnd_5617982 : Nat := 4983230072969 + 3 ^ 40 * 5617982 * 2
def baseEnd_5617982 : Nat := 2884725074307343853288377

theorem tailTrace_5617982 : CollatzResearch.WordTrace tailWord_5617982 prefixEnd_5617982 2884725074307343853288377 := by
  unfold tailWord_5617982
  simp only [CollatzResearch.WordTrace]
  refine ⟨25613079641627270472876025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136603091422012109188672133 25613079641627270472876025)
  ·
    refine ⟨19209809731220452854657019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25613079641627270472876025 19209809731220452854657019)
    ·
      refine ⟨28814714596830679281985529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19209809731220452854657019 28814714596830679281985529)
      ·
        refine ⟨21611035947623009461489147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28814714596830679281985529 21611035947623009461489147)
        ·
          refine ⟨32416553921434514192233721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21611035947623009461489147 32416553921434514192233721)
          ·
            refine ⟨24312415441075885644175291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32416553921434514192233721 24312415441075885644175291)
            ·
              refine ⟨36468623161613828466262937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24312415441075885644175291 36468623161613828466262937)
              ·
                refine ⟨27351467371210371349697203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36468623161613828466262937 27351467371210371349697203)
                ·
                  refine ⟨41027201056815557024545805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27351467371210371349697203 41027201056815557024545805)
                  ·
                    refine ⟨15385200396305833884204677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41027201056815557024545805 15385200396305833884204677)
                    ·
                      refine ⟨2884725074307343853288377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15385200396305833884204677 2884725074307343853288377)
                      ·
                        rfl

theorem cell23_5617982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_5617982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617982 prefixEnd_5617982 := by exact prefixLift 5617982
  have htrace : WordTrace (prefixWord ++ tailWord_5617982) baseStart_5617982 baseEnd_5617982 := by
    simpa [prefixWord, tailWord_5617982, baseEnd_5617982] using wordTrace_append hprefix tailTrace_5617982
  have hstable : (prefixWord ++ tailWord_5617982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617982).length < 2 ^ (prefixWord ++ tailWord_5617982).sum := by decide
  have hdescent : baseEnd_5617982 < baseStart_5617982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617992 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 3, 4]
def baseStart_5617992 : Nat := 118140960795 + 5617992 * 2 ^ 59
def prefixEnd_5617992 : Nat := 4983230072969 + 3 ^ 40 * 5617992 * 2
def baseEnd_5617992 : Nat := 961576736371296271387777

theorem tailTrace_5617992 : CollatzResearch.WordTrace tailWord_5617992 prefixEnd_5617992 961576736371296271387777 := by
  unfold tailWord_5617992
  simp only [CollatzResearch.WordTrace]
  refine ⟨102452500931490967745436115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136603334575321290327248153 102452500931490967745436115)
  ·
    refine ⟨153678751397236451618154173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102452500931490967745436115 153678751397236451618154173)
    ·
      refine ⟨57629531773963669356807815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153678751397236451618154173 57629531773963669356807815)
      ·
        refine ⟨86444297660945504035211723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57629531773963669356807815 86444297660945504035211723)
        ·
          refine ⟨129666446491418256052817585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86444297660945504035211723 129666446491418256052817585)
          ·
            refine ⟨97249834868563692039613189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129666446491418256052817585 97249834868563692039613189)
            ·
              refine ⟨18234344037855692257427473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97249834868563692039613189 18234344037855692257427473)
              ·
                refine ⟨13675758028391769193070605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18234344037855692257427473 13675758028391769193070605)
                ·
                  refine ⟨5128409260646913447401477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13675758028391769193070605 5128409260646913447401477)
                  ·
                    refine ⟨961576736371296271387777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5128409260646913447401477 961576736371296271387777)
                    ·
                      rfl

theorem cell23_5617992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_5617992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617992 prefixEnd_5617992 := by exact prefixLift 5617992
  have htrace : WordTrace (prefixWord ++ tailWord_5617992) baseStart_5617992 baseEnd_5617992 := by
    simpa [prefixWord, tailWord_5617992, baseEnd_5617992] using wordTrace_append hprefix tailTrace_5617992
  have hstable : (prefixWord ++ tailWord_5617992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617992).length < 2 ^ (prefixWord ++ tailWord_5617992).sum := by decide
  have hdescent : baseEnd_5617992 < baseStart_5617992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618002 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_5618002 : Nat := 118140960795 + 5618002 * 2 ^ 59
def prefixEnd_5618002 : Nat := 4983230072969 + 3 ^ 40 * 5618002 * 2
def baseEnd_5618002 : Nat := 2884735343920433775038285

theorem tailTrace_5618002 : CollatzResearch.WordTrace tailWord_5618002 prefixEnd_5618002 2884735343920433775038285 := by
  unfold tailWord_5618002
  simp only [CollatzResearch.WordTrace]
  refine ⟨51226341648236426799684065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136603577728630471465824173 51226341648236426799684065)
  ·
    refine ⟨38419756236177320099763049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51226341648236426799684065 38419756236177320099763049)
    ·
      refine ⟨28814817177132990074822287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38419756236177320099763049 28814817177132990074822287)
      ·
        refine ⟨43222225765699485112233431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28814817177132990074822287 43222225765699485112233431)
        ·
          refine ⟨64833338648549227668350147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43222225765699485112233431 64833338648549227668350147)
          ·
            refine ⟨97250007972823841502525221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64833338648549227668350147 97250007972823841502525221)
            ·
              refine ⟨18234376494904470281723479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97250007972823841502525221 18234376494904470281723479)
              ·
                refine ⟨27351564742356705422585219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18234376494904470281723479 27351564742356705422585219)
                ·
                  refine ⟨41027347113535058133877829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27351564742356705422585219 41027347113535058133877829)
                  ·
                    refine ⟨7692627583787823400102093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41027347113535058133877829 7692627583787823400102093)
                    ·
                      refine ⟨2884735343920433775038285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7692627583787823400102093 2884735343920433775038285)
                      ·
                        rfl

theorem cell23_5618002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_5618002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618002 prefixEnd_5618002 := by exact prefixLift 5618002
  have htrace : WordTrace (prefixWord ++ tailWord_5618002) baseStart_5618002 baseEnd_5618002 := by
    simpa [prefixWord, tailWord_5618002, baseEnd_5618002] using wordTrace_append hprefix tailTrace_5618002
  have hstable : (prefixWord ++ tailWord_5618002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618002).length < 2 ^ (prefixWord ++ tailWord_5618002).sum := by decide
  have hdescent : baseEnd_5618002 < baseStart_5618002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618026 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 3, 4]
def baseStart_5618026 : Nat := 118140960795 + 5618026 * 2 ^ 59
def prefixEnd_5618026 : Nat := 4983230072969 + 3 ^ 40 * 5618026 * 2
def baseEnd_5618026 : Nat := 961582555818713893712725

theorem tailTrace_5618026 : CollatzResearch.WordTrace tailWord_5618026 prefixEnd_5618026 961582555818713893712725 := by
  unfold tailWord_5618026
  simp only [CollatzResearch.WordTrace]
  refine ⟨51226560486214689824402483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136604161296572506198406621 51226560486214689824402483)
  ·
    refine ⟨76839840729322034736603725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51226560486214689824402483 76839840729322034736603725)
    ·
      refine ⟨28814940273495763026226397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76839840729322034736603725 28814940273495763026226397)
      ·
        refine ⟨10805602602560911134834899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28814940273495763026226397 10805602602560911134834899)
        ·
          refine ⟨16208403903841366702252349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10805602602560911134834899 16208403903841366702252349)
          ·
            refine ⟨6078151463940512513344631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16208403903841366702252349 6078151463940512513344631)
            ·
              refine ⟨9117227195910768770016947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6078151463940512513344631 9117227195910768770016947)
              ·
                refine ⟨13675840793866153155025421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9117227195910768770016947 13675840793866153155025421)
                ·
                  refine ⟨5128440297699807433134533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13675840793866153155025421 5128440297699807433134533)
                  ·
                    refine ⟨961582555818713893712725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5128440297699807433134533 961582555818713893712725)
                    ·
                      rfl

theorem cell23_5618026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_5618026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618026 prefixEnd_5618026 := by exact prefixLift 5618026
  have htrace : WordTrace (prefixWord ++ tailWord_5618026) baseStart_5618026 baseEnd_5618026 := by
    simpa [prefixWord, tailWord_5618026, baseEnd_5618026] using wordTrace_append hprefix tailTrace_5618026
  have hstable : (prefixWord ++ tailWord_5618026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618026).length < 2 ^ (prefixWord ++ tailWord_5618026).sum := by decide
  have hdescent : baseEnd_5618026 < baseStart_5618026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618035 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 5, 5]
def baseStart_5618035 : Nat := 118140960795 + 5618035 * 2 ^ 59
def prefixEnd_5618035 : Nat := 4983230072969 + 3 ^ 40 * 5618035 * 2
def baseEnd_5618035 : Nat := 961584096260677381975211

theorem tailTrace_5618035 : CollatzResearch.WordTrace tailWord_5618035 prefixEnd_5618035 961584096260677381975211 := by
  unfold tailWord_5618035
  simp only [CollatzResearch.WordTrace]
  refine ⟨204906570201826153834687559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136604380134550769223125039 204906570201826153834687559)
  ·
    refine ⟨307359855302739230752031339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204906570201826153834687559 307359855302739230752031339)
    ·
      refine ⟨461039782954108846128047009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307359855302739230752031339 461039782954108846128047009)
      ·
        refine ⟨345779837215581634596035257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461039782954108846128047009 345779837215581634596035257)
        ·
          refine ⟨259334877911686225947026443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345779837215581634596035257 259334877911686225947026443)
          ·
            refine ⟨389002316867529338920539665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259334877911686225947026443 389002316867529338920539665)
            ·
              refine ⟨291751737650647004190404749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389002316867529338920539665 291751737650647004190404749)
              ·
                refine ⟨109406901618992626571401781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291751737650647004190404749 109406901618992626571401781)
                ·
                  refine ⟨10256897026780558741068917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109406901618992626571401781 10256897026780558741068917)
                  ·
                    refine ⟨961584096260677381975211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10256897026780558741068917 961584096260677381975211)
                    ·
                      rfl

theorem cell23_5618035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 5].length) (baseStart_5618035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618035 prefixEnd_5618035 := by exact prefixLift 5618035
  have htrace : WordTrace (prefixWord ++ tailWord_5618035) baseStart_5618035 baseEnd_5618035 := by
    simpa [prefixWord, tailWord_5618035, baseEnd_5618035] using wordTrace_append hprefix tailTrace_5618035
  have hstable : (prefixWord ++ tailWord_5618035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618035).length < 2 ^ (prefixWord ++ tailWord_5618035).sum := by decide
  have hdescent : baseEnd_5618035 < baseStart_5618035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618052 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 3, 5]
def baseStart_5618052 : Nat := 118140960795 + 5618052 * 2 ^ 59
def prefixEnd_5618052 : Nat := 4983230072969 + 3 ^ 40 * 5618052 * 2
def baseEnd_5618052 : Nat := 961587005984386193137685

theorem tailTrace_5618052 : CollatzResearch.WordTrace tailWord_5618052 prefixEnd_5618052 961587005984386193137685 := by
  unfold tailWord_5618052
  simp only [CollatzResearch.WordTrace]
  refine ⟨102453595121382282869028205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136604793495176377158704273 102453595121382282869028205)
  ·
    refine ⟨38420098170518356075885577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102453595121382282869028205 38420098170518356075885577)
    ·
      refine ⟨28815073627888767056914183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38420098170518356075885577 28815073627888767056914183)
      ·
        refine ⟨43222610441833150585371275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28815073627888767056914183 43222610441833150585371275)
        ·
          refine ⟨64833915662749725878056913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43222610441833150585371275 64833915662749725878056913)
          ·
            refine ⟨48625436747062294408542685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64833915662749725878056913 48625436747062294408542685)
            ·
              refine ⟨18234538780148360403203507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48625436747062294408542685 18234538780148360403203507)
              ·
                refine ⟨27351808170222540604805261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18234538780148360403203507 27351808170222540604805261)
                ·
                  refine ⟨10256928063833452726801973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27351808170222540604805261 10256928063833452726801973)
                  ·
                    refine ⟨961587005984386193137685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10256928063833452726801973 961587005984386193137685)
                    ·
                      rfl

theorem cell23_5618052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_5618052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618052 prefixEnd_5618052 := by exact prefixLift 5618052
  have htrace : WordTrace (prefixWord ++ tailWord_5618052) baseStart_5618052 baseEnd_5618052 := by
    simpa [prefixWord, tailWord_5618052, baseEnd_5618052] using wordTrace_append hprefix tailTrace_5618052
  have hstable : (prefixWord ++ tailWord_5618052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618052).length < 2 ^ (prefixWord ++ tailWord_5618052).sum := by decide
  have hdescent : baseEnd_5618052 < baseStart_5618052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618059 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 2, 3, 2]
def baseStart_5618059 : Nat := 118140960795 + 5618059 * 2 ^ 59
def prefixEnd_5618059 : Nat := 4983230072969 + 3 ^ 40 * 5618059 * 2
def baseEnd_5618059 : Nat := 2884764612317740052025523

theorem tailTrace_5618059 : CollatzResearch.WordTrace tailWord_5618059 prefixEnd_5618059 2884764612317740052025523 := by
  unfold tailWord_5618059
  simp only [CollatzResearch.WordTrace]
  refine ⟨204907445553739205933561231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136604963702492803955707487 204907445553739205933561231)
  ·
    refine ⟨307361168330608808900341847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204907445553739205933561231 307361168330608808900341847)
    ·
      refine ⟨461041752495913213350512771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307361168330608808900341847 461041752495913213350512771)
      ·
        refine ⟨691562628743869820025769157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461041752495913213350512771 691562628743869820025769157)
        ·
          refine ⟨129667992889475591254831717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 691562628743869820025769157 129667992889475591254831717)
          ·
            refine ⟨24312748666776673360280947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129667992889475591254831717 24312748666776673360280947)
            ·
              refine ⟨36469123000165010040421421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24312748666776673360280947 36469123000165010040421421)
              ·
                refine ⟨13675921125061878765158033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36469123000165010040421421 13675921125061878765158033)
                ·
                  refine ⟨10256940843796409073868525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13675921125061878765158033 10256940843796409073868525)
                  ·
                    refine ⟨3846352816423653402700697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10256940843796409073868525 3846352816423653402700697)
                    ·
                      refine ⟨2884764612317740052025523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3846352816423653402700697 2884764612317740052025523)
                      ·
                        rfl

theorem cell23_5618059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 3, 2].length) (baseStart_5618059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618059 prefixEnd_5618059 := by exact prefixLift 5618059
  have htrace : WordTrace (prefixWord ++ tailWord_5618059) baseStart_5618059 baseEnd_5618059 := by
    simpa [prefixWord, tailWord_5618059, baseEnd_5618059] using wordTrace_append hprefix tailTrace_5618059
  have hstable : (prefixWord ++ tailWord_5618059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618059).length < 2 ^ (prefixWord ++ tailWord_5618059).sum := by decide
  have hdescent : baseEnd_5618059 < baseStart_5618059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618082 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_5618082 : Nat := 118140960795 + 5618082 * 2 ^ 59
def prefixEnd_5618082 : Nat := 4983230072969 + 3 ^ 40 * 5618082 * 2
def baseEnd_5618082 : Nat := 961592140790931154012639

theorem tailTrace_5618082 : CollatzResearch.WordTrace tailWord_5618082 prefixEnd_5618082 961592140790931154012639 := by
  unfold tailWord_5618082
  simp only [CollatzResearch.WordTrace]
  refine ⟨51227071108163970215412125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136605522955103920574432333 51227071108163970215412125)
  ·
    refine ⟨19210151665561488830779547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51227071108163970215412125 19210151665561488830779547)
    ·
      refine ⟨28815227498342233246169321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19210151665561488830779547 28815227498342233246169321)
      ·
        refine ⟨21611420623756674934626991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28815227498342233246169321 21611420623756674934626991)
        ·
          refine ⟨32417130935635012401940487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21611420623756674934626991 32417130935635012401940487)
          ·
            refine ⟨48625696403452518602910731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32417130935635012401940487 48625696403452518602910731)
            ·
              refine ⟨72938544605178777904366097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48625696403452518602910731 72938544605178777904366097)
              ·
                refine ⟨54703908453884083428274573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72938544605178777904366097 54703908453884083428274573)
                ·
                  refine ⟨20513965670206531285602965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54703908453884083428274573 20513965670206531285602965)
                  ·
                    refine ⟨961592140790931154012639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20513965670206531285602965 961592140790931154012639)
                    ·
                      rfl

theorem cell23_5618082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_5618082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618082 prefixEnd_5618082 := by exact prefixLift 5618082
  have htrace : WordTrace (prefixWord ++ tailWord_5618082) baseStart_5618082 baseEnd_5618082 := by
    simpa [prefixWord, tailWord_5618082, baseEnd_5618082] using wordTrace_append hprefix tailTrace_5618082
  have hstable : (prefixWord ++ tailWord_5618082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618082).length < 2 ^ (prefixWord ++ tailWord_5618082).sum := by decide
  have hdescent : baseEnd_5618082 < baseStart_5618082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618083 : List Nat := [1, 1, 1, 4, 1, 4, 4, 2, 1, 1, 3]
def baseStart_5618083 : Nat := 118140960795 + 5618083 * 2 ^ 59
def prefixEnd_5618083 : Nat := 4983230072969 + 3 ^ 40 * 5618083 * 2
def baseEnd_5618083 : Nat := 2884776935853447958125413

theorem tailTrace_5618083 : CollatzResearch.WordTrace tailWord_5618083 prefixEnd_5618083 2884776935853447958125413 := by
  unfold tailWord_5618083
  simp only [CollatzResearch.WordTrace]
  refine ⟨204908320905652258032434903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136605547270434838688289935 204908320905652258032434903)
  ·
    refine ⟨307362481358478387048652355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204908320905652258032434903 307362481358478387048652355)
    ·
      refine ⟨461043722037717580572978533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307362481358478387048652355 461043722037717580572978533)
      ·
        refine ⟨86445697882072046357433475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 461043722037717580572978533 86445697882072046357433475)
        ·
          refine ⟨129668546823108069536150213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86445697882072046357433475 129668546823108069536150213)
          ·
            refine ⟨24312852529332763038028165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129668546823108069536150213 24312852529332763038028165)
            ·
              refine ⟨4558659849249893069630281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24312852529332763038028165 4558659849249893069630281)
              ·
                refine ⟨3418994886937419802222711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4558659849249893069630281 3418994886937419802222711)
                ·
                  refine ⟨5128492330406129703334067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3418994886937419802222711 5128492330406129703334067)
                  ·
                    refine ⟨7692738495609194555001101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5128492330406129703334067 7692738495609194555001101)
                    ·
                      refine ⟨2884776935853447958125413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7692738495609194555001101 2884776935853447958125413)
                      ·
                        rfl

theorem cell23_5618083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_5618083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618083 prefixEnd_5618083 := by exact prefixLift 5618083
  have htrace : WordTrace (prefixWord ++ tailWord_5618083) baseStart_5618083 baseEnd_5618083 := by
    simpa [prefixWord, tailWord_5618083, baseEnd_5618083] using wordTrace_append hprefix tailTrace_5618083
  have hstable : (prefixWord ++ tailWord_5618083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618083).length < 2 ^ (prefixWord ++ tailWord_5618083).sum := by decide
  have hdescent : baseEnd_5618083 < baseStart_5618083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618089 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 7, 2, 2]
def baseStart_5618089 : Nat := 118140960795 + 5618089 * 2 ^ 59
def prefixEnd_5618089 : Nat := 4983230072969 + 3 ^ 40 * 5618089 * 2
def baseEnd_5618089 : Nat := 2884780016737374934650385

theorem tailTrace_5618089 : CollatzResearch.WordTrace tailWord_5618089 prefixEnd_5618089 2884780016737374934650385 := by
  unfold tailWord_5618089
  simp only [CollatzResearch.WordTrace]
  refine ⟨204908539743630521057153321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136605693162420347371435547 204908539743630521057153321)
  ·
    refine ⟨153681404807722890792864991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204908539743630521057153321 153681404807722890792864991)
    ·
      refine ⟨230522107211584336189297487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153681404807722890792864991 230522107211584336189297487)
      ·
        refine ⟨345783160817376504283946231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230522107211584336189297487 345783160817376504283946231)
        ·
          refine ⟨518674741226064756425919347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345783160817376504283946231 518674741226064756425919347)
          ·
            refine ⟨778012111839097134638879021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518674741226064756425919347 778012111839097134638879021)
            ·
              refine ⟨291754541939661425489579633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 778012111839097134638879021 291754541939661425489579633)
              ·
                refine ⟨218815906454746069117184725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291754541939661425489579633 218815906454746069117184725)
                ·
                  refine ⟨5128497807533110994934017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 218815906454746069117184725 5128497807533110994934017)
                  ·
                    refine ⟨3846373355649833246200513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5128497807533110994934017 3846373355649833246200513)
                    ·
                      refine ⟨2884780016737374934650385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3846373355649833246200513 2884780016737374934650385)
                      ·
                        rfl

theorem cell23_5618089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 2, 2].length) (baseStart_5618089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618089 prefixEnd_5618089 := by exact prefixLift 5618089
  have htrace : WordTrace (prefixWord ++ tailWord_5618089) baseStart_5618089 baseEnd_5618089 := by
    simpa [prefixWord, tailWord_5618089, baseEnd_5618089] using wordTrace_append hprefix tailTrace_5618089
  have hstable : (prefixWord ++ tailWord_5618089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618089).length < 2 ^ (prefixWord ++ tailWord_5618089).sum := by decide
  have hdescent : baseEnd_5618089 < baseStart_5618089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618100 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_5618100 : Nat := 118140960795 + 5618100 * 2 ^ 59
def prefixEnd_5618100 : Nat := 4983230072969 + 3 ^ 40 * 5618100 * 2
def baseEnd_5618100 : Nat := 2884785665024574391612835

theorem tailTrace_5618100 : CollatzResearch.WordTrace tailWord_5618100 prefixEnd_5618100 2884785665024574391612835 := by
  unfold tailWord_5618100
  simp only [CollatzResearch.WordTrace]
  refine ⟨102454470473295334967901877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136605960631060446623869169 102454470473295334967901877)
  ·
    refine ⟨9605106606871437653240801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102454470473295334967901877 9605106606871437653240801)
    ·
      refine ⟨7203829955153578239930601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9605106606871437653240801 7203829955153578239930601)
      ·
        refine ⟨5402872466365183679947951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7203829955153578239930601 5402872466365183679947951)
        ·
          refine ⟨8104308699547775519921927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5402872466365183679947951 8104308699547775519921927)
          ·
            refine ⟨12156463049321663279882891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8104308699547775519921927 12156463049321663279882891)
            ·
              refine ⟨18234694573982494919824337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12156463049321663279882891 18234694573982494919824337)
              ·
                refine ⟨13676020930486871189868253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18234694573982494919824337 13676020930486871189868253)
                ·
                  refine ⟨5128507848932576696200595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13676020930486871189868253 5128507848932576696200595)
                  ·
                    refine ⟨7692761773398865044300893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5128507848932576696200595 7692761773398865044300893)
                    ·
                      refine ⟨2884785665024574391612835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7692761773398865044300893 2884785665024574391612835)
                      ·
                        rfl

theorem cell23_5618100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_5618100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618100 prefixEnd_5618100 := by exact prefixLift 5618100
  have htrace : WordTrace (prefixWord ++ tailWord_5618100) baseStart_5618100 baseEnd_5618100 := by
    simpa [prefixWord, tailWord_5618100, baseEnd_5618100] using wordTrace_append hprefix tailTrace_5618100
  have hstable : (prefixWord ++ tailWord_5618100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618100).length < 2 ^ (prefixWord ++ tailWord_5618100).sum := by decide
  have hdescent : baseEnd_5618100 < baseStart_5618100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618109 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 3, 2, 3]
def baseStart_5618109 : Nat := 118140960795 + 5618109 * 2 ^ 59
def prefixEnd_5618109 : Nat := 4983230072969 + 3 ^ 40 * 5618109 * 2
def baseEnd_5618109 : Nat := 2884790286350464856400293

theorem tailTrace_5618109 : CollatzResearch.WordTrace tailWord_5618109 prefixEnd_5618109 2884790286350464856400293 := by
  unfold tailWord_5618109
  simp only [CollatzResearch.WordTrace]
  refine ⟨204909269203558064472881381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136606179469038709648587587 204909269203558064472881381)
  ·
    refine ⟨38420487975667137088665259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204909269203558064472881381 38420487975667137088665259)
    ·
      refine ⟨57630731963500705632997889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38420487975667137088665259 57630731963500705632997889)
      ·
        refine ⟨43223048972625529224748417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57630731963500705632997889 43223048972625529224748417)
        ·
          refine ⟨32417286729469146918561313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43223048972625529224748417 32417286729469146918561313)
          ·
            refine ⟨24312965047101860188920985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32417286729469146918561313 24312965047101860188920985)
            ·
              refine ⟨18234723785326395141690739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24312965047101860188920985 18234723785326395141690739)
              ·
                refine ⟨27352085677989592712536109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18234723785326395141690739 27352085677989592712536109)
                ·
                  refine ⟨10257032129246097267201041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27352085677989592712536109 10257032129246097267201041)
                  ·
                    refine ⟨7692774096934572950400781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10257032129246097267201041 7692774096934572950400781)
                    ·
                      refine ⟨2884790286350464856400293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7692774096934572950400781 2884790286350464856400293)
                      ·
                        rfl

theorem cell23_5618109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_5618109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618109 prefixEnd_5618109 := by exact prefixLift 5618109
  have htrace : WordTrace (prefixWord ++ tailWord_5618109) baseStart_5618109 baseEnd_5618109 := by
    simpa [prefixWord, tailWord_5618109, baseEnd_5618109] using wordTrace_append hprefix tailTrace_5618109
  have hstable : (prefixWord ++ tailWord_5618109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618109).length < 2 ^ (prefixWord ++ tailWord_5618109).sum := by decide
  have hdescent : baseEnd_5618109 < baseStart_5618109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618179 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 3, 4, 2]
def baseStart_5618179 : Nat := 118140960795 + 5618179 * 2 ^ 59
def prefixEnd_5618179 : Nat := 4983230072969 + 3 ^ 40 * 5618179 * 2
def baseEnd_5618179 : Nat := 2884826229996279582524971

theorem tailTrace_5618179 : CollatzResearch.WordTrace tailWord_5618179 prefixEnd_5618179 2884826229996279582524971 := by
  unfold tailWord_5618179
  simp only [CollatzResearch.WordTrace]
  refine ⟨204911822313304466427929591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136607881542202977618619727 204911822313304466427929591)
  ·
    refine ⟨307367733469956699641894387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204911822313304466427929591 307367733469956699641894387)
    ·
      refine ⟨461051600204935049462841581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307367733469956699641894387 461051600204935049462841581)
      ·
        refine ⟨172894350076850643548565593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 461051600204935049462841581 172894350076850643548565593)
        ·
          refine ⟨129670762557637982661424195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172894350076850643548565593 129670762557637982661424195)
          ·
            refine ⟨194506143836456973992136293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129670762557637982661424195 194506143836456973992136293)
            ·
              refine ⟨36469901969335682623525555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194506143836456973992136293 36469901969335682623525555)
              ·
                refine ⟨54704852954003523935288333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36469901969335682623525555 54704852954003523935288333)
                ·
                  refine ⟨20514319857751321475733125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54704852954003523935288333 20514319857751321475733125)
                  ·
                    refine ⟨3846434973328372776699961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20514319857751321475733125 3846434973328372776699961)
                    ·
                      refine ⟨2884826229996279582524971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3846434973328372776699961 2884826229996279582524971)
                      ·
                        rfl

theorem cell23_5618179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 4, 2].length) (baseStart_5618179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618179 prefixEnd_5618179 := by exact prefixLift 5618179
  have htrace : WordTrace (prefixWord ++ tailWord_5618179) baseStart_5618179 baseEnd_5618179 := by
    simpa [prefixWord, tailWord_5618179, baseEnd_5618179] using wordTrace_append hprefix tailTrace_5618179
  have hstable : (prefixWord ++ tailWord_5618179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618179).length < 2 ^ (prefixWord ++ tailWord_5618179).sum := by decide
  have hdescent : baseEnd_5618179 < baseStart_5618179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618253 : List Nat := [1, 6, 1, 1, 2, 2, 1, 4, 5]
def baseStart_5618253 : Nat := 118140960795 + 5618253 * 2 ^ 59
def prefixEnd_5618253 : Nat := 4983230072969 + 3 ^ 40 * 5618253 * 2
def baseEnd_5618253 : Nat := 320540469729412476999959

theorem tailTrace_5618253 : CollatzResearch.WordTrace tailWord_5618253 prefixEnd_5618253 320540469729412476999959 := by
  unfold tailWord_5618253
  simp only [CollatzResearch.WordTrace]
  refine ⟨204914521315036377066123413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136609680876690918044082275 204914521315036377066123413)
  ·
    refine ⟨9605368186642330174974535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 204914521315036377066123413 9605368186642330174974535)
    ·
      refine ⟨14408052279963495262461803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9605368186642330174974535 14408052279963495262461803)
      ·
        refine ⟨21612078419945242893692705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14408052279963495262461803 21612078419945242893692705)
        ·
          refine ⟨16209058814958932170269529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21612078419945242893692705 16209058814958932170269529)
          ·
            refine ⟨12156794111219199127702147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16209058814958932170269529 12156794111219199127702147)
            ·
              refine ⟨18235191166828798691553221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12156794111219199127702147 18235191166828798691553221)
              ·
                refine ⟨3419098343780399754666229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18235191166828798691553221 3419098343780399754666229)
                ·
                  refine ⟨320540469729412476999959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3419098343780399754666229 320540469729412476999959)
                  ·
                    rfl

theorem cell23_5618253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_5618253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618253 prefixEnd_5618253 := by exact prefixLift 5618253
  have htrace : WordTrace (prefixWord ++ tailWord_5618253) baseStart_5618253 baseEnd_5618253 := by
    simpa [prefixWord, tailWord_5618253, baseEnd_5618253] using wordTrace_append hprefix tailTrace_5618253
  have hstable : (prefixWord ++ tailWord_5618253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618253).length < 2 ^ (prefixWord ++ tailWord_5618253).sum := by decide
  have hdescent : baseEnd_5618253 < baseStart_5618253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618270 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 7]
def baseStart_5618270 : Nat := 118140960795 + 5618270 * 2 ^ 59
def prefixEnd_5618270 : Nat := 4983230072969 + 3 ^ 40 * 5618270 * 2
def baseEnd_5618270 : Nat := 320541439637315414054117

theorem tailTrace_5618270 : CollatzResearch.WordTrace tailWord_5618270 prefixEnd_5618270 320541439637315414054117 := by
  unfold tailWord_5618270
  simp only [CollatzResearch.WordTrace]
  refine ⟨25614392669496848621186533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136610094237316525979661509 25614392669496848621186533)
  ·
    refine ⟨4802698625530659116472475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25614392669496848621186533 4802698625530659116472475)
    ·
      refine ⟨7204047938295988674708713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4802698625530659116472475 7204047938295988674708713)
      ·
        refine ⟨5403035953721991506031535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7204047938295988674708713 5403035953721991506031535)
        ·
          refine ⟨8104553930582987259047303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5403035953721991506031535 8104553930582987259047303)
          ·
            refine ⟨12156830895874480888570955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8104553930582987259047303 12156830895874480888570955)
            ·
              refine ⟨18235246343811721332856433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12156830895874480888570955 18235246343811721332856433)
              ·
                refine ⟨13676434757858790999642325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18235246343811721332856433 13676434757858790999642325)
                ·
                  refine ⟨320541439637315414054117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13676434757858790999642325 320541439637315414054117)
                  ·
                    rfl

theorem cell23_5618270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_5618270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618270 prefixEnd_5618270 := by exact prefixLift 5618270
  have htrace : WordTrace (prefixWord ++ tailWord_5618270) baseStart_5618270 baseEnd_5618270 := by
    simpa [prefixWord, tailWord_5618270, baseEnd_5618270] using wordTrace_append hprefix tailTrace_5618270
  have hstable : (prefixWord ++ tailWord_5618270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618270).length < 2 ^ (prefixWord ++ tailWord_5618270).sum := by decide
  have hdescent : baseEnd_5618270 < baseStart_5618270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618286 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_5618286 : Nat := 118140960795 + 5618286 * 2 ^ 59
def prefixEnd_5618286 : Nat := 4983230072969 + 3 ^ 40 * 5618286 * 2
def baseEnd_5618286 : Nat := 2884881172426310663886979

theorem tailTrace_5618286 : CollatzResearch.WordTrace tailWord_5618286 prefixEnd_5618286 2884881172426310663886979 := by
  unfold tailWord_5618286
  simp only [CollatzResearch.WordTrace]
  refine ⟨25614465615489602962759339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136610483282611215801383141 25614465615489602962759339)
  ·
    refine ⟨38421698423234404444139009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25614465615489602962759339 38421698423234404444139009)
    ·
      refine ⟨28816273817425803333104257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38421698423234404444139009 28816273817425803333104257)
      ·
        refine ⟨21612205363069352499828193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28816273817425803333104257 21612205363069352499828193)
        ·
          refine ⟨16209154022302014374871145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21612205363069352499828193 16209154022302014374871145)
          ·
            refine ⟨12156865516726510781153359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16209154022302014374871145 12156865516726510781153359)
            ·
              refine ⟨18235298275089766171730039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12156865516726510781153359 18235298275089766171730039)
              ·
                refine ⟨27352947412634649257595059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18235298275089766171730039 27352947412634649257595059)
                ·
                  refine ⟨41029421118951973886392589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27352947412634649257595059 41029421118951973886392589)
                  ·
                    refine ⟨15386032919606990207397221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41029421118951973886392589 15386032919606990207397221)
                    ·
                      refine ⟨2884881172426310663886979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15386032919606990207397221 2884881172426310663886979)
                      ·
                        rfl

theorem cell23_5618286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_5618286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618286 prefixEnd_5618286 := by exact prefixLift 5618286
  have htrace : WordTrace (prefixWord ++ tailWord_5618286) baseStart_5618286 baseEnd_5618286 := by
    simpa [prefixWord, tailWord_5618286, baseEnd_5618286] using wordTrace_append hprefix tailTrace_5618286
  have hstable : (prefixWord ++ tailWord_5618286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618286).length < 2 ^ (prefixWord ++ tailWord_5618286).sum := by decide
  have hdescent : baseEnd_5618286 < baseStart_5618286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618309 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 8]
def baseStart_5618309 : Nat := 118140960795 + 5618309 * 2 ^ 59
def prefixEnd_5618309 : Nat := 4983230072969 + 3 ^ 40 * 5618309 * 2
def baseEnd_5618309 : Nat := 320543664720151563766597

theorem tailTrace_5618309 : CollatzResearch.WordTrace tailWord_5618309 prefixEnd_5618309 320543664720151563766597 := by
  unfold tailWord_5618309
  simp only [CollatzResearch.WordTrace]
  refine ⟨204916563802833498630161981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136611042535222332420107987 204916563802833498630161981)
  ·
    refine ⟨76843711426062561986310743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204916563802833498630161981 76843711426062561986310743)
    ·
      refine ⟨115265567139093842979466115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76843711426062561986310743 115265567139093842979466115)
      ·
        refine ⟨172898350708640764469199173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115265567139093842979466115 172898350708640764469199173)
        ·
          refine ⟨32418440757870143337974845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172898350708640764469199173 32418440757870143337974845)
          ·
            refine ⟨12156915284201303751740567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32418440757870143337974845 12156915284201303751740567)
            ·
              refine ⟨18235372926301955627610851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12156915284201303751740567 18235372926301955627610851)
              ·
                refine ⟨27353059389452933441416277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18235372926301955627610851 27353059389452933441416277)
                ·
                  refine ⟨320543664720151563766597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27353059389452933441416277 320543664720151563766597)
                  ·
                    rfl

theorem cell23_5618309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 8].length) (baseStart_5618309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618309 prefixEnd_5618309 := by exact prefixLift 5618309
  have htrace : WordTrace (prefixWord ++ tailWord_5618309) baseStart_5618309 baseEnd_5618309 := by
    simpa [prefixWord, tailWord_5618309, baseEnd_5618309] using wordTrace_append hprefix tailTrace_5618309
  have hstable : (prefixWord ++ tailWord_5618309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618309).length < 2 ^ (prefixWord ++ tailWord_5618309).sum := by decide
  have hdescent : baseEnd_5618309 < baseStart_5618309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618379 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 3]
def baseStart_5618379 : Nat := 118140960795 + 5618379 * 2 ^ 59
def prefixEnd_5618379 : Nat := 4983230072969 + 3 ^ 40 * 5618379 * 2
def baseEnd_5618379 : Nat := 2884928926127178800024051

theorem tailTrace_5618379 : CollatzResearch.WordTrace tailWord_5618379 prefixEnd_5618379 2884928926127178800024051 := by
  unfold tailWord_5618379
  simp only [CollatzResearch.WordTrace]
  refine ⟨204919116912579900585210191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136612744608386600390140127 204919116912579900585210191)
  ·
    refine ⟨307378675368869850877815287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204919116912579900585210191 307378675368869850877815287)
    ·
      refine ⟨461068013053304776316722931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307378675368869850877815287 461068013053304776316722931)
      ·
        refine ⟨691602019579957164475084397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461068013053304776316722931 691602019579957164475084397)
        ·
          refine ⟨259350757342483936678156649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 691602019579957164475084397 259350757342483936678156649)
          ·
            refine ⟨194513068006862952508617487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259350757342483936678156649 194513068006862952508617487)
            ·
              refine ⟨291769602010294428762926231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194513068006862952508617487 291769602010294428762926231)
              ·
                refine ⟨437654403015441643144389347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291769602010294428762926231 437654403015441643144389347)
                ·
                  refine ⟨656481604523162464716584021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437654403015441643144389347 656481604523162464716584021)
                  ·
                    refine ⟨7693143803005810133397469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 656481604523162464716584021 7693143803005810133397469)
                    ·
                      refine ⟨2884928926127178800024051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7693143803005810133397469 2884928926127178800024051)
                      ·
                        rfl

theorem cell23_5618379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 3].length) (baseStart_5618379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618379 prefixEnd_5618379 := by exact prefixLift 5618379
  have htrace : WordTrace (prefixWord ++ tailWord_5618379) baseStart_5618379 baseEnd_5618379 := by
    simpa [prefixWord, tailWord_5618379, baseEnd_5618379] using wordTrace_append hprefix tailTrace_5618379
  have hstable : (prefixWord ++ tailWord_5618379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618379).length < 2 ^ (prefixWord ++ tailWord_5618379).sum := by decide
  have hdescent : baseEnd_5618379 < baseStart_5618379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618393 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 5, 2, 2]
def baseStart_5618393 : Nat := 118140960795 + 5618393 * 2 ^ 59
def prefixEnd_5618393 : Nat := 4983230072969 + 3 ^ 40 * 5618393 * 2
def baseEnd_5618393 : Nat := 2884936114856341745248987

theorem tailTrace_5618393 : CollatzResearch.WordTrace tailWord_5618393 prefixEnd_5618393 2884936114856341745248987 := by
  unfold tailWord_5618393
  simp only [CollatzResearch.WordTrace]
  refine ⟨204919627534529180976219833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136613085023019453984146555 204919627534529180976219833)
  ·
    refine ⟨153689720650896885732164875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204919627534529180976219833 153689720650896885732164875)
    ·
      refine ⟨230534580976345328598247313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153689720650896885732164875 230534580976345328598247313)
      ·
        refine ⟨172900935732258996448685485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230534580976345328598247313 172900935732258996448685485)
        ·
          refine ⟨64837850899597123668257057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172900935732258996448685485 64837850899597123668257057)
          ·
            refine ⟨48628388174697842751192793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64837850899597123668257057 48628388174697842751192793)
            ·
              refine ⟨36471291131023382063394595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48628388174697842751192793 36471291131023382063394595)
              ·
                refine ⟨54706936696535073095091893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36471291131023382063394595 54706936696535073095091893)
                ·
                  refine ⟨5128775315300163102664865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54706936696535073095091893 5128775315300163102664865)
                  ·
                    refine ⟨3846581486475122326998649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5128775315300163102664865 3846581486475122326998649)
                    ·
                      refine ⟨2884936114856341745248987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3846581486475122326998649 2884936114856341745248987)
                      ·
                        rfl

theorem cell23_5618393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 2, 2].length) (baseStart_5618393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618393 prefixEnd_5618393 := by exact prefixLift 5618393
  have htrace : WordTrace (prefixWord ++ tailWord_5618393) baseStart_5618393 baseEnd_5618393 := by
    simpa [prefixWord, tailWord_5618393, baseEnd_5618393] using wordTrace_append hprefix tailTrace_5618393
  have hstable : (prefixWord ++ tailWord_5618393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618393).length < 2 ^ (prefixWord ++ tailWord_5618393).sum := by decide
  have hdescent : baseEnd_5618393 < baseStart_5618393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618399 : List Nat := [1, 1, 2, 3, 2, 3, 2, 9]
def baseStart_5618399 : Nat := 118140960795 + 5618399 * 2 ^ 59
def prefixEnd_5618399 : Nat := 4983230072969 + 3 ^ 40 * 5618399 * 2
def baseEnd_5618399 : Nat := 106849599842232174880517

theorem tailTrace_5618399 : CollatzResearch.WordTrace tailWord_5618399 prefixEnd_5618399 106849599842232174880517 := by
  unfold tailWord_5618399
  simp only [CollatzResearch.WordTrace]
  refine ⟨204919846372507444000938251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136613230915004962667292167 204919846372507444000938251)
  ·
    refine ⟨307379769558761166001407377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204919846372507444000938251 307379769558761166001407377)
    ·
      refine ⟨230534827169070874501055533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307379769558761166001407377 230534827169070874501055533)
      ·
        refine ⟨86450560188401577937895825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230534827169070874501055533 86450560188401577937895825)
        ·
          refine ⟨64837920141301183453421869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86450560188401577937895825 64837920141301183453421869)
          ·
            refine ⟨24314220052987943795033201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64837920141301183453421869 24314220052987943795033201)
            ·
              refine ⟨18235665039740957846274901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24314220052987943795033201 18235665039740957846274901)
              ·
                refine ⟨106849599842232174880517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18235665039740957846274901 106849599842232174880517)
                ·
                  rfl

theorem cell23_5618399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 9].length) (baseStart_5618399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618399 prefixEnd_5618399 := by exact prefixLift 5618399
  have htrace : WordTrace (prefixWord ++ tailWord_5618399) baseStart_5618399 baseEnd_5618399 := by
    simpa [prefixWord, tailWord_5618399, baseEnd_5618399] using wordTrace_append hprefix tailTrace_5618399
  have hstable : (prefixWord ++ tailWord_5618399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618399).length < 2 ^ (prefixWord ++ tailWord_5618399).sum := by decide
  have hdescent : baseEnd_5618399 < baseStart_5618399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618421 : List Nat := [1, 3, 6, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_5618421 : Nat := 118140960795 + 5618421 * 2 ^ 59
def prefixEnd_5618421 : Nat := 4983230072969 + 3 ^ 40 * 5618421 * 2
def baseEnd_5618421 : Nat := 2884950492314667635698859

theorem tailTrace_5618421 : CollatzResearch.WordTrace tailWord_5618421 prefixEnd_5618421 2884950492314667635698859 := by
  unfold tailWord_5618421
  simp only [CollatzResearch.WordTrace]
  refine ⟨204920648778427741758239117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136613765852285161172159411 204920648778427741758239117)
  ·
    refine ⟨76845243291910403159339669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204920648778427741758239117 76845243291910403159339669)
    ·
      refine ⟨3602120779308300148094047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76845243291910403159339669 3602120779308300148094047)
      ·
        refine ⟨5403181168962450222141071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3602120779308300148094047 5403181168962450222141071)
        ·
          refine ⟨8104771753443675333211607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5403181168962450222141071 8104771753443675333211607)
          ·
            refine ⟨12157157630165512999817411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8104771753443675333211607 12157157630165512999817411)
            ·
              refine ⟨18235736445248269499726117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12157157630165512999817411 18235736445248269499726117)
              ·
                refine ⟨3419200583484050531198647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18235736445248269499726117 3419200583484050531198647)
                ·
                  refine ⟨5128800875226075796797971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3419200583484050531198647 5128800875226075796797971)
                  ·
                    refine ⟨7693201312839113695196957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5128800875226075796797971 7693201312839113695196957)
                    ·
                      refine ⟨2884950492314667635698859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7693201312839113695196957 2884950492314667635698859)
                      ·
                        rfl

theorem cell23_5618421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_5618421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618421 prefixEnd_5618421 := by exact prefixLift 5618421
  have htrace : WordTrace (prefixWord ++ tailWord_5618421) baseStart_5618421 baseEnd_5618421 := by
    simpa [prefixWord, tailWord_5618421, baseEnd_5618421] using wordTrace_append hprefix tailTrace_5618421
  have hstable : (prefixWord ++ tailWord_5618421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618421).length < 2 ^ (prefixWord ++ tailWord_5618421).sum := by decide
  have hdescent : baseEnd_5618421 < baseStart_5618421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618429 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 1, 9]
def baseStart_5618429 : Nat := 118140960795 + 5618429 * 2 ^ 59
def prefixEnd_5618429 : Nat := 4983230072969 + 3 ^ 40 * 5618429 * 2
def baseEnd_5618429 : Nat := 961651533386634534799607

theorem tailTrace_5618429 : CollatzResearch.WordTrace tailWord_5618429 prefixEnd_5618429 961651533386634534799607 := by
  unfold tailWord_5618429
  simp only [CollatzResearch.WordTrace]
  refine ⟨204920940562398759124530341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136613960374932506083020227 204920940562398759124530341)
  ·
    refine ⟨38422676355449767335849439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204920940562398759124530341 38422676355449767335849439)
    ·
      refine ⟨57634014533174651003774159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38422676355449767335849439 57634014533174651003774159)
      ·
        refine ⟨86451021799761976505661239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57634014533174651003774159 86451021799761976505661239)
        ·
          refine ⟨129676532699642964758491859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86451021799761976505661239 129676532699642964758491859)
          ·
            refine ⟨194514799049464447137737789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129676532699642964758491859 194514799049464447137737789)
            ·
              refine ⟨72943049643549167676651671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194514799049464447137737789 72943049643549167676651671)
              ·
                refine ⟨109414574465323751514977507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72943049643549167676651671 109414574465323751514977507)
                ·
                  refine ⟨164121861697985627272466261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109414574465323751514977507 164121861697985627272466261)
                  ·
                    refine ⟨961651533386634534799607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 164121861697985627272466261 961651533386634534799607)
                    ·
                      rfl

theorem cell23_5618429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_5618429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618429 prefixEnd_5618429 := by exact prefixLift 5618429
  have htrace : WordTrace (prefixWord ++ tailWord_5618429) baseStart_5618429 baseEnd_5618429 := by
    simpa [prefixWord, tailWord_5618429, baseEnd_5618429] using wordTrace_append hprefix tailTrace_5618429
  have hstable : (prefixWord ++ tailWord_5618429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618429).length < 2 ^ (prefixWord ++ tailWord_5618429).sum := by decide
  have hdescent : baseEnd_5618429 < baseStart_5618429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618450 : List Nat := [3, 2, 4, 1, 2, 1, 3, 7]
def baseStart_5618450 : Nat := 118140960795 + 5618450 * 2 ^ 59
def prefixEnd_5618450 : Nat := 4983230072969 + 3 ^ 40 * 5618450 * 2
def baseEnd_5618450 : Nat := 106850569750135111934675

theorem tailTrace_5618450 : CollatzResearch.WordTrace tailWord_5618450 prefixEnd_5618450 106850569750135111934675 := by
  unfold tailWord_5618450
  simp only [CollatzResearch.WordTrace]
  refine ⟨51230426623830669927761201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136614470996881786474029869 51230426623830669927761201)
  ·
    refine ⟨38422819967873002445820901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51230426623830669927761201 38422819967873002445820901)
    ·
      refine ⟨7204278743976187958591419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38422819967873002445820901 7204278743976187958591419)
      ·
        refine ⟨10806418115964281937887129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7204278743976187958591419 10806418115964281937887129)
        ·
          refine ⟨8104813586973211453415347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10806418115964281937887129 8104813586973211453415347)
          ·
            refine ⟨12157220380459817180123021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8104813586973211453415347 12157220380459817180123021)
            ·
              refine ⟨4558957642672431442546133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12157220380459817180123021 4558957642672431442546133)
              ·
                refine ⟨106850569750135111934675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4558957642672431442546133 106850569750135111934675)
                ·
                  rfl

theorem cell23_5618450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 7].length) (baseStart_5618450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618450 prefixEnd_5618450 := by exact prefixLift 5618450
  have htrace : WordTrace (prefixWord ++ tailWord_5618450) baseStart_5618450 baseEnd_5618450 := by
    simpa [prefixWord, tailWord_5618450, baseEnd_5618450] using wordTrace_append hprefix tailTrace_5618450
  have hstable : (prefixWord ++ tailWord_5618450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618450).length < 2 ^ (prefixWord ++ tailWord_5618450).sum := by decide
  have hdescent : baseEnd_5618450 < baseStart_5618450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618453 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 3, 3, 2]
def baseStart_5618453 : Nat := 118140960795 + 5618453 * 2 ^ 59
def prefixEnd_5618453 : Nat := 4983230072969 + 3 ^ 40 * 5618453 * 2
def baseEnd_5618453 : Nat := 2884966923695611510498711

theorem tailTrace_5618453 : CollatzResearch.WordTrace tailWord_5618453 prefixEnd_5618453 2884966923695611510498711 := by
  unfold tailWord_5618453
  simp only [CollatzResearch.WordTrace]
  refine ⟨204921815914311811223404013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136614543942874540815602675 204921815914311811223404013)
  ·
    refine ⟨76845680967866929208776505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204921815914311811223404013 76845680967866929208776505)
    ·
      refine ⟨57634260725900196906582379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76845680967866929208776505 57634260725900196906582379)
      ·
        refine ⟨86451391088850295359873569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57634260725900196906582379 86451391088850295359873569)
        ·
          refine ⟨64838543316637721519905177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86451391088850295359873569 64838543316637721519905177)
          ·
            refine ⟨48628907487478291139928883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64838543316637721519905177 48628907487478291139928883)
            ·
              refine ⟨72943361231217436709893325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48628907487478291139928883 72943361231217436709893325)
              ·
                refine ⟨27353760461706538766209997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72943361231217436709893325 27353760461706538766209997)
                ·
                  refine ⟨10257660173139952037328749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27353760461706538766209997 10257660173139952037328749)
                  ·
                    refine ⟨3846622564927482013998281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10257660173139952037328749 3846622564927482013998281)
                    ·
                      refine ⟨2884966923695611510498711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3846622564927482013998281 2884966923695611510498711)
                      ·
                        rfl

theorem cell23_5618453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_5618453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618453 prefixEnd_5618453 := by exact prefixLift 5618453
  have htrace : WordTrace (prefixWord ++ tailWord_5618453) baseStart_5618453 baseEnd_5618453 := by
    simpa [prefixWord, tailWord_5618453, baseEnd_5618453] using wordTrace_append hprefix tailTrace_5618453
  have hstable : (prefixWord ++ tailWord_5618453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618453).length < 2 ^ (prefixWord ++ tailWord_5618453).sum := by decide
  have hdescent : baseEnd_5618453 < baseStart_5618453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618459 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 6, 6]
def baseStart_5618459 : Nat := 118140960795 + 5618459 * 2 ^ 59
def prefixEnd_5618459 : Nat := 4983230072969 + 3 ^ 40 * 5618459 * 2
def baseEnd_5618459 : Nat := 961656668193179495674561

theorem tailTrace_5618459 : CollatzResearch.WordTrace tailWord_5618459 prefixEnd_5618459 961656668193179495674561 := by
  unfold tailWord_5618459
  simp only [CollatzResearch.WordTrace]
  refine ⟨204922034752290074248122431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136614689834860049498748287 204922034752290074248122431)
  ·
    refine ⟨307383052128435111372183647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204922034752290074248122431 307383052128435111372183647)
    ·
      refine ⟨461074578192652667058275471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307383052128435111372183647 461074578192652667058275471)
      ·
        refine ⟨691611867288979000587413207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461074578192652667058275471 691611867288979000587413207)
        ·
          refine ⟨1037417800933468500881119811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691611867288979000587413207 1037417800933468500881119811)
          ·
            refine ⟨1556126701400202751321679717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037417800933468500881119811 1556126701400202751321679717)
            ·
              refine ⟨291773756512538015872814947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1556126701400202751321679717 291773756512538015872814947)
              ·
                refine ⟨437660634768807023809222421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291773756512538015872814947 437660634768807023809222421)
                ·
                  refine ⟨20515342254787829241057301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 437660634768807023809222421 20515342254787829241057301)
                  ·
                    refine ⟨961656668193179495674561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20515342254787829241057301 961656668193179495674561)
                    ·
                      rfl

theorem cell23_5618459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 6].length) (baseStart_5618459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618459 prefixEnd_5618459 := by exact prefixLift 5618459
  have htrace : WordTrace (prefixWord ++ tailWord_5618459) baseStart_5618459 baseEnd_5618459 := by
    simpa [prefixWord, tailWord_5618459, baseEnd_5618459] using wordTrace_append hprefix tailTrace_5618459
  have hstable : (prefixWord ++ tailWord_5618459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618459).length < 2 ^ (prefixWord ++ tailWord_5618459).sum := by decide
  have hdescent : baseEnd_5618459 < baseStart_5618459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618461 : List Nat := [1, 4, 2, 4, 1, 1, 2, 3, 1, 2, 2]
def baseStart_5618461 : Nat := 118140960795 + 5618461 * 2 ^ 59
def prefixEnd_5618461 : Nat := 4983230072969 + 3 ^ 40 * 5618461 * 2
def baseEnd_5618461 : Nat := 2884971031540847479198675

theorem tailTrace_5618461 : CollatzResearch.WordTrace tailWord_5618461 prefixEnd_5618461 2884971031540847479198675 := by
  unfold tailWord_5618461
  simp only [CollatzResearch.WordTrace]
  refine ⟨204922107698282828589695237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136614738465521885726463491 204922107698282828589695237)
  ·
    refine ⟨38422895193428030360567857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204922107698282828589695237 38422895193428030360567857)
    ·
      refine ⟨28817171395071022770425893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38422895193428030360567857 28817171395071022770425893)
      ·
        refine ⟨5403219636575816769454855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28817171395071022770425893 5403219636575816769454855)
        ·
          refine ⟨8104829454863725154182283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5403219636575816769454855 8104829454863725154182283)
          ·
            refine ⟨12157244182295587731273425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8104829454863725154182283 12157244182295587731273425)
            ·
              refine ⟨9117933136721690798455069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12157244182295587731273425 9117933136721690798455069)
              ·
                refine ⟨3419224926270634049420651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9117933136721690798455069 3419224926270634049420651)
                ·
                  refine ⟨5128837389405951074130977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3419224926270634049420651 5128837389405951074130977)
                  ·
                    refine ⟨3846628042054463305598233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5128837389405951074130977 3846628042054463305598233)
                    ·
                      refine ⟨2884971031540847479198675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3846628042054463305598233 2884971031540847479198675)
                      ·
                        rfl

theorem cell23_5618461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_5618461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618461 prefixEnd_5618461 := by exact prefixLift 5618461
  have htrace : WordTrace (prefixWord ++ tailWord_5618461) baseStart_5618461 baseEnd_5618461 := by
    simpa [prefixWord, tailWord_5618461, baseEnd_5618461] using wordTrace_append hprefix tailTrace_5618461
  have hstable : (prefixWord ++ tailWord_5618461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618461).length < 2 ^ (prefixWord ++ tailWord_5618461).sum := by decide
  have hdescent : baseEnd_5618461 < baseStart_5618461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618479 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 6]
def baseStart_5618479 : Nat := 118140960795 + 5618479 * 2 ^ 59
def prefixEnd_5618479 : Nat := 4983230072969 + 3 ^ 40 * 5618479 * 2
def baseEnd_5618479 : Nat := 2884980274192628408773591

theorem tailTrace_5618479 : CollatzResearch.WordTrace tailWord_5618479 prefixEnd_5618479 2884980274192628408773591 := by
  unfold tailWord_5618479
  simp only [CollatzResearch.WordTrace]
  refine ⟨204922764212217617663850491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136615176141478411775900327 204922764212217617663850491)
  ·
    refine ⟨307384146318326426495775737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204922764212217617663850491 307384146318326426495775737)
    ·
      refine ⟨230538109738744819871831803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307384146318326426495775737 230538109738744819871831803)
      ·
        refine ⟨345807164608117229807747705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230538109738744819871831803 345807164608117229807747705)
        ·
          refine ⟨259355373456087922355810779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345807164608117229807747705 259355373456087922355810779)
          ·
            refine ⟨389033060184131883533716169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259355373456087922355810779 389033060184131883533716169)
            ·
              refine ⟨291774795138098912650287127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389033060184131883533716169 291774795138098912650287127)
              ·
                refine ⟨437662192707148368975430691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291774795138098912650287127 437662192707148368975430691)
                ·
                  refine ⟨656493289060722553463146037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437662192707148368975430691 656493289060722553463146037)
                  ·
                    refine ⟨61546245849442739387169941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 656493289060722553463146037 61546245849442739387169941)
                    ·
                      refine ⟨2884980274192628408773591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61546245849442739387169941 2884980274192628408773591)
                      ·
                        rfl

theorem cell23_5618479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_5618479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618479 prefixEnd_5618479 := by exact prefixLift 5618479
  have htrace : WordTrace (prefixWord ++ tailWord_5618479) baseStart_5618479 baseEnd_5618479 := by
    simpa [prefixWord, tailWord_5618479, baseEnd_5618479] using wordTrace_append hprefix tailTrace_5618479
  have hstable : (prefixWord ++ tailWord_5618479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618479).length < 2 ^ (prefixWord ++ tailWord_5618479).sum := by decide
  have hdescent : baseEnd_5618479 < baseStart_5618479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618494 : List Nat := [4, 2, 1, 2, 3, 1, 3, 1, 2, 1, 3]
def baseStart_5618494 : Nat := 118140960795 + 5618494 * 2 ^ 59
def prefixEnd_5618494 : Nat := 4983230072969 + 3 ^ 40 * 5618494 * 2
def baseEnd_5618494 : Nat := 2884987976402445850086023

theorem tailTrace_5618494 : CollatzResearch.WordTrace tailWord_5618494 prefixEnd_5618494 2884987976402445850086023 := by
  unfold tailWord_5618494
  simp only [CollatzResearch.WordTrace]
  refine ⟨25615413913395409403205817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136615540871442183483764357 25615413913395409403205817)
  ·
    refine ⟨19211560435046557052404363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25615413913395409403205817 19211560435046557052404363)
    ·
      refine ⟨28817340652569835578606545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19211560435046557052404363 28817340652569835578606545)
      ·
        refine ⟨21613005489427376683954909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28817340652569835578606545 21613005489427376683954909)
        ·
          refine ⟨8104877058535266256483091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21613005489427376683954909 8104877058535266256483091)
          ·
            refine ⟨12157315587802899384724637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8104877058535266256483091 12157315587802899384724637)
            ·
              refine ⟨4558993345426087269271739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12157315587802899384724637 4558993345426087269271739)
              ·
                refine ⟨6838490018139130903907609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4558993345426087269271739 6838490018139130903907609)
                ·
                  refine ⟨5128867513604348177930707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6838490018139130903907609 5128867513604348177930707)
                  ·
                    refine ⟨7693301270406522266896061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5128867513604348177930707 7693301270406522266896061)
                    ·
                      refine ⟨2884987976402445850086023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7693301270406522266896061 2884987976402445850086023)
                      ·
                        rfl

theorem cell23_5618494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_5618494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618494 prefixEnd_5618494 := by exact prefixLift 5618494
  have htrace : WordTrace (prefixWord ++ tailWord_5618494) baseStart_5618494 baseEnd_5618494 := by
    simpa [prefixWord, tailWord_5618494, baseEnd_5618494] using wordTrace_append hprefix tailTrace_5618494
  have hstable : (prefixWord ++ tailWord_5618494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618494).length < 2 ^ (prefixWord ++ tailWord_5618494).sum := by decide
  have hdescent : baseEnd_5618494 < baseStart_5618494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618540 : List Nat := [2, 2, 1, 1, 4, 1, 5, 2, 5]
def baseStart_5618540 : Nat := 118140960795 + 5618540 * 2 ^ 59
def prefixEnd_5618540 : Nat := 4983230072969 + 3 ^ 40 * 5618540 * 2
def baseEnd_5618540 : Nat := 320556844056950296678979

theorem tailTrace_5618540 : CollatzResearch.WordTrace tailWord_5618540 prefixEnd_5618540 320556844056950296678979 := by
  unfold tailWord_5618540
  simp only [CollatzResearch.WordTrace]
  refine ⟨102462494532498312540910537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136616659376664416721214049 102462494532498312540910537)
  ·
    refine ⟨76846870899373734405682903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102462494532498312540910537 76846870899373734405682903)
    ·
      refine ⟨115270306349060601608524355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76846870899373734405682903 115270306349060601608524355)
      ·
        refine ⟨172905459523590902412786533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115270306349060601608524355 172905459523590902412786533)
        ·
          refine ⟨32419773660673294202397475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172905459523590902412786533 32419773660673294202397475)
          ·
            refine ⟨48629660491009941303596213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32419773660673294202397475 48629660491009941303596213)
            ·
              refine ⟨4559030671032181997212145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48629660491009941303596213 4559030671032181997212145)
              ·
                refine ⟨3419273003274136497909109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4559030671032181997212145 3419273003274136497909109)
                ·
                  refine ⟨320556844056950296678979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3419273003274136497909109 320556844056950296678979)
                  ·
                    rfl

theorem cell23_5618540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 5].length) (baseStart_5618540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618540 prefixEnd_5618540 := by exact prefixLift 5618540
  have htrace : WordTrace (prefixWord ++ tailWord_5618540) baseStart_5618540 baseEnd_5618540 := by
    simpa [prefixWord, tailWord_5618540, baseEnd_5618540] using wordTrace_append hprefix tailTrace_5618540
  have hstable : (prefixWord ++ tailWord_5618540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618540).length < 2 ^ (prefixWord ++ tailWord_5618540).sum := by decide
  have hdescent : baseEnd_5618540 < baseStart_5618540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618546 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_5618546 : Nat := 118140960795 + 5618546 * 2 ^ 59
def prefixEnd_5618546 : Nat := 4983230072969 + 3 ^ 40 * 5618546 * 2
def baseEnd_5618546 : Nat := 2885014677396479646635783

theorem tailTrace_5618546 : CollatzResearch.WordTrace tailWord_5618546 prefixEnd_5618546 2885014677396479646635783 := by
  unfold tailWord_5618546
  simp only [CollatzResearch.WordTrace]
  refine ⟨51231301975743722026634873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136616805268649925404359661 51231301975743722026634873)
  ·
    refine ⟨38423476481807791519976155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51231301975743722026634873 38423476481807791519976155)
    ·
      refine ⟨57635214722711687279964233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38423476481807791519976155 57635214722711687279964233)
      ·
        refine ⟨43226411042033765459973175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57635214722711687279964233 43226411042033765459973175)
        ·
          refine ⟨64839616563050648189959763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43226411042033765459973175 64839616563050648189959763)
          ·
            refine ⟨97259424844575972284939645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64839616563050648189959763 97259424844575972284939645)
            ·
              refine ⟨36472284316715989606852367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97259424844575972284939645 36472284316715989606852367)
              ·
                refine ⟨54708426475073984410278551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36472284316715989606852367 54708426475073984410278551)
                ·
                  refine ⟨82062639712610976615417827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54708426475073984410278551 82062639712610976615417827)
                  ·
                    refine ⟨123093959568916464923126741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82062639712610976615417827 123093959568916464923126741)
                    ·
                      refine ⟨2885014677396479646635783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123093959568916464923126741 2885014677396479646635783)
                      ·
                        rfl

theorem cell23_5618546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_5618546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618546 prefixEnd_5618546 := by exact prefixLift 5618546
  have htrace : WordTrace (prefixWord ++ tailWord_5618546) baseStart_5618546 baseEnd_5618546 := by
    simpa [prefixWord, tailWord_5618546, baseEnd_5618546] using wordTrace_append hprefix tailTrace_5618546
  have hstable : (prefixWord ++ tailWord_5618546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618546).length < 2 ^ (prefixWord ++ tailWord_5618546).sum := by decide
  have hdescent : baseEnd_5618546 < baseStart_5618546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618556 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_5618556 : Nat := 118140960795 + 5618556 * 2 ^ 59
def prefixEnd_5618556 : Nat := 4983230072969 + 3 ^ 40 * 5618556 * 2
def baseEnd_5618556 : Nat := 2885019812203024607510737

theorem tailTrace_5618556 : CollatzResearch.WordTrace tailWord_5618556 prefixEnd_5618556 2885019812203024607510737 := by
  unfold tailWord_5618556
  simp only [CollatzResearch.WordTrace]
  refine ⟨102462786316469329907201761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136617048421959106542935681 102462786316469329907201761)
  ·
    refine ⟨76847089737351997430401321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102462786316469329907201761 76847089737351997430401321)
    ·
      refine ⟨57635317303013998072800991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76847089737351997430401321 57635317303013998072800991)
      ·
        refine ⟨86452975954520997109201487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57635317303013998072800991 86452975954520997109201487)
        ·
          refine ⟨129679463931781495663802231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86452975954520997109201487 129679463931781495663802231)
          ·
            refine ⟨194519195897672243495703347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129679463931781495663802231 194519195897672243495703347)
            ·
              refine ⟨291778793846508365243555021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194519195897672243495703347 291778793846508365243555021)
              ·
                refine ⟨109417047692440636966333133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291778793846508365243555021 109417047692440636966333133)
                ·
                  refine ⟨41031392884665238862374925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109417047692440636966333133 41031392884665238862374925)
                  ·
                    refine ⟨15386772331749464573390597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41031392884665238862374925 15386772331749464573390597)
                    ·
                      refine ⟨2885019812203024607510737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15386772331749464573390597 2885019812203024607510737)
                      ·
                        rfl

theorem cell23_5618556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_5618556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618556 prefixEnd_5618556 := by exact prefixLift 5618556
  have htrace : WordTrace (prefixWord ++ tailWord_5618556) baseStart_5618556 baseEnd_5618556 := by
    simpa [prefixWord, tailWord_5618556, baseEnd_5618556] using wordTrace_append hprefix tailTrace_5618556
  have hstable : (prefixWord ++ tailWord_5618556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618556).length < 2 ^ (prefixWord ++ tailWord_5618556).sum := by decide
  have hdescent : baseEnd_5618556 < baseStart_5618556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618570 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 2, 5]
def baseStart_5618570 : Nat := 118140960795 + 5618570 * 2 ^ 59
def prefixEnd_5618570 : Nat := 4983230072969 + 3 ^ 40 * 5618570 * 2
def baseEnd_5618570 : Nat := 961675666977395850911891

theorem tailTrace_5618570 : CollatzResearch.WordTrace tailWord_5618570 prefixEnd_5618570 961675666977395850911891 := by
  unfold tailWord_5618570
  simp only [CollatzResearch.WordTrace]
  refine ⟨51231520813721985051353291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136617388836591960136942109 51231520813721985051353291)
  ·
    refine ⟨76847281220582977577029937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51231520813721985051353291 76847281220582977577029937)
    ·
      refine ⟨57635460915437233182772453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76847281220582977577029937 57635460915437233182772453)
      ·
        refine ⟨10806648921644481221769835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57635460915437233182772453 10806648921644481221769835)
        ·
          refine ⟨16209973382466721832654753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10806648921644481221769835 16209973382466721832654753)
          ·
            refine ⟨12157480036850041374491065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16209973382466721832654753 12157480036850041374491065)
            ·
              refine ⟨9118110027637531030868299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12157480036850041374491065 9118110027637531030868299)
              ·
                refine ⟨13677165041456296546302449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9118110027637531030868299 13677165041456296546302449)
                ·
                  refine ⟨10257873781092222409726837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13677165041456296546302449 10257873781092222409726837)
                  ·
                    refine ⟨961675666977395850911891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10257873781092222409726837 961675666977395850911891)
                    ·
                      rfl

theorem cell23_5618570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_5618570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618570 prefixEnd_5618570 := by exact prefixLift 5618570
  have htrace : WordTrace (prefixWord ++ tailWord_5618570) baseStart_5618570 baseEnd_5618570 := by
    simpa [prefixWord, tailWord_5618570, baseEnd_5618570] using wordTrace_append hprefix tailTrace_5618570
  have hstable : (prefixWord ++ tailWord_5618570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618570).length < 2 ^ (prefixWord ++ tailWord_5618570).sum := by decide
  have hdescent : baseEnd_5618570 < baseStart_5618570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618613 : List Nat := [1, 3, 3, 2, 1, 1, 1, 5, 6]
def baseStart_5618613 : Nat := 118140960795 + 5618613 * 2 ^ 59
def prefixEnd_5618613 : Nat := 4983230072969 + 3 ^ 40 * 5618613 * 2
def baseEnd_5618613 : Nat := 320561008955592320499775

theorem tailTrace_5618613 : CollatzResearch.WordTrace tailWord_5618613 prefixEnd_5618613 320561008955592320499775 := by
  unfold tailWord_5618613
  simp only [CollatzResearch.WordTrace]
  refine ⟨204927651593732158549228493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136618434395821439032818995 204927651593732158549228493)
  ·
    refine ⟨76847869347649559455960685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204927651593732158549228493 76847869347649559455960685)
    ·
      refine ⟨28817951005368584795985257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76847869347649559455960685 28817951005368584795985257)
      ·
        refine ⟨21613463254026438596988943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28817951005368584795985257 21613463254026438596988943)
        ·
          refine ⟨32420194881039657895483415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21613463254026438596988943 32420194881039657895483415)
          ·
            refine ⟨48630292321559486843225123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32420194881039657895483415 48630292321559486843225123)
            ·
              refine ⟨72945438482339230264837685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48630292321559486843225123 72945438482339230264837685)
              ·
                refine ⟨6838634857719302837328533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72945438482339230264837685 6838634857719302837328533)
                ·
                  refine ⟨320561008955592320499775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6838634857719302837328533 320561008955592320499775)
                  ·
                    rfl

theorem cell23_5618613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 6].length) (baseStart_5618613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618613 prefixEnd_5618613 := by exact prefixLift 5618613
  have htrace : WordTrace (prefixWord ++ tailWord_5618613) baseStart_5618613 baseEnd_5618613 := by
    simpa [prefixWord, tailWord_5618613, baseEnd_5618613] using wordTrace_append hprefix tailTrace_5618613
  have hstable : (prefixWord ++ tailWord_5618613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618613).length < 2 ^ (prefixWord ++ tailWord_5618613).sum := by decide
  have hdescent : baseEnd_5618613 < baseStart_5618613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618656 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 2, 10]
def baseStart_5618656 : Nat := 118140960795 + 5618656 * 2 ^ 59
def prefixEnd_5618656 : Nat := 4983230072969 + 3 ^ 40 * 5618656 * 2
def baseEnd_5618656 : Nat := 961690386756158072086759

theorem tailTrace_5618656 : CollatzResearch.WordTrace tailWord_5618656 prefixEnd_5618656 961690386756158072086759 := by
  unfold tailWord_5618656
  simp only [CollatzResearch.WordTrace]
  refine ⟨102464609966288188446521911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136619479955050917928695881 102464609966288188446521911)
  ·
    refine ⟨153696914949432282669782867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102464609966288188446521911 153696914949432282669782867)
    ·
      refine ⟨230545372424148424004674301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153696914949432282669782867 230545372424148424004674301)
      ·
        refine ⟨86454514659055659001752863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230545372424148424004674301 86454514659055659001752863)
        ·
          refine ⟨129681771988583488502629295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86454514659055659001752863 129681771988583488502629295)
          ·
            refine ⟨194522657982875232753943943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129681771988583488502629295 194522657982875232753943943)
            ·
              refine ⟨291783986974312849130915915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194522657982875232753943943 291783986974312849130915915)
              ·
                refine ⟨437675980461469273696373873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291783986974312849130915915 437675980461469273696373873)
                ·
                  refine ⟨328256985346101955272280405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437675980461469273696373873 328256985346101955272280405)
                  ·
                    refine ⟨961690386756158072086759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 328256985346101955272280405 961690386756158072086759)
                    ·
                      rfl

theorem cell23_5618656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 10].length) (baseStart_5618656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618656 prefixEnd_5618656 := by exact prefixLift 5618656
  have htrace : WordTrace (prefixWord ++ tailWord_5618656) baseStart_5618656 baseEnd_5618656 := by
    simpa [prefixWord, tailWord_5618656, baseEnd_5618656] using wordTrace_append hprefix tailTrace_5618656
  have hstable : (prefixWord ++ tailWord_5618656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618656).length < 2 ^ (prefixWord ++ tailWord_5618656).sum := by decide
  have hdescent : baseEnd_5618656 < baseStart_5618656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618693 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 3, 2, 4]
def baseStart_5618693 : Nat := 118140960795 + 5618693 * 2 ^ 59
def prefixEnd_5618693 : Nat := 4983230072969 + 3 ^ 40 * 5618693 * 2
def baseEnd_5618693 : Nat := 2885090159052690571497607

theorem tailTrace_5618693 : CollatzResearch.WordTrace tailWord_5618693 prefixEnd_5618693 2885090159052690571497607 := by
  unfold tailWord_5618693
  simp only [CollatzResearch.WordTrace]
  refine ⟨204930569433442332212140733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136620379622294888141427155 204930569433442332212140733)
  ·
    refine ⟨76848963537540874579552775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204930569433442332212140733 76848963537540874579552775)
    ·
      refine ⟨115273445306311311869329163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76848963537540874579552775 115273445306311311869329163)
      ·
        refine ⟨172910167959466967803993745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115273445306311311869329163 172910167959466967803993745)
        ·
          refine ⟨129682625969600225852995309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172910167959466967803993745 129682625969600225852995309)
          ·
            refine ⟨48630984738600084694873241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129682625969600225852995309 48630984738600084694873241)
            ·
              refine ⟨36473238553950063521154931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48630984738600084694873241 36473238553950063521154931)
              ·
                refine ⟨54709857830925095281732397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36473238553950063521154931 54709857830925095281732397)
                ·
                  refine ⟨20516196686596910730649649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54709857830925095281732397 20516196686596910730649649)
                  ·
                    refine ⟨15387147514947683047987237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20516196686596910730649649 15387147514947683047987237)
                    ·
                      refine ⟨2885090159052690571497607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15387147514947683047987237 2885090159052690571497607)
                      ·
                        rfl

theorem cell23_5618693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_5618693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618693 prefixEnd_5618693 := by exact prefixLift 5618693
  have htrace : WordTrace (prefixWord ++ tailWord_5618693) baseStart_5618693 baseEnd_5618693 := by
    simpa [prefixWord, tailWord_5618693, baseEnd_5618693] using wordTrace_append hprefix tailTrace_5618693
  have hstable : (prefixWord ++ tailWord_5618693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618693).length < 2 ^ (prefixWord ++ tailWord_5618693).sum := by decide
  have hdescent : baseEnd_5618693 < baseStart_5618693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618700 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 1, 1, 5]
def baseStart_5618700 : Nat := 118140960795 + 5618700 * 2 ^ 59
def prefixEnd_5618700 : Nat := 4983230072969 + 3 ^ 40 * 5618700 * 2
def baseEnd_5618700 : Nat := 2885093753417272044110075

theorem tailTrace_5618700 : CollatzResearch.WordTrace tailWord_5618700 prefixEnd_5618700 2885093753417272044110075 := by
  unfold tailWord_5618700
  simp only [CollatzResearch.WordTrace]
  refine ⟨102465412372208486203822777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136620549829611314938430369 102465412372208486203822777)
  ·
    refine ⟨76849059279156364652867083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102465412372208486203822777 76849059279156364652867083)
    ·
      refine ⟨115273588918734546979300625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76849059279156364652867083 115273588918734546979300625)
      ·
        refine ⟨86455191689050910234475469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115273588918734546979300625 86455191689050910234475469)
        ·
          refine ⟨32420696883394091337928301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86455191689050910234475469 32420696883394091337928301)
          ·
            refine ⟨12157761331272784251723113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32420696883394091337928301 12157761331272784251723113)
            ·
              refine ⟨9118320998454588188792335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12157761331272784251723113 9118320998454588188792335)
              ·
                refine ⟨13677481497681882283188503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9118320998454588188792335 13677481497681882283188503)
                ·
                  refine ⟨20516222246522823424782755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13677481497681882283188503 20516222246522823424782755)
                  ·
                    refine ⟨30774333369784235137174133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20516222246522823424782755 30774333369784235137174133)
                    ·
                      refine ⟨2885093753417272044110075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30774333369784235137174133 2885093753417272044110075)
                      ·
                        rfl

theorem cell23_5618700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_5618700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618700 prefixEnd_5618700 := by exact prefixLift 5618700
  have htrace : WordTrace (prefixWord ++ tailWord_5618700) baseStart_5618700 baseEnd_5618700 := by
    simpa [prefixWord, tailWord_5618700, baseEnd_5618700] using wordTrace_append hprefix tailTrace_5618700
  have hstable : (prefixWord ++ tailWord_5618700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618700).length < 2 ^ (prefixWord ++ tailWord_5618700).sum := by decide
  have hdescent : baseEnd_5618700 < baseStart_5618700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618724 : List Nat := [2, 3, 1, 4, 1, 1, 4, 1, 2, 4]
def baseStart_5618724 : Nat := 118140960795 + 5618724 * 2 ^ 59
def prefixEnd_5618724 : Nat := 4983230072969 + 3 ^ 40 * 5618724 * 2
def baseEnd_5618724 : Nat := 961702025650993316736655

theorem tailTrace_5618724 : CollatzResearch.WordTrace tailWord_5618724 prefixEnd_5618724 961702025650993316736655 := by
  unfold tailWord_5618724
  simp only [CollatzResearch.WordTrace]
  refine ⟨102465850048165012253259613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136621133397553349671012817 102465850048165012253259613)
  ·
    refine ⟨38424693768061879594972355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102465850048165012253259613 38424693768061879594972355)
    ·
      refine ⟨57637040652092819392458533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38424693768061879594972355 57637040652092819392458533)
      ·
        refine ⟨10806945122267403636085975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57637040652092819392458533 10806945122267403636085975)
        ·
          refine ⟨16210417683401105454128963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10806945122267403636085975 16210417683401105454128963)
          ·
            refine ⟨24315626525101658181193445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16210417683401105454128963 24315626525101658181193445)
            ·
              refine ⟨4559179973456560908973771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24315626525101658181193445 4559179973456560908973771)
              ·
                refine ⟨6838769960184841363460657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4559179973456560908973771 6838769960184841363460657)
                ·
                  refine ⟨5129077470138631022595493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6838769960184841363460657 5129077470138631022595493)
                  ·
                    refine ⟨961702025650993316736655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5129077470138631022595493 961702025650993316736655)
                    ·
                      rfl

theorem cell23_5618724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_5618724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618724 prefixEnd_5618724 := by exact prefixLift 5618724
  have htrace : WordTrace (prefixWord ++ tailWord_5618724) baseStart_5618724 baseEnd_5618724 := by
    simpa [prefixWord, tailWord_5618724, baseEnd_5618724] using wordTrace_append hprefix tailTrace_5618724
  have hstable : (prefixWord ++ tailWord_5618724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618724).length < 2 ^ (prefixWord ++ tailWord_5618724).sum := by decide
  have hdescent : baseEnd_5618724 < baseStart_5618724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618757 : List Nat := [1, 3, 1, 1, 1, 3, 2, 5, 1, 3, 2]
def baseStart_5618757 : Nat := 118140960795 + 5618757 * 2 ^ 59
def prefixEnd_5618757 : Nat := 4983230072969 + 3 ^ 40 * 5618757 * 2
def baseEnd_5618757 : Nat := 2885123021814578321097313

theorem tailTrace_5618757 : CollatzResearch.WordTrace tailWord_5618757 prefixEnd_5618757 2885123021814578321097313 := by
  unfold tailWord_5618757
  simp only [CollatzResearch.WordTrace]
  refine ⟨204932903705210471142470525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136621935803473647428313683 204932903705210471142470525)
  ·
    refine ⟨76849838889453926678426447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204932903705210471142470525 76849838889453926678426447)
    ·
      refine ⟨115274758334180890017639671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76849838889453926678426447 115274758334180890017639671)
      ·
        refine ⟨172912137501271335026459507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115274758334180890017639671 172912137501271335026459507)
        ·
          refine ⟨259368206251907002539689261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172912137501271335026459507 259368206251907002539689261)
          ·
            refine ⟨97263077344465125952383473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 259368206251907002539689261 97263077344465125952383473)
            ·
              refine ⟨72947308008348844464287605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97263077344465125952383473 72947308008348844464287605)
              ·
                refine ⟨6838810125782704168526963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72947308008348844464287605 6838810125782704168526963)
                ·
                  refine ⟨10258215188674056252790445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6838810125782704168526963 10258215188674056252790445)
                  ·
                    refine ⟨3846830695752771094796417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10258215188674056252790445 3846830695752771094796417)
                    ·
                      refine ⟨2885123021814578321097313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3846830695752771094796417 2885123021814578321097313)
                      ·
                        rfl

theorem cell23_5618757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 3, 2].length) (baseStart_5618757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618757 prefixEnd_5618757 := by exact prefixLift 5618757
  have htrace : WordTrace (prefixWord ++ tailWord_5618757) baseStart_5618757 baseEnd_5618757 := by
    simpa [prefixWord, tailWord_5618757, baseEnd_5618757] using wordTrace_append hprefix tailTrace_5618757
  have hstable : (prefixWord ++ tailWord_5618757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618757).length < 2 ^ (prefixWord ++ tailWord_5618757).sum := by decide
  have hdescent : baseEnd_5618757 < baseStart_5618757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618765 : List Nat := [1, 6, 1, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_5618765 : Nat := 118140960795 + 5618765 * 2 ^ 59
def prefixEnd_5618765 : Nat := 4983230072969 + 3 ^ 40 * 5618765 * 2
def baseEnd_5618765 : Nat := 2885127129659814289797277

theorem tailTrace_5618765 : CollatzResearch.WordTrace tailWord_5618765 prefixEnd_5618765 2885127129659814289797277 := by
  unfold tailWord_5618765
  simp only [CollatzResearch.WordTrace]
  refine ⟨204933195489181488508761749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136622130326120992339174499 204933195489181488508761749)
  ·
    refine ⟨9606243538555382273848207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 204933195489181488508761749 9606243538555382273848207)
    ·
      refine ⟨14409365307833073410772311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9606243538555382273848207 14409365307833073410772311)
      ·
        refine ⟨21614047961749610116158467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14409365307833073410772311 21614047961749610116158467)
        ·
          refine ⟨32421071942624415174237701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21614047961749610116158467 32421071942624415174237701)
          ·
            refine ⟨6078950989242077845169569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32421071942624415174237701 6078950989242077845169569)
            ·
              refine ⟨4559213241931558383877177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6078950989242077845169569 4559213241931558383877177)
              ·
                refine ⟨3419409931448668787907883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4559213241931558383877177 3419409931448668787907883)
                ·
                  refine ⟨5129114897173003181861825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3419409931448668787907883 5129114897173003181861825)
                  ·
                    refine ⟨3846836172879752386396369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5129114897173003181861825 3846836172879752386396369)
                    ·
                      refine ⟨2885127129659814289797277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3846836172879752386396369 2885127129659814289797277)
                      ·
                        rfl

theorem cell23_5618765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_5618765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618765 prefixEnd_5618765 := by exact prefixLift 5618765
  have htrace : WordTrace (prefixWord ++ tailWord_5618765) baseStart_5618765 baseEnd_5618765 := by
    simpa [prefixWord, tailWord_5618765, baseEnd_5618765] using wordTrace_append hprefix tailTrace_5618765
  have hstable : (prefixWord ++ tailWord_5618765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618765).length < 2 ^ (prefixWord ++ tailWord_5618765).sum := by decide
  have hdescent : baseEnd_5618765 < baseStart_5618765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618770 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_5618770 : Nat := 118140960795 + 5618770 * 2 ^ 59
def prefixEnd_5618770 : Nat := 4983230072969 + 3 ^ 40 * 5618770 * 2
def baseEnd_5618770 : Nat := 2885129697063086770234753

theorem tailTrace_5618770 : CollatzResearch.WordTrace tailWord_5618770 prefixEnd_5618770 2885129697063086770234753 := by
  unfold tailWord_5618770
  simp only [CollatzResearch.WordTrace]
  refine ⟨51233344463540843590673441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136622251902775582908462509 51233344463540843590673441)
  ·
    refine ⟨38425008347655632693005081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51233344463540843590673441 38425008347655632693005081)
    ·
      refine ⟨28818756260741724519753811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38425008347655632693005081 28818756260741724519753811)
      ·
        refine ⟨43228134391112586779630717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28818756260741724519753811 43228134391112586779630717)
        ·
          refine ⟨16210550396667220042361519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43228134391112586779630717 16210550396667220042361519)
          ·
            refine ⟨24315825595000830063542279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16210550396667220042361519 24315825595000830063542279)
            ·
              refine ⟨36473738392501245095313419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24315825595000830063542279 36473738392501245095313419)
              ·
                refine ⟨54710607588751867642970129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36473738392501245095313419 54710607588751867642970129)
                ·
                  refine ⟨41032955691563900732227597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54710607588751867642970129 41032955691563900732227597)
                  ·
                    refine ⟨15387358384336462774585349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41032955691563900732227597 15387358384336462774585349)
                    ·
                      refine ⟨2885129697063086770234753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15387358384336462774585349 2885129697063086770234753)
                      ·
                        rfl

theorem cell23_5618770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_5618770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618770 prefixEnd_5618770 := by exact prefixLift 5618770
  have htrace : WordTrace (prefixWord ++ tailWord_5618770) baseStart_5618770 baseEnd_5618770 := by
    simpa [prefixWord, tailWord_5618770, baseEnd_5618770] using wordTrace_append hprefix tailTrace_5618770
  have hstable : (prefixWord ++ tailWord_5618770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618770).length < 2 ^ (prefixWord ++ tailWord_5618770).sum := by decide
  have hdescent : baseEnd_5618770 < baseStart_5618770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618780 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 2, 6]
def baseStart_5618780 : Nat := 118140960795 + 5618780 * 2 ^ 59
def prefixEnd_5618780 : Nat := 4983230072969 + 3 ^ 40 * 5618780 * 2
def baseEnd_5618780 : Nat := 961711610623210577036569

theorem tailTrace_5618780 : CollatzResearch.WordTrace tailWord_5618780 prefixEnd_5618780 961711610623210577036569 := by
  unfold tailWord_5618780
  simp only [CollatzResearch.WordTrace]
  refine ⟨102466871292063573035278897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136622495056084764047038529 102466871292063573035278897)
  ·
    refine ⟨76850153469047679776459173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102466871292063573035278897 76850153469047679776459173)
    ·
      refine ⟨14409403775446439958086095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76850153469047679776459173 14409403775446439958086095)
      ·
        refine ⟨21614105663169659937129143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14409403775446439958086095 21614105663169659937129143)
        ·
          refine ⟨32421158494754489905693715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21614105663169659937129143 32421158494754489905693715)
          ·
            refine ⟨48631737742131734858540573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32421158494754489905693715 48631737742131734858540573)
            ·
              refine ⟨18236901653299400571952715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48631737742131734858540573 18236901653299400571952715)
              ·
                refine ⟨27355352479949100857929073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18236901653299400571952715 27355352479949100857929073)
                ·
                  refine ⟨20516514359961825643446805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27355352479949100857929073 20516514359961825643446805)
                  ·
                    refine ⟨961711610623210577036569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20516514359961825643446805 961711610623210577036569)
                    ·
                      rfl

theorem cell23_5618780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_5618780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618780 prefixEnd_5618780 := by exact prefixLift 5618780
  have htrace : WordTrace (prefixWord ++ tailWord_5618780) baseStart_5618780 baseEnd_5618780 := by
    simpa [prefixWord, tailWord_5618780, baseEnd_5618780] using wordTrace_append hprefix tailTrace_5618780
  have hstable : (prefixWord ++ tailWord_5618780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618780).length < 2 ^ (prefixWord ++ tailWord_5618780).sum := by decide
  have hdescent : baseEnd_5618780 < baseStart_5618780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618787 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 6, 2, 2]
def baseStart_5618787 : Nat := 118140960795 + 5618787 * 2 ^ 59
def prefixEnd_5618787 : Nat := 4983230072969 + 3 ^ 40 * 5618787 * 2
def baseEnd_5618787 : Nat := 2885138426234213203722175

theorem tailTrace_5618787 : CollatzResearch.WordTrace tailWord_5618787 prefixEnd_5618787 2885138426234213203722175 := by
  unfold tailWord_5618787
  simp only [CollatzResearch.WordTrace]
  refine ⟨204933997895101786266062615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136622665263401190844041743 204933997895101786266062615)
  ·
    refine ⟨307400996842652679399093923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204933997895101786266062615 307400996842652679399093923)
    ·
      refine ⟨461101495263979019098640885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307400996842652679399093923 461101495263979019098640885)
      ·
        refine ⟨43228265180998033040497583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 461101495263979019098640885 43228265180998033040497583)
        ·
          refine ⟨64842397771497049560746375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43228265180998033040497583 64842397771497049560746375)
          ·
            refine ⟨97263596657245574341119563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64842397771497049560746375 97263596657245574341119563)
            ·
              refine ⟨145895394985868361511679345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97263596657245574341119563 145895394985868361511679345)
              ·
                refine ⟨109421546239401271133759509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145895394985868361511679345 109421546239401271133759509)
                ·
                  refine ⟨5129134979971934584394977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109421546239401271133759509 5129134979971934584394977)
                  ·
                    refine ⟨3846851234978950938296233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5129134979971934584394977 3846851234978950938296233)
                    ·
                      refine ⟨2885138426234213203722175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3846851234978950938296233 2885138426234213203722175)
                      ·
                        rfl

theorem cell23_5618787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_5618787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618787 prefixEnd_5618787 := by exact prefixLift 5618787
  have htrace : WordTrace (prefixWord ++ tailWord_5618787) baseStart_5618787 baseEnd_5618787 := by
    simpa [prefixWord, tailWord_5618787, baseEnd_5618787] using wordTrace_append hprefix tailTrace_5618787
  have hstable : (prefixWord ++ tailWord_5618787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618787).length < 2 ^ (prefixWord ++ tailWord_5618787).sum := by decide
  have hdescent : baseEnd_5618787 < baseStart_5618787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618793 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 9]
def baseStart_5618793 : Nat := 118140960795 + 5618793 * 2 ^ 59
def prefixEnd_5618793 : Nat := 4983230072969 + 3 ^ 40 * 5618793 * 2
def baseEnd_5618793 : Nat := 320571278568682242249683

theorem tailTrace_5618793 : CollatzResearch.WordTrace tailWord_5618793 prefixEnd_5618793 320571278568682242249683 := by
  unfold tailWord_5618793
  simp only [CollatzResearch.WordTrace]
  refine ⟨204934216733080049290781033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136622811155386699527187355 204934216733080049290781033)
  ·
    refine ⟨153700662549810036968085775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204934216733080049290781033 153700662549810036968085775)
    ·
      refine ⟨230550993824715055452128663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153700662549810036968085775 230550993824715055452128663)
      ·
        refine ⟨345826490737072583178192995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230550993824715055452128663 345826490737072583178192995)
        ·
          refine ⟨518739736105608874767289493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345826490737072583178192995 518739736105608874767289493)
          ·
            refine ⟨24315925129950416004716695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 518739736105608874767289493 24315925129950416004716695)
            ·
              refine ⟨36473887694925624007075043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24315925129950416004716695 36473887694925624007075043)
              ·
                refine ⟨54710831542388436010612565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36473887694925624007075043 54710831542388436010612565)
                ·
                  refine ⟨320571278568682242249683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54710831542388436010612565 320571278568682242249683)
                  ·
                    rfl

theorem cell23_5618793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 9].length) (baseStart_5618793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618793 prefixEnd_5618793 := by exact prefixLift 5618793
  have htrace : WordTrace (prefixWord ++ tailWord_5618793) baseStart_5618793 baseEnd_5618793 := by
    simpa [prefixWord, tailWord_5618793, baseEnd_5618793] using wordTrace_append hprefix tailTrace_5618793
  have hstable : (prefixWord ++ tailWord_5618793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618793).length < 2 ^ (prefixWord ++ tailWord_5618793).sum := by decide
  have hdescent : baseEnd_5618793 < baseStart_5618793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618840 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 1, 7]
def baseStart_5618840 : Nat := 118140960795 + 5618840 * 2 ^ 59
def prefixEnd_5618840 : Nat := 4983230072969 + 3 ^ 40 * 5618840 * 2
def baseEnd_5618840 : Nat := 961721880236300498786477

theorem tailTrace_5618840 : CollatzResearch.WordTrace tailWord_5618840 prefixEnd_5618840 961721880236300498786477 := by
  unfold tailWord_5618840
  simp only [CollatzResearch.WordTrace]
  refine ⟨102467965481954888158870987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136623953975939850878494649 102467965481954888158870987)
  ·
    refine ⟨153701948222932332238306481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102467965481954888158870987 153701948222932332238306481)
    ·
      refine ⟨115276461167199249178729861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153701948222932332238306481 115276461167199249178729861)
      ·
        refine ⟨21614336468849859221011849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115276461167199249178729861 21614336468849859221011849)
        ·
          refine ⟨16210752351637394415758887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21614336468849859221011849 16210752351637394415758887)
          ·
            refine ⟨24316128527456091623638331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16210752351637394415758887 24316128527456091623638331)
            ·
              refine ⟨36474192791184137435457497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24316128527456091623638331 36474192791184137435457497)
              ·
                refine ⟨27355644593388103076593123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36474192791184137435457497 27355644593388103076593123)
                ·
                  refine ⟨41033466890082154614889685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27355644593388103076593123 41033466890082154614889685)
                  ·
                    refine ⟨961721880236300498786477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41033466890082154614889685 961721880236300498786477)
                    ·
                      rfl

theorem cell23_5618840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_5618840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618840 prefixEnd_5618840 := by exact prefixLift 5618840
  have htrace : WordTrace (prefixWord ++ tailWord_5618840) baseStart_5618840 baseEnd_5618840 := by
    simpa [prefixWord, tailWord_5618840, baseEnd_5618840] using wordTrace_append hprefix tailTrace_5618840
  have hstable : (prefixWord ++ tailWord_5618840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618840).length < 2 ^ (prefixWord ++ tailWord_5618840).sum := by decide
  have hdescent : baseEnd_5618840 < baseStart_5618840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618861 : List Nat := [1, 5, 2, 1, 3, 2, 1, 3, 5]
def baseStart_5618861 : Nat := 118140960795 + 5618861 * 2 ^ 59
def prefixEnd_5618861 : Nat := 4983230072969 + 3 ^ 40 * 5618861 * 2
def baseEnd_5618861 : Nat := 320575158200293990466315

theorem tailTrace_5618861 : CollatzResearch.WordTrace tailWord_5618861 prefixEnd_5618861 320575158200293990466315 := by
  unfold tailWord_5618861
  simp only [CollatzResearch.WordTrace]
  refine ⟨204936696896833696904256437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136624464597889131269504291 204936696896833696904256437)
  ·
    refine ⟨19212815334078159084774041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204936696896833696904256437 19212815334078159084774041)
    ·
      refine ⟨14409611500558619313580531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19212815334078159084774041 14409611500558619313580531)
      ·
        refine ⟨21614417250837928970370797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14409611500558619313580531 21614417250837928970370797)
        ·
          refine ⟨8105406469064223363889049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21614417250837928970370797 8105406469064223363889049)
          ·
            refine ⟨6079054851798167522916787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8105406469064223363889049 6079054851798167522916787)
            ·
              refine ⟨9118582277697251284375181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6079054851798167522916787 9118582277697251284375181)
              ·
                refine ⟨3419468354136469231640693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9118582277697251284375181 3419468354136469231640693)
                ·
                  refine ⟨320575158200293990466315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3419468354136469231640693 320575158200293990466315)
                  ·
                    rfl

theorem cell23_5618861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_5618861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618861 prefixEnd_5618861 := by exact prefixLift 5618861
  have htrace : WordTrace (prefixWord ++ tailWord_5618861) baseStart_5618861 baseEnd_5618861 := by
    simpa [prefixWord, tailWord_5618861, baseEnd_5618861] using wordTrace_append hprefix tailTrace_5618861
  have hstable : (prefixWord ++ tailWord_5618861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618861).length < 2 ^ (prefixWord ++ tailWord_5618861).sum := by decide
  have hdescent : baseEnd_5618861 < baseStart_5618861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618877 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 4, 4, 2]
def baseStart_5618877 : Nat := 118140960795 + 5618877 * 2 ^ 59
def prefixEnd_5618877 : Nat := 4983230072969 + 3 ^ 40 * 5618877 * 2
def baseEnd_5618877 : Nat := 2885184639493117851596761

theorem tailTrace_5618877 : CollatzResearch.WordTrace tailWord_5618877 prefixEnd_5618877 2885184639493117851596761 := by
  unfold tailWord_5618877
  simp only [CollatzResearch.WordTrace]
  refine ⟨204937280464775731636838885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136624853643183821091225923 204937280464775731636838885)
  ·
    refine ⟨38425740087145449681907291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204937280464775731636838885 38425740087145449681907291)
    ·
      refine ⟨57638610130718174522860937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38425740087145449681907291 57638610130718174522860937)
      ·
        refine ⟨43228957598038630892145703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57638610130718174522860937 43228957598038630892145703)
        ·
          refine ⟨64843436397057946338218555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43228957598038630892145703 64843436397057946338218555)
          ·
            refine ⟨97265154595586919507327833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64843436397057946338218555 97265154595586919507327833)
            ·
              refine ⟨72948865946690189630495875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97265154595586919507327833 72948865946690189630495875)
              ·
                refine ⟨109423298920035284445743813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72948865946690189630495875 109423298920035284445743813)
                ·
                  refine ⟨20516868547506615833576965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109423298920035284445743813 20516868547506615833576965)
                  ·
                    refine ⟨3846912852657490468795681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20516868547506615833576965 3846912852657490468795681)
                    ·
                      refine ⟨2885184639493117851596761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3846912852657490468795681 2885184639493117851596761)
                      ·
                        rfl

theorem cell23_5618877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_5618877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618877 prefixEnd_5618877 := by exact prefixLift 5618877
  have htrace : WordTrace (prefixWord ++ tailWord_5618877) baseStart_5618877 baseEnd_5618877 := by
    simpa [prefixWord, tailWord_5618877, baseEnd_5618877] using wordTrace_append hprefix tailTrace_5618877
  have hstable : (prefixWord ++ tailWord_5618877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618877).length < 2 ^ (prefixWord ++ tailWord_5618877).sum := by decide
  have hdescent : baseEnd_5618877 < baseStart_5618877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618967 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 4]
def baseStart_5618967 : Nat := 118140960795 + 5618967 * 2 ^ 59
def prefixEnd_5618967 : Nat := 4983230072969 + 3 ^ 40 * 5618967 * 2
def baseEnd_5618967 : Nat := 2885230852752022499471347

theorem tailTrace_5618967 : CollatzResearch.WordTrace tailWord_5618967 prefixEnd_5618967 2885230852752022499471347 := by
  unfold tailWord_5618967
  simp only [CollatzResearch.WordTrace]
  refine ⟨204940563034449677007615155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136627042022966451338410103 204940563034449677007615155)
  ·
    refine ⟨307410844551674515511422733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204940563034449677007615155 307410844551674515511422733)
    ·
      refine ⟨115279066706877943316783525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307410844551674515511422733 115279066706877943316783525)
      ·
        refine ⟨21614825007539614371896911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115279066706877943316783525 21614825007539614371896911)
        ·
          refine ⟨32422237511309421557845367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21614825007539614371896911 32422237511309421557845367)
          ·
            refine ⟨48633356266964132336768051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32422237511309421557845367 48633356266964132336768051)
            ·
              refine ⟨72950034400446198505152077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48633356266964132336768051 72950034400446198505152077)
              ·
                refine ⟨27356262900167324439432029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72950034400446198505152077 27356262900167324439432029)
                ·
                  refine ⟨10258598587562746664787011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27356262900167324439432029 10258598587562746664787011)
                  ·
                    refine ⟨15387897881344119997180517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10258598587562746664787011 15387897881344119997180517)
                    ·
                      refine ⟨2885230852752022499471347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15387897881344119997180517 2885230852752022499471347)
                      ·
                        rfl

theorem cell23_5618967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_5618967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618967 prefixEnd_5618967 := by exact prefixLift 5618967
  have htrace : WordTrace (prefixWord ++ tailWord_5618967) baseStart_5618967 baseEnd_5618967 := by
    simpa [prefixWord, tailWord_5618967, baseEnd_5618967] using wordTrace_append hprefix tailTrace_5618967
  have hstable : (prefixWord ++ tailWord_5618967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618967).length < 2 ^ (prefixWord ++ tailWord_5618967).sum := by decide
  have hdescent : baseEnd_5618967 < baseStart_5618967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618977 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 4, 4]
def baseStart_5618977 : Nat := 118140960795 + 5618977 * 2 ^ 59
def prefixEnd_5618977 : Nat := 4983230072969 + 3 ^ 40 * 5618977 * 2
def baseEnd_5618977 : Nat := 961745329186189153448767

theorem tailTrace_5618977 : CollatzResearch.WordTrace tailWord_5618977 prefixEnd_5618977 961745329186189153448767 := by
  unfold tailWord_5618977
  simp only [CollatzResearch.WordTrace]
  refine ⟨204940927764413448715479185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136627285176275632476986123 204940927764413448715479185)
  ·
    refine ⟨153705695823310086536609389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204940927764413448715479185 153705695823310086536609389)
    ·
      refine ⟨57639635933741282451228521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153705695823310086536609389 57639635933741282451228521)
      ·
        refine ⟨43229726950305961838421391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57639635933741282451228521 43229726950305961838421391)
        ·
          refine ⟨64844590425458942757632087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43229726950305961838421391 64844590425458942757632087)
          ·
            refine ⟨97266885638188414136448131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64844590425458942757632087 97266885638188414136448131)
            ·
              refine ⟨145900328457282621204672197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97266885638188414136448131 145900328457282621204672197)
              ·
                refine ⟨27356311585740491475876037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145900328457282621204672197 27356311585740491475876037)
                ·
                  refine ⟨5129308422326342151726757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27356311585740491475876037 5129308422326342151726757)
                  ·
                    refine ⟨961745329186189153448767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5129308422326342151726757 961745329186189153448767)
                    ·
                      rfl

theorem cell23_5618977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_5618977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618977 prefixEnd_5618977 := by exact prefixLift 5618977
  have htrace : WordTrace (prefixWord ++ tailWord_5618977) baseStart_5618977 baseEnd_5618977 := by
    simpa [prefixWord, tailWord_5618977, baseEnd_5618977] using wordTrace_append hprefix tailTrace_5618977
  have hstable : (prefixWord ++ tailWord_5618977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618977).length < 2 ^ (prefixWord ++ tailWord_5618977).sum := by decide
  have hdescent : baseEnd_5618977 < baseStart_5618977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618981 : List Nat := [1, 3, 1, 2, 4, 3, 2, 1, 1, 5]
def baseStart_5618981 : Nat := 118140960795 + 5618981 * 2 ^ 59
def prefixEnd_5618981 : Nat := 4983230072969 + 3 ^ 40 * 5618981 * 2
def baseEnd_5618981 : Nat := 961746013827061814898761

theorem tailTrace_5618981 : CollatzResearch.WordTrace tailWord_5618981 prefixEnd_5618981 961746013827061814898761 := by
  unfold tailWord_5618981
  simp only [CollatzResearch.WordTrace]
  refine ⟨204941073656398957398624797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136627382437599304932416531 204941073656398957398624797)
  ·
    refine ⟨76852902621149609024484299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204941073656398957398624797 76852902621149609024484299)
    ·
      refine ⟨115279353931724413536726449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76852902621149609024484299 115279353931724413536726449)
      ·
        refine ⟨86459515448793310152544837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115279353931724413536726449 86459515448793310152544837)
        ·
          refine ⟨16211159146648745653602157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86459515448793310152544837 16211159146648745653602157)
          ·
            refine ⟨6079184679993279620100809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16211159146648745653602157 6079184679993279620100809)
            ·
              refine ⟨4559388509994959715075607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6079184679993279620100809 4559388509994959715075607)
              ·
                refine ⟨6839082764992439572613411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4559388509994959715075607 6839082764992439572613411)
                ·
                  refine ⟨10258624147488659358920117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6839082764992439572613411 10258624147488659358920117)
                  ·
                    refine ⟨961746013827061814898761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10258624147488659358920117 961746013827061814898761)
                    ·
                      rfl

theorem cell23_5618981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_5618981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618981 prefixEnd_5618981 := by exact prefixLift 5618981
  have htrace : WordTrace (prefixWord ++ tailWord_5618981) baseStart_5618981 baseEnd_5618981 := by
    simpa [prefixWord, tailWord_5618981, baseEnd_5618981] using wordTrace_append hprefix tailTrace_5618981
  have hstable : (prefixWord ++ tailWord_5618981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618981).length < 2 ^ (prefixWord ++ tailWord_5618981).sum := by decide
  have hdescent : baseEnd_5618981 < baseStart_5618981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5618994 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 4, 4]
def baseStart_5618994 : Nat := 118140960795 + 5618994 * 2 ^ 59
def prefixEnd_5618994 : Nat := 4983230072969 + 3 ^ 40 * 5618994 * 2
def baseEnd_5618994 : Nat := 961748238909897964611241

theorem tailTrace_5618994 : CollatzResearch.WordTrace tailWord_5618994 prefixEnd_5618994 961748238909897964611241 := by
  unfold tailWord_5618994
  simp only [CollatzResearch.WordTrace]
  refine ⟨51235386951337965154712009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136627698536901240412565357 51235386951337965154712009)
  ·
    refine ⟨38426540213503473866034007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51235386951337965154712009 38426540213503473866034007)
    ·
      refine ⟨57639810320255210799051011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38426540213503473866034007 57639810320255210799051011)
      ·
        refine ⟨86459715480382816198576517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57639810320255210799051011 86459715480382816198576517)
        ·
          refine ⟨16211196652571778037233097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86459715480382816198576517 16211196652571778037233097)
          ·
            refine ⟨12158397489428833527924823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16211196652571778037233097 12158397489428833527924823)
            ·
              refine ⟨18237596234143250291887235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12158397489428833527924823 18237596234143250291887235)
              ·
                refine ⟨27356394351214875437830853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18237596234143250291887235 27356394351214875437830853)
                ·
                  refine ⟨5129323940852789144593285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27356394351214875437830853 5129323940852789144593285)
                  ·
                    refine ⟨961748238909897964611241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5129323940852789144593285 961748238909897964611241)
                    ·
                      rfl

theorem cell23_5618994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_5618994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5618994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5618994 prefixEnd_5618994 := by exact prefixLift 5618994
  have htrace : WordTrace (prefixWord ++ tailWord_5618994) baseStart_5618994 baseEnd_5618994 := by
    simpa [prefixWord, tailWord_5618994, baseEnd_5618994] using wordTrace_append hprefix tailTrace_5618994
  have hstable : (prefixWord ++ tailWord_5618994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5618994).length < 2 ^ (prefixWord ++ tailWord_5618994).sum := by decide
  have hdescent : baseEnd_5618994 < baseStart_5618994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5618994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619000 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 2, 2, 7]
def baseStart_5619000 : Nat := 118140960795 + 5619000 * 2 ^ 59
def prefixEnd_5619000 : Nat := 4983230072969 + 3 ^ 40 * 5619000 * 2
def baseEnd_5619000 : Nat := 2885247797613620870358695

theorem tailTrace_5619000 : CollatzResearch.WordTrace tailWord_5619000 prefixEnd_5619000 2885247797613620870358695 := by
  unfold tailWord_5619000
  simp only [CollatzResearch.WordTrace]
  refine ⟨102470883321665061821783227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136627844428886749095710969 102470883321665061821783227)
  ·
    refine ⟨153706324982497592732674841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102470883321665061821783227 153706324982497592732674841)
    ·
      refine ⟨115279743736873194549506131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153706324982497592732674841 115279743736873194549506131)
      ·
        refine ⟨172919615605309791824259197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115279743736873194549506131 172919615605309791824259197)
        ·
          refine ⟨64844855851991171934097199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172919615605309791824259197 64844855851991171934097199)
          ·
            refine ⟨97267283777986757901145799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64844855851991171934097199 97267283777986757901145799)
            ·
              refine ⟨145900925666980136851718699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97267283777986757901145799 145900925666980136851718699)
              ·
                refine ⟨218851388500470205277578049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145900925666980136851718699 218851388500470205277578049)
                ·
                  refine ⟨164138541375352653958183537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218851388500470205277578049 164138541375352653958183537)
                  ·
                    refine ⟨123103906031514490468637653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 164138541375352653958183537 123103906031514490468637653)
                    ·
                      refine ⟨2885247797613620870358695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123103906031514490468637653 2885247797613620870358695)
                      ·
                        rfl

theorem cell23_5619000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_5619000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619000 prefixEnd_5619000 := by exact prefixLift 5619000
  have htrace : WordTrace (prefixWord ++ tailWord_5619000) baseStart_5619000 baseEnd_5619000 := by
    simpa [prefixWord, tailWord_5619000, baseEnd_5619000] using wordTrace_append hprefix tailTrace_5619000
  have hstable : (prefixWord ++ tailWord_5619000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619000).length < 2 ^ (prefixWord ++ tailWord_5619000).sum := by decide
  have hdescent : baseEnd_5619000 < baseStart_5619000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619034 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3]
def baseStart_5619034 : Nat := 118140960795 + 5619034 * 2 ^ 59
def prefixEnd_5619034 : Nat := 4983230072969 + 3 ^ 40 * 5619034 * 2
def baseEnd_5619034 : Nat := 2885265255955873737333539

theorem tailTrace_5619034 : CollatzResearch.WordTrace tailWord_5619034 prefixEnd_5619034 2885265255955873737333539 := by
  unfold tailWord_5619034
  simp only [CollatzResearch.WordTrace]
  refine ⟨51235751681301736862576039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136628671150137964966869437 51235751681301736862576039)
  ·
    refine ⟨76853627521952605293864059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51235751681301736862576039 76853627521952605293864059)
    ·
      refine ⟨115280441282928907940796089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76853627521952605293864059 115280441282928907940796089)
      ·
        refine ⟨86460330962196680955597067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115280441282928907940796089 86460330962196680955597067)
        ·
          refine ⟨129690496443295021433395601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86460330962196680955597067 129690496443295021433395601)
          ·
            refine ⟨97267872332471266075046701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129690496443295021433395601 97267872332471266075046701)
            ·
              refine ⟨36475452124676724778142513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97267872332471266075046701 36475452124676724778142513)
              ·
                refine ⟨27356589093507543583606885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36475452124676724778142513 27356589093507543583606885)
                ·
                  refine ⟨5129360455032664421926291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27356589093507543583606885 5129360455032664421926291)
                  ·
                    refine ⟨7694040682548996632889437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5129360455032664421926291 7694040682548996632889437)
                    ·
                      refine ⟨2885265255955873737333539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7694040682548996632889437 2885265255955873737333539)
                      ·
                        rfl

theorem cell23_5619034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_5619034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619034 prefixEnd_5619034 := by exact prefixLift 5619034
  have htrace : WordTrace (prefixWord ++ tailWord_5619034) baseStart_5619034 baseEnd_5619034 := by
    simpa [prefixWord, tailWord_5619034, baseEnd_5619034] using wordTrace_append hprefix tailTrace_5619034
  have hstable : (prefixWord ++ tailWord_5619034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619034).length < 2 ^ (prefixWord ++ tailWord_5619034).sum := by decide
  have hdescent : baseEnd_5619034 < baseStart_5619034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619077 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 5]
def baseStart_5619077 : Nat := 118140960795 + 5619077 * 2 ^ 59
def prefixEnd_5619077 : Nat := 4983230072969 + 3 ^ 40 * 5619077 * 2
def baseEnd_5619077 : Nat := 2885287335624017069095841

theorem tailTrace_5619077 : CollatzResearch.WordTrace tailWord_5619077 prefixEnd_5619077 2885287335624017069095841 := by
  unfold tailWord_5619077
  simp only [CollatzResearch.WordTrace]
  refine ⟨204944575064051165794119485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136629716709367443862746323 204944575064051165794119485)
  ·
    refine ⟨76854215649019187172794807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204944575064051165794119485 76854215649019187172794807)
    ·
      refine ⟨115281323473528780759192211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76854215649019187172794807 115281323473528780759192211)
      ·
        refine ⟨172921985210293171138788317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115281323473528780759192211 172921985210293171138788317)
        ·
          refine ⟨64845744453859939177045619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172921985210293171138788317 64845744453859939177045619)
          ·
            refine ⟨97268616680789908765568429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64845744453859939177045619 97268616680789908765568429)
            ·
              refine ⟨36475731255296215787088161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97268616680789908765568429 36475731255296215787088161)
              ·
                refine ⟨27356798441472161840316121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36475731255296215787088161 27356798441472161840316121)
                ·
                  refine ⟨20517598831104121380237091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27356798441472161840316121 20517598831104121380237091)
                  ·
                    refine ⟨30776398246656182070355637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20517598831104121380237091 30776398246656182070355637)
                    ·
                      refine ⟨2885287335624017069095841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30776398246656182070355637 2885287335624017069095841)
                      ·
                        rfl

theorem cell23_5619077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_5619077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619077 prefixEnd_5619077 := by exact prefixLift 5619077
  have htrace : WordTrace (prefixWord ++ tailWord_5619077) baseStart_5619077 baseEnd_5619077 := by
    simpa [prefixWord, tailWord_5619077, baseEnd_5619077] using wordTrace_append hprefix tailTrace_5619077
  have hstable : (prefixWord ++ tailWord_5619077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619077).length < 2 ^ (prefixWord ++ tailWord_5619077).sum := by decide
  have hdescent : baseEnd_5619077 < baseStart_5619077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619127 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 1, 7]
def baseStart_5619127 : Nat := 118140960795 + 5619127 * 2 ^ 59
def prefixEnd_5619127 : Nat := 4983230072969 + 3 ^ 40 * 5619127 * 2
def baseEnd_5619127 : Nat := 961771003218913957823537

theorem tailTrace_5619127 : CollatzResearch.WordTrace tailWord_5619127 prefixEnd_5619127 961771003218913957823537 := by
  unfold tailWord_5619127
  simp only [CollatzResearch.WordTrace]
  refine ⟨204946398713870024333439635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136630932475913349555626423 204946398713870024333439635)
  ·
    refine ⟨307419598070805036500159453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204946398713870024333439635 307419598070805036500159453)
    ·
      refine ⟨115282349276551888687559795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307419598070805036500159453 115282349276551888687559795)
      ·
        refine ⟨172923523914827833031339693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115282349276551888687559795 172923523914827833031339693)
        ·
          refine ⟨64846321468060437386752385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172923523914827833031339693 64846321468060437386752385)
          ·
            refine ⟨48634741101045328040064289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64846321468060437386752385 48634741101045328040064289)
            ·
              refine ⟨36476055825783996030048217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48634741101045328040064289 36476055825783996030048217)
              ·
                refine ⟨27357041869337997022536163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36476055825783996030048217 27357041869337997022536163)
                ·
                  refine ⟨41035562804006995533804245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27357041869337997022536163 41035562804006995533804245)
                  ·
                    refine ⟨961771003218913957823537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41035562804006995533804245 961771003218913957823537)
                    ·
                      rfl

theorem cell23_5619127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_5619127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619127 prefixEnd_5619127 := by exact prefixLift 5619127
  have htrace : WordTrace (prefixWord ++ tailWord_5619127) baseStart_5619127 baseEnd_5619127 := by
    simpa [prefixWord, tailWord_5619127, baseEnd_5619127] using wordTrace_append hprefix tailTrace_5619127
  have hstable : (prefixWord ++ tailWord_5619127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619127).length < 2 ^ (prefixWord ++ tailWord_5619127).sum := by decide
  have hdescent : baseEnd_5619127 < baseStart_5619127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619184 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 3]
def baseStart_5619184 : Nat := 118140960795 + 5619184 * 2 ^ 59
def prefixEnd_5619184 : Nat := 4983230072969 + 3 ^ 40 * 5619184 * 2
def baseEnd_5619184 : Nat := 2885342278054048150457849

theorem tailTrace_5619184 : CollatzResearch.WordTrace tailWord_5619184 prefixEnd_5619184 2885342278054048150457849 := by
  unfold tailWord_5619184
  simp only [CollatzResearch.WordTrace]
  refine ⟨102474238837331761534132303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136632318449775682045509737 102474238837331761534132303)
  ·
    refine ⟨153711358255997642301198455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102474238837331761534132303 153711358255997642301198455)
    ·
      refine ⟨230567037383996463451797683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153711358255997642301198455 230567037383996463451797683)
      ·
        refine ⟨345850556075994695177696525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230567037383996463451797683 345850556075994695177696525)
        ·
          refine ⟨129693958528498010691636197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345850556075994695177696525 129693958528498010691636197)
          ·
            refine ⟨24317617224093377004681787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129693958528498010691636197 24317617224093377004681787)
            ·
              refine ⟨36476425836140065507022681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24317617224093377004681787 36476425836140065507022681)
              ·
                refine ⟨27357319377105049130267011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36476425836140065507022681 27357319377105049130267011)
                ·
                  refine ⟨41035979065657573695400517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27357319377105049130267011 41035979065657573695400517)
                  ·
                    refine ⟨7694246074810795067887597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41035979065657573695400517 7694246074810795067887597)
                    ·
                      refine ⟨2885342278054048150457849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7694246074810795067887597 2885342278054048150457849)
                      ·
                        rfl

theorem cell23_5619184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 3].length) (baseStart_5619184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619184 prefixEnd_5619184 := by exact prefixLift 5619184
  have htrace : WordTrace (prefixWord ++ tailWord_5619184) baseStart_5619184 baseEnd_5619184 := by
    simpa [prefixWord, tailWord_5619184, baseEnd_5619184] using wordTrace_append hprefix tailTrace_5619184
  have hstable : (prefixWord ++ tailWord_5619184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619184).length < 2 ^ (prefixWord ++ tailWord_5619184).sum := by decide
  have hdescent : baseEnd_5619184 < baseStart_5619184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619208 : List Nat := [2, 1, 3, 2, 1, 1, 5, 3, 1, 4]
def baseStart_5619208 : Nat := 118140960795 + 5619208 * 2 ^ 59
def prefixEnd_5619208 : Nat := 4983230072969 + 3 ^ 40 * 5619208 * 2
def baseEnd_5619208 : Nat := 961784867196585352185913

theorem tailTrace_5619208 : CollatzResearch.WordTrace tailWord_5619208 prefixEnd_5619208 961784867196585352185913 := by
  unfold tailWord_5619208
  simp only [CollatzResearch.WordTrace]
  refine ⟨102474676513288287583569139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136632902017717716778092185 102474676513288287583569139)
  ·
    refine ⟨153712014769932431375353709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102474676513288287583569139 153712014769932431375353709)
    ·
      refine ⟨57642005538724661765757641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153712014769932431375353709 57642005538724661765757641)
      ·
        refine ⟨43231504154043496324318231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57642005538724661765757641 43231504154043496324318231)
        ·
          refine ⟨64847256231065244486477347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43231504154043496324318231 64847256231065244486477347)
          ·
            refine ⟨97270884346597866729716021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64847256231065244486477347 97270884346597866729716021)
            ·
              refine ⟨9119145407493550005910877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97270884346597866729716021 9119145407493550005910877)
              ·
                refine ⟨3419679527810081252216579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9119145407493550005910877 3419679527810081252216579)
                ·
                  refine ⟨5129519291715121878324869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3419679527810081252216579 5129519291715121878324869)
                  ·
                    refine ⟨961784867196585352185913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5129519291715121878324869 961784867196585352185913)
                    ·
                      rfl

theorem cell23_5619208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_5619208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619208 prefixEnd_5619208 := by exact prefixLift 5619208
  have htrace : WordTrace (prefixWord ++ tailWord_5619208) baseStart_5619208 baseEnd_5619208 := by
    simpa [prefixWord, tailWord_5619208, baseEnd_5619208] using wordTrace_append hprefix tailTrace_5619208
  have hstable : (prefixWord ++ tailWord_5619208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619208).length < 2 ^ (prefixWord ++ tailWord_5619208).sum := by decide
  have hdescent : baseEnd_5619208 < baseStart_5619208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619251 : List Nat := [1, 1, 1, 2, 4, 3, 3, 2, 1, 5]
def baseStart_5619251 : Nat := 118140960795 + 5619251 * 2 ^ 59
def prefixEnd_5619251 : Nat := 4983230072969 + 3 ^ 40 * 5619251 * 2
def baseEnd_5619251 : Nat := 961792227085966462773347

theorem tailTrace_5619251 : CollatzResearch.WordTrace tailWord_5619251 prefixEnd_5619251 961792227085966462773347 := by
  unfold tailWord_5619251
  simp only [CollatzResearch.WordTrace]
  refine ⟨204950921365420793510953607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136633947576947195673969071 204950921365420793510953607)
  ·
    refine ⟨307426382048131190266430411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204950921365420793510953607 307426382048131190266430411)
    ·
      refine ⟨461139573072196785399645617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307426382048131190266430411 461139573072196785399645617)
      ·
        refine ⟨345854679804147589049734213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461139573072196785399645617 345854679804147589049734213)
        ·
          refine ⟨64847752463277672946825165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 345854679804147589049734213 64847752463277672946825165)
          ·
            refine ⟨24317907173729127355059437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64847752463277672946825165 24317907173729127355059437)
            ·
              refine ⟨9119215190148422758147289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24317907173729127355059437 9119215190148422758147289)
              ·
                refine ⟨6839411392611317068610467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9119215190148422758147289 6839411392611317068610467)
                ·
                  refine ⟨10259117088916975602915701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6839411392611317068610467 10259117088916975602915701)
                  ·
                    refine ⟨961792227085966462773347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10259117088916975602915701 961792227085966462773347)
                    ·
                      rfl

theorem cell23_5619251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 5].length) (baseStart_5619251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619251 prefixEnd_5619251 := by exact prefixLift 5619251
  have htrace : WordTrace (prefixWord ++ tailWord_5619251) baseStart_5619251 baseEnd_5619251 := by
    simpa [prefixWord, tailWord_5619251, baseEnd_5619251] using wordTrace_append hprefix tailTrace_5619251
  have hstable : (prefixWord ++ tailWord_5619251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619251).length < 2 ^ (prefixWord ++ tailWord_5619251).sum := by decide
  have hdescent : baseEnd_5619251 < baseStart_5619251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619258 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2]
def baseStart_5619258 : Nat := 118140960795 + 5619258 * 2 ^ 59
def prefixEnd_5619258 : Nat := 4983230072969 + 3 ^ 40 * 5619258 * 2
def baseEnd_5619258 : Nat := 2885380275622480860932509

theorem tailTrace_5619258 : CollatzResearch.WordTrace tailWord_5619258 prefixEnd_5619258 2885380275622480860932509 := by
  unfold tailWord_5619258
  simp only [CollatzResearch.WordTrace]
  refine ⟨51237794169098858426614607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136634117784263622470972285 51237794169098858426614607)
  ·
    refine ⟨76856691253648287639921911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51237794169098858426614607 76856691253648287639921911)
    ·
      refine ⟨115285036880472431459882867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76856691253648287639921911 115285036880472431459882867)
      ·
        refine ⟨172927555320708647189824301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115285036880472431459882867 172927555320708647189824301)
        ·
          refine ⟨64847833245265742696184113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172927555320708647189824301 64847833245265742696184113)
          ·
            refine ⟨48635874933949307022138085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64847833245265742696184113 48635874933949307022138085)
            ·
              refine ⟨9119226550115495066650891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48635874933949307022138085 9119226550115495066650891)
              ·
                refine ⟨13678839825173242599976337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9119226550115495066650891 13678839825173242599976337)
                ·
                  refine ⟨10259129868879931949982253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13678839825173242599976337 10259129868879931949982253)
                  ·
                    refine ⟨3847173700829974481243345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10259129868879931949982253 3847173700829974481243345)
                    ·
                      refine ⟨2885380275622480860932509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3847173700829974481243345 2885380275622480860932509)
                      ·
                        rfl

theorem cell23_5619258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2].length) (baseStart_5619258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619258 prefixEnd_5619258 := by exact prefixLift 5619258
  have htrace : WordTrace (prefixWord ++ tailWord_5619258) baseStart_5619258 baseEnd_5619258 := by
    simpa [prefixWord, tailWord_5619258, baseEnd_5619258] using wordTrace_append hprefix tailTrace_5619258
  have hstable : (prefixWord ++ tailWord_5619258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619258).length < 2 ^ (prefixWord ++ tailWord_5619258).sum := by decide
  have hdescent : baseEnd_5619258 < baseStart_5619258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619265 : List Nat := [1, 2, 5, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_5619265 : Nat := 118140960795 + 5619265 * 2 ^ 59
def prefixEnd_5619265 : Nat := 4983230072969 + 3 ^ 40 * 5619265 * 2
def baseEnd_5619265 : Nat := 2885383869987062333544977

theorem tailTrace_5619265 : CollatzResearch.WordTrace tailWord_5619265 prefixEnd_5619265 2885383869987062333544977 := by
  unfold tailWord_5619265
  simp only [CollatzResearch.WordTrace]
  refine ⟨204951431987370073901963249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136634287991580049267975499 204951431987370073901963249)
  ·
    refine ⟨153713573990527555426472437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204951431987370073901963249 153713573990527555426472437)
    ·
      refine ⟨14410647561611958321231791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153713573990527555426472437 14410647561611958321231791)
      ·
        refine ⟨21615971342417937481847687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14410647561611958321231791 21615971342417937481847687)
        ·
          refine ⟨32423957013626906222771531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21615971342417937481847687 32423957013626906222771531)
          ·
            refine ⟨48635935520440359334157297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32423957013626906222771531 48635935520440359334157297)
            ·
              refine ⟨36476951640330269500617973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48635935520440359334157297 36476951640330269500617973)
              ·
                refine ⟨3419714216280962765682935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36476951640330269500617973 3419714216280962765682935)
                ·
                  refine ⟨5129571324421444148524403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3419714216280962765682935 5129571324421444148524403)
                  ·
                    refine ⟨7694356986632166222786605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5129571324421444148524403 7694356986632166222786605)
                    ·
                      refine ⟨2885383869987062333544977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7694356986632166222786605 2885383869987062333544977)
                      ·
                        rfl

theorem cell23_5619265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_5619265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619265 prefixEnd_5619265 := by exact prefixLift 5619265
  have htrace : WordTrace (prefixWord ++ tailWord_5619265) baseStart_5619265 baseEnd_5619265 := by
    simpa [prefixWord, tailWord_5619265, baseEnd_5619265] using wordTrace_append hprefix tailTrace_5619265
  have hstable : (prefixWord ++ tailWord_5619265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619265).length < 2 ^ (prefixWord ++ tailWord_5619265).sum := by decide
  have hdescent : baseEnd_5619265 < baseStart_5619265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619282 : List Nat := [3, 2, 2, 1, 2, 2, 4, 2, 1, 1, 3]
def baseStart_5619282 : Nat := 118140960795 + 5619282 * 2 ^ 59
def prefixEnd_5619282 : Nat := 4983230072969 + 3 ^ 40 * 5619282 * 2
def baseEnd_5619282 : Nat := 2885392599158188767032399

theorem tailTrace_5619282 : CollatzResearch.WordTrace tailWord_5619282 prefixEnd_5619282 2885392599158188767032399 := by
  unfold tailWord_5619282
  simp only [CollatzResearch.WordTrace]
  refine ⟨51238013007077121451333025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136634701352205657203554733 51238013007077121451333025)
  ·
    refine ⟨38428509755307841088499769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51238013007077121451333025 38428509755307841088499769)
    ·
      refine ⟨28821382316480880816374827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38428509755307841088499769 28821382316480880816374827)
      ·
        refine ⟨43232073474721321224562241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28821382316480880816374827 43232073474721321224562241)
        ·
          refine ⟨32424055106040990918421681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43232073474721321224562241 32424055106040990918421681)
          ·
            refine ⟨24318041329530743188816261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32424055106040990918421681 24318041329530743188816261)
            ·
              refine ⟨4559632749287014347903049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24318041329530743188816261 4559632749287014347903049)
              ·
                refine ⟨3419724561965260760927287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4559632749287014347903049 3419724561965260760927287)
                ·
                  refine ⟨5129586842947891141390931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3419724561965260760927287 5129586842947891141390931)
                  ·
                    refine ⟨7694380264421836712086397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5129586842947891141390931 7694380264421836712086397)
                    ·
                      refine ⟨2885392599158188767032399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7694380264421836712086397 2885392599158188767032399)
                      ·
                        rfl

theorem cell23_5619282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_5619282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619282 prefixEnd_5619282 := by exact prefixLift 5619282
  have htrace : WordTrace (prefixWord ++ tailWord_5619282) baseStart_5619282 baseEnd_5619282 := by
    simpa [prefixWord, tailWord_5619282, baseEnd_5619282] using wordTrace_append hprefix tailTrace_5619282
  have hstable : (prefixWord ++ tailWord_5619282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619282).length < 2 ^ (prefixWord ++ tailWord_5619282).sum := by decide
  have hdescent : baseEnd_5619282 < baseStart_5619282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619288 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 3, 2, 2]
def baseStart_5619288 : Nat := 118140960795 + 5619288 * 2 ^ 59
def prefixEnd_5619288 : Nat := 4983230072969 + 3 ^ 40 * 5619288 * 2
def baseEnd_5619288 : Nat := 2885395680042115743557371

theorem tailTrace_5619288 : CollatzResearch.WordTrace tailWord_5619288 prefixEnd_5619288 2885395680042115743557371 := by
  unfold tailWord_5619288
  simp only [CollatzResearch.WordTrace]
  refine ⟨102476135433143374415025259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136634847244191165886700345 102476135433143374415025259)
  ·
    refine ⟨153714203149715061622537889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102476135433143374415025259 153714203149715061622537889)
    ·
      refine ⟨115285652362286296216903417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153714203149715061622537889 115285652362286296216903417)
      ·
        refine ⟨86464239271714722162677563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115285652362286296216903417 86464239271714722162677563)
        ·
          refine ⟨129696358907572083244016345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86464239271714722162677563 129696358907572083244016345)
          ·
            refine ⟨97272269180679062433012259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129696358907572083244016345 97272269180679062433012259)
            ·
              refine ⟨145908403771018593649518389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97272269180679062433012259 145908403771018593649518389)
              ·
                refine ⟨13678912853532993154642349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145908403771018593649518389 13678912853532993154642349)
                ·
                  refine ⟨5129592320074872432990881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13678912853532993154642349 5129592320074872432990881)
                  ·
                    refine ⟨3847194240056154324743161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5129592320074872432990881 3847194240056154324743161)
                    ·
                      refine ⟨2885395680042115743557371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3847194240056154324743161 2885395680042115743557371)
                      ·
                        rfl

theorem cell23_5619288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_5619288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619288 prefixEnd_5619288 := by exact prefixLift 5619288
  have htrace : WordTrace (prefixWord ++ tailWord_5619288) baseStart_5619288 baseEnd_5619288 := by
    simpa [prefixWord, tailWord_5619288, baseEnd_5619288] using wordTrace_append hprefix tailTrace_5619288
  have hstable : (prefixWord ++ tailWord_5619288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619288).length < 2 ^ (prefixWord ++ tailWord_5619288).sum := by decide
  have hdescent : baseEnd_5619288 < baseStart_5619288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619301 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 1, 2, 4]
def baseStart_5619301 : Nat := 118140960795 + 5619301 * 2 ^ 59
def prefixEnd_5619301 : Nat := 4983230072969 + 3 ^ 40 * 5619301 * 2
def baseEnd_5619301 : Nat := 2885402355290624192694811

theorem tailTrace_5619301 : CollatzResearch.WordTrace tailWord_5619301 prefixEnd_5619301 2885402355290624192694811 := by
  unfold tailWord_5619301
  simp only [CollatzResearch.WordTrace]
  refine ⟨204952745015239652050273757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136635163343493101366849171 204952745015239652050273757)
  ·
    refine ⟨76857279380714869518852659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204952745015239652050273757 76857279380714869518852659)
    ·
      refine ⟨115285919071072304278278989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76857279380714869518852659 115285919071072304278278989)
      ·
        refine ⟨43232219651652114104354621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115285919071072304278278989 43232219651652114104354621)
        ·
          refine ⟨16212082369369542789132983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43232219651652114104354621 16212082369369542789132983)
          ·
            refine ⟨24318123554054314183699475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16212082369369542789132983 24318123554054314183699475)
            ·
              refine ⟨36477185331081471275549213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24318123554054314183699475 36477185331081471275549213)
              ·
                refine ⟨13678944499155551728330955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36477185331081471275549213 13678944499155551728330955)
                ·
                  refine ⟨20518416748733327592496433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13678944499155551728330955 20518416748733327592496433)
                  ·
                    refine ⟨15388812561549995694372325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20518416748733327592496433 15388812561549995694372325)
                    ·
                      refine ⟨2885402355290624192694811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15388812561549995694372325 2885402355290624192694811)
                      ·
                        rfl

theorem cell23_5619301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_5619301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619301 prefixEnd_5619301 := by exact prefixLift 5619301
  have htrace : WordTrace (prefixWord ++ tailWord_5619301) baseStart_5619301 baseEnd_5619301 := by
    simpa [prefixWord, tailWord_5619301, baseEnd_5619301] using wordTrace_append hprefix tailTrace_5619301
  have hstable : (prefixWord ++ tailWord_5619301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619301).length < 2 ^ (prefixWord ++ tailWord_5619301).sum := by decide
  have hdescent : baseEnd_5619301 < baseStart_5619301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619318 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_5619318 : Nat := 118140960795 + 5619318 * 2 ^ 59
def prefixEnd_5619318 : Nat := 4983230072969 + 3 ^ 40 * 5619318 * 2
def baseEnd_5619318 : Nat := 2885411084461750626182233

theorem tailTrace_5619318 : CollatzResearch.WordTrace tailWord_5619318 prefixEnd_5619318 2885411084461750626182233 := by
  unfold tailWord_5619318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12809585316011128997102663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136635576704118709302428405 12809585316011128997102663)
  ·
    refine ⟨19214377974016693495653995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12809585316011128997102663 19214377974016693495653995)
    ·
      refine ⟨28821566961025040243480993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19214377974016693495653995 28821566961025040243480993)
      ·
        refine ⟨21616175220768780182610745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28821566961025040243480993 21616175220768780182610745)
        ·
          refine ⟨16212131415576585136958059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21616175220768780182610745 16212131415576585136958059)
          ·
            refine ⟨24318197123364877705437089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16212131415576585136958059 24318197123364877705437089)
            ·
              refine ⟨18238647842523658279077817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24318197123364877705437089 18238647842523658279077817)
              ·
                refine ⟨13678985881892743709308363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18238647842523658279077817 13678985881892743709308363)
                ·
                  refine ⟨20518478822839115563962545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13678985881892743709308363 20518478822839115563962545)
                  ·
                    refine ⟨15388859117129336672971909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20518478822839115563962545 15388859117129336672971909)
                    ·
                      refine ⟨2885411084461750626182233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15388859117129336672971909 2885411084461750626182233)
                      ·
                        rfl

theorem cell23_5619318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_5619318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619318 prefixEnd_5619318 := by exact prefixLift 5619318
  have htrace : WordTrace (prefixWord ++ tailWord_5619318) baseStart_5619318 baseEnd_5619318 := by
    simpa [prefixWord, tailWord_5619318, baseEnd_5619318] using wordTrace_append hprefix tailTrace_5619318
  have hstable : (prefixWord ++ tailWord_5619318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619318).length < 2 ^ (prefixWord ++ tailWord_5619318).sum := by decide
  have hdescent : baseEnd_5619318 < baseStart_5619318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619321 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 1, 3, 3]
def baseStart_5619321 : Nat := 118140960795 + 5619321 * 2 ^ 59
def prefixEnd_5619321 : Nat := 4983230072969 + 3 ^ 40 * 5619321 * 2
def baseEnd_5619321 : Nat := 2885412624903714114444719

theorem tailTrace_5619321 : CollatzResearch.WordTrace tailWord_5619321 prefixEnd_5619321 2885412624903714114444719 := by
  unfold tailWord_5619321
  simp only [CollatzResearch.WordTrace]
  refine ⟨204953474475167195466001817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136635649650111463644001211 204953474475167195466001817)
  ·
    refine ⟨153715105856375396599501363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204953474475167195466001817 153715105856375396599501363)
    ·
      refine ⟨230572658784563094899252045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153715105856375396599501363 230572658784563094899252045)
      ·
        refine ⟨86464747044211160587219517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230572658784563094899252045 86464747044211160587219517)
        ·
          refine ⟨32424280141579185220207319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86464747044211160587219517 32424280141579185220207319)
          ·
            refine ⟨48636420212368777830310979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32424280141579185220207319 48636420212368777830310979)
            ·
              refine ⟨72954630318553166745466469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48636420212368777830310979 72954630318553166745466469)
              ·
                refine ⟨13678993184728718764774963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72954630318553166745466469 13678993184728718764774963)
                ·
                  refine ⟨20518489777093078147162445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13678993184728718764774963 20518489777093078147162445)
                  ·
                    refine ⟨7694433666409904305185917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20518489777093078147162445 7694433666409904305185917)
                    ·
                      refine ⟨2885412624903714114444719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7694433666409904305185917 2885412624903714114444719)
                      ·
                        rfl

theorem cell23_5619321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_5619321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619321 prefixEnd_5619321 := by exact prefixLift 5619321
  have htrace : WordTrace (prefixWord ++ tailWord_5619321) baseStart_5619321 baseEnd_5619321 := by
    simpa [prefixWord, tailWord_5619321, baseEnd_5619321] using wordTrace_append hprefix tailTrace_5619321
  have hstable : (prefixWord ++ tailWord_5619321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619321).length < 2 ^ (prefixWord ++ tailWord_5619321).sum := by decide
  have hdescent : baseEnd_5619321 < baseStart_5619321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619325 : List Nat := [1, 4, 1, 1, 4, 1, 4, 1, 1, 2, 3]
def baseStart_5619325 : Nat := 118140960795 + 5619325 * 2 ^ 59
def prefixEnd_5619325 : Nat := 4983230072969 + 3 ^ 40 * 5619325 * 2
def baseEnd_5619325 : Nat := 2885414678826332098794701

theorem tailTrace_5619325 : CollatzResearch.WordTrace tailWord_5619325 prefixEnd_5619325 2885414678826332098794701 := by
  unfold tailWord_5619325
  simp only [CollatzResearch.WordTrace]
  refine ⟨204953620367152704149147429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136635746911435136099431619 204953620367152704149147429)
  ·
    refine ⟨38428803818841132027965143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204953620367152704149147429 38428803818841132027965143)
    ·
      refine ⟨57643205728261698041947715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38428803818841132027965143 57643205728261698041947715)
      ·
        refine ⟨86464808592392547062921573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57643205728261698041947715 86464808592392547062921573)
        ·
          refine ⟨16212151611073602574297795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86464808592392547062921573 16212151611073602574297795)
          ·
            refine ⟨24318227416610403861446693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16212151611073602574297795 24318227416610403861446693)
            ·
              refine ⟨4559667640614450724021255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24318227416610403861446693 4559667640614450724021255)
              ·
                refine ⟨6839501460921676086031883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4559667640614450724021255 6839501460921676086031883)
                ·
                  refine ⟨10259252191382514129047825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6839501460921676086031883 10259252191382514129047825)
                  ·
                    refine ⟨7694439143536885596785869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10259252191382514129047825 7694439143536885596785869)
                    ·
                      refine ⟨2885414678826332098794701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7694439143536885596785869 2885414678826332098794701)
                      ·
                        rfl

theorem cell23_5619325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_5619325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619325 prefixEnd_5619325 := by exact prefixLift 5619325
  have htrace : WordTrace (prefixWord ++ tailWord_5619325) baseStart_5619325 baseEnd_5619325 := by
    simpa [prefixWord, tailWord_5619325, baseEnd_5619325] using wordTrace_append hprefix tailTrace_5619325
  have hstable : (prefixWord ++ tailWord_5619325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619325).length < 2 ^ (prefixWord ++ tailWord_5619325).sum := by decide
  have hdescent : baseEnd_5619325 < baseStart_5619325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619332 : List Nat := [2, 3, 2, 1, 5, 1, 1, 2, 2, 4]
def baseStart_5619332 : Nat := 118140960795 + 5619332 * 2 ^ 59
def prefixEnd_5619332 : Nat := 4983230072969 + 3 ^ 40 * 5619332 * 2
def baseEnd_5619332 : Nat := 961806091063637857135723

theorem tailTrace_5619332 : CollatzResearch.WordTrace tailWord_5619332 prefixEnd_5619332 961806091063637857135723 := by
  unfold tailWord_5619332
  simp only [CollatzResearch.WordTrace]
  refine ⟨102476937839063672172326125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136635917118751562896434833 102476937839063672172326125)
  ·
    refine ⟨38428851689648877064622297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102476937839063672172326125 38428851689648877064622297)
    ·
      refine ⟨28821638767236657798466723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38428851689648877064622297 28821638767236657798466723)
      ·
        refine ⟨43232458150854986697700085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28821638767236657798466723 43232458150854986697700085)
        ·
          refine ⟨4053042951642655002909383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43232458150854986697700085 4053042951642655002909383)
          ·
            refine ⟨6079564427463982504364075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4053042951642655002909383 6079564427463982504364075)
            ·
              refine ⟨9119346641195973756546113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6079564427463982504364075 9119346641195973756546113)
              ·
                refine ⟨6839509980896980317409585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9119346641195973756546113 6839509980896980317409585)
                ·
                  refine ⟨5129632485672735238057189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6839509980896980317409585 5129632485672735238057189)
                  ·
                    refine ⟨961806091063637857135723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5129632485672735238057189 961806091063637857135723)
                    ·
                      rfl

theorem cell23_5619332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_5619332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619332 prefixEnd_5619332 := by exact prefixLift 5619332
  have htrace : WordTrace (prefixWord ++ tailWord_5619332) baseStart_5619332 baseEnd_5619332 := by
    simpa [prefixWord, tailWord_5619332, baseEnd_5619332] using wordTrace_append hprefix tailTrace_5619332
  have hstable : (prefixWord ++ tailWord_5619332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619332).length < 2 ^ (prefixWord ++ tailWord_5619332).sum := by decide
  have hdescent : baseEnd_5619332 < baseStart_5619332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619344 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 4]
def baseStart_5619344 : Nat := 118140960795 + 5619344 * 2 ^ 59
def prefixEnd_5619344 : Nat := 4983230072969 + 3 ^ 40 * 5619344 * 2
def baseEnd_5619344 : Nat := 2885424434958767524457113

theorem tailTrace_5619344 : CollatzResearch.WordTrace tailWord_5619344 prefixEnd_5619344 2885424434958767524457113 := by
  unfold tailWord_5619344
  simp only [CollatzResearch.WordTrace]
  refine ⟨102477156677041935197044543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136636208902722580262726057 102477156677041935197044543)
  ·
    refine ⟨153715735015562902795566815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102477156677041935197044543 153715735015562902795566815)
    ·
      refine ⟨230573602523344354193350223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153715735015562902795566815 230573602523344354193350223)
      ·
        refine ⟨345860403785016531290025335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230573602523344354193350223 345860403785016531290025335)
        ·
          refine ⟨518790605677524796935038003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345860403785016531290025335 518790605677524796935038003)
          ·
            refine ⟨778185908516287195402557005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518790605677524796935038003 778185908516287195402557005)
            ·
              refine ⟨291819715693607698275958877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 778185908516287195402557005 291819715693607698275958877)
              ·
                refine ⟨109432393385102886853484579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291819715693607698275958877 109432393385102886853484579)
                ·
                  refine ⟨164148590077654330280226869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109432393385102886853484579 164148590077654330280226869)
                  ·
                    refine ⟨15388930319780093463771269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 164148590077654330280226869 15388930319780093463771269)
                    ·
                      refine ⟨2885424434958767524457113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15388930319780093463771269 2885424434958767524457113)
                      ·
                        rfl

theorem cell23_5619344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_5619344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619344 prefixEnd_5619344 := by exact prefixLift 5619344
  have htrace : WordTrace (prefixWord ++ tailWord_5619344) baseStart_5619344 baseEnd_5619344 := by
    simpa [prefixWord, tailWord_5619344, baseEnd_5619344] using wordTrace_append hprefix tailTrace_5619344
  have hstable : (prefixWord ++ tailWord_5619344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619344).length < 2 ^ (prefixWord ++ tailWord_5619344).sum := by decide
  have hdescent : baseEnd_5619344 < baseStart_5619344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619362 : List Nat := [3, 3, 1, 4, 2, 1, 2, 7]
def baseStart_5619362 : Nat := 118140960795 + 5619362 * 2 ^ 59
def prefixEnd_5619362 : Nat := 4983230072969 + 3 ^ 40 * 5619362 * 2
def baseEnd_5619362 : Nat := 106867913985575868667853

theorem tailTrace_5619362 : CollatzResearch.WordTrace tailWord_5619362 prefixEnd_5619362 106867913985575868667853 := by
  unfold tailWord_5619362
  simp only [CollatzResearch.WordTrace]
  refine ⟨51238742467004664867061085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136636646578679106312162893 51238742467004664867061085)
  ·
    refine ⟨19214528425126749325147907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51238742467004664867061085 19214528425126749325147907)
    ·
      refine ⟨28821792637690123987721861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19214528425126749325147907 28821792637690123987721861)
      ·
        refine ⟨5404086119566898247697849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28821792637690123987721861 5404086119566898247697849)
        ·
          refine ⟨4053064589675173685773387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5404086119566898247697849 4053064589675173685773387)
          ·
            refine ⟨6079596884512760528660081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4053064589675173685773387 6079596884512760528660081)
            ·
              refine ⟨4559697663384570396495061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6079596884512760528660081 4559697663384570396495061)
              ·
                refine ⟨106867913985575868667853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4559697663384570396495061 106867913985575868667853)
                ·
                  rfl

theorem cell23_5619362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 7].length) (baseStart_5619362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619362 prefixEnd_5619362 := by exact prefixLift 5619362
  have htrace : WordTrace (prefixWord ++ tailWord_5619362) baseStart_5619362 baseEnd_5619362 := by
    simpa [prefixWord, tailWord_5619362, baseEnd_5619362] using wordTrace_append hprefix tailTrace_5619362
  have hstable : (prefixWord ++ tailWord_5619362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619362).length < 2 ^ (prefixWord ++ tailWord_5619362).sum := by decide
  have hdescent : baseEnd_5619362 < baseStart_5619362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619378 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2]
def baseStart_5619378 : Nat := 118140960795 + 5619378 * 2 ^ 59
def prefixEnd_5619378 : Nat := 4983230072969 + 3 ^ 40 * 5619378 * 2
def baseEnd_5619378 : Nat := 2885441893301020391431957

theorem tailTrace_5619378 : CollatzResearch.WordTrace tailWord_5619378 prefixEnd_5619378 2885441893301020391431957 := by
  unfold tailWord_5619378
  simp only [CollatzResearch.WordTrace]
  refine ⟨51238888358990173550206697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136637035623973796133884525 51238888358990173550206697)
  ·
    refine ⟨38429166269242630162655023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51238888358990173550206697 38429166269242630162655023)
    ·
      refine ⟨57643749403863945243982535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38429166269242630162655023 57643749403863945243982535)
      ·
        refine ⟨86465624105795917865973803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57643749403863945243982535 86465624105795917865973803)
        ·
          refine ⟨129698436158693876798960705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86465624105795917865973803 129698436158693876798960705)
          ·
            refine ⟨97273827119020407599220529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129698436158693876798960705 97273827119020407599220529)
            ·
              refine ⟨72955370339265305699415397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97273827119020407599220529 72955370339265305699415397)
              ·
                refine ⟨13679131938612244818640387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72955370339265305699415397 13679131938612244818640387)
                ·
                  refine ⟨20518697907918367227960581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13679131938612244818640387 20518697907918367227960581)
                  ·
                    refine ⟨3847255857734693855242609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20518697907918367227960581 3847255857734693855242609)
                    ·
                      refine ⟨2885441893301020391431957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3847255857734693855242609 2885441893301020391431957)
                      ·
                        rfl

theorem cell23_5619378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_5619378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619378 prefixEnd_5619378 := by exact prefixLift 5619378
  have htrace : WordTrace (prefixWord ++ tailWord_5619378) baseStart_5619378 baseEnd_5619378 := by
    simpa [prefixWord, tailWord_5619378, baseEnd_5619378] using wordTrace_append hprefix tailTrace_5619378
  have hstable : (prefixWord ++ tailWord_5619378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619378).length < 2 ^ (prefixWord ++ tailWord_5619378).sum := by decide
  have hdescent : baseEnd_5619378 < baseStart_5619378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619384 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 9]
def baseStart_5619384 : Nat := 118140960795 + 5619384 * 2 ^ 59
def prefixEnd_5619384 : Nat := 4983230072969 + 3 ^ 40 * 5619384 * 2
def baseEnd_5619384 : Nat := 320604997131660818661881

theorem tailTrace_5619384 : CollatzResearch.WordTrace tailWord_5619384 prefixEnd_5619384 320604997131660818661881 := by
  unfold tailWord_5619384
  simp only [CollatzResearch.WordTrace]
  refine ⟨102477886136969478612772603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136637181515959304817030137 102477886136969478612772603)
  ·
    refine ⟨153716829205454217919158905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102477886136969478612772603 153716829205454217919158905)
    ·
      refine ⟨115287621904090663439369179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153716829205454217919158905 115287621904090663439369179)
      ·
        refine ⟨172931432856135995159053769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115287621904090663439369179 172931432856135995159053769)
        ·
          refine ⟨129698574642101996369290327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172931432856135995159053769 129698574642101996369290327)
          ·
            refine ⟨194547861963152994553935491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129698574642101996369290327 194547861963152994553935491)
            ·
              refine ⟨291821792944729491830903237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194547861963152994553935491 291821792944729491830903237)
              ·
                refine ⟨54716586177136779718294357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 291821792944729491830903237 54716586177136779718294357)
                ·
                  refine ⟨320604997131660818661881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54716586177136779718294357 320604997131660818661881)
                  ·
                    rfl

theorem cell23_5619384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 9].length) (baseStart_5619384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619384 prefixEnd_5619384 := by exact prefixLift 5619384
  have htrace : WordTrace (prefixWord ++ tailWord_5619384) baseStart_5619384 baseEnd_5619384 := by
    simpa [prefixWord, tailWord_5619384, baseEnd_5619384] using wordTrace_append hprefix tailTrace_5619384
  have hstable : (prefixWord ++ tailWord_5619384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619384).length < 2 ^ (prefixWord ++ tailWord_5619384).sum := by decide
  have hdescent : baseEnd_5619384 < baseStart_5619384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619441 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 1, 2, 5]
def baseStart_5619441 : Nat := 118140960795 + 5619441 * 2 ^ 59
def prefixEnd_5619441 : Nat := 4983230072969 + 3 ^ 40 * 5619441 * 2
def baseEnd_5619441 : Nat := 2885474242582253644944167

theorem tailTrace_5619441 : CollatzResearch.WordTrace tailWord_5619441 prefixEnd_5619441 2885474242582253644944167 := by
  unfold tailWord_5619441
  simp only [CollatzResearch.WordTrace]
  refine ⟨204957851234732455960370177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136638567489821637306913451 204957851234732455960370177)
  ·
    refine ⟨153718388426049341970277633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204957851234732455960370177 153718388426049341970277633)
    ·
      refine ⟨115288791319537006477708225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153718388426049341970277633 115288791319537006477708225)
      ·
        refine ⟨86466593489652754858281169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115288791319537006477708225 86466593489652754858281169)
        ·
          refine ⟨64849945117239566143710877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86466593489652754858281169 64849945117239566143710877)
          ·
            refine ⟨24318729418964837303891579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64849945117239566143710877 24318729418964837303891579)
            ·
              refine ⟨36478094128447255955837369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24318729418964837303891579 36478094128447255955837369)
              ·
                refine ⟨27358570596335441966878027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36478094128447255955837369 27358570596335441966878027)
                ·
                  refine ⟨41037855894503162950317041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27358570596335441966878027 41037855894503162950317041)
                  ·
                    refine ⟨30778391920877372212737781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41037855894503162950317041 30778391920877372212737781)
                    ·
                      refine ⟨2885474242582253644944167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30778391920877372212737781 2885474242582253644944167)
                      ·
                        rfl

theorem cell23_5619441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_5619441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619441 prefixEnd_5619441 := by exact prefixLift 5619441
  have htrace : WordTrace (prefixWord ++ tailWord_5619441) baseStart_5619441 baseEnd_5619441 := by
    simpa [prefixWord, tailWord_5619441, baseEnd_5619441] using wordTrace_append hprefix tailTrace_5619441
  have hstable : (prefixWord ++ tailWord_5619441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619441).length < 2 ^ (prefixWord ++ tailWord_5619441).sum := by decide
  have hdescent : baseEnd_5619441 < baseStart_5619441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619451 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 4]
def baseStart_5619451 : Nat := 118140960795 + 5619451 * 2 ^ 59
def prefixEnd_5619451 : Nat := 4983230072969 + 3 ^ 40 * 5619451 * 2
def baseEnd_5619451 : Nat := 2885479377388798605819121

theorem tailTrace_5619451 : CollatzResearch.WordTrace tailWord_5619451 prefixEnd_5619451 2885479377388798605819121 := by
  unfold tailWord_5619451
  simp only [CollatzResearch.WordTrace]
  refine ⟨204958215964696227668234207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136638810643130818445489471 204958215964696227668234207)
  ·
    refine ⟨307437323947044341502351311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204958215964696227668234207 307437323947044341502351311)
    ·
      refine ⟨461155985920566512253526967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307437323947044341502351311 461155985920566512253526967)
      ·
        refine ⟨691733978880849768380290451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461155985920566512253526967 691733978880849768380290451)
        ·
          refine ⟨1037600968321274652570435677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691733978880849768380290451 1037600968321274652570435677)
          ·
            refine ⟨389100363120477994713913379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1037600968321274652570435677 389100363120477994713913379)
            ·
              refine ⟨583650544680716992070870069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389100363120477994713913379 583650544680716992070870069)
              ·
                refine ⟨54717238563817218006644069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 583650544680716992070870069 54717238563817218006644069)
                ·
                  refine ⟨10259482230715728376245763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54717238563817218006644069 10259482230715728376245763)
                  ·
                    refine ⟨15389223346073592564368645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10259482230715728376245763 15389223346073592564368645)
                    ·
                      refine ⟨2885479377388798605819121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15389223346073592564368645 2885479377388798605819121)
                      ·
                        rfl

theorem cell23_5619451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 4].length) (baseStart_5619451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619451 prefixEnd_5619451 := by exact prefixLift 5619451
  have htrace : WordTrace (prefixWord ++ tailWord_5619451) baseStart_5619451 baseEnd_5619451 := by
    simpa [prefixWord, tailWord_5619451, baseEnd_5619451] using wordTrace_append hprefix tailTrace_5619451
  have hstable : (prefixWord ++ tailWord_5619451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619451).length < 2 ^ (prefixWord ++ tailWord_5619451).sum := by decide
  have hdescent : baseEnd_5619451 < baseStart_5619451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619458 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_5619458 : Nat := 118140960795 + 5619458 * 2 ^ 59
def prefixEnd_5619458 : Nat := 4983230072969 + 3 ^ 40 * 5619458 * 2
def baseEnd_5619458 : Nat := 2885482971753380078431589

theorem tailTrace_5619458 : CollatzResearch.WordTrace tailWord_5619458 prefixEnd_5619458 2885482971753380078431589 := by
  unfold tailWord_5619458
  simp only [CollatzResearch.WordTrace]
  refine ⟨51239617818917716965934757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136638980850447245242492685 51239617818917716965934757)
  ·
    refine ⟨9607428341047071931112767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51239617818917716965934757 9607428341047071931112767)
    ·
      refine ⟨14411142511570607896669151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9607428341047071931112767 14411142511570607896669151)
      ·
        refine ⟨21616713767355911845003727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14411142511570607896669151 21616713767355911845003727)
        ·
          refine ⟨32425070651033867767505591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21616713767355911845003727 32425070651033867767505591)
          ·
            refine ⟨48637605976550801651258387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32425070651033867767505591 48637605976550801651258387)
            ·
              refine ⟨72956408964826202476887581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48637605976550801651258387 72956408964826202476887581)
              ·
                refine ⟨27358653361809825928832843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72956408964826202476887581 27358653361809825928832843)
                ·
                  refine ⟨41037980042714738893249265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27358653361809825928832843 41037980042714738893249265)
                  ·
                    refine ⟨30778485032036054169936949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41037980042714738893249265 30778485032036054169936949)
                    ·
                      refine ⟨2885482971753380078431589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30778485032036054169936949 2885482971753380078431589)
                      ·
                        rfl

theorem cell23_5619458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_5619458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619458 prefixEnd_5619458 := by exact prefixLift 5619458
  have htrace : WordTrace (prefixWord ++ tailWord_5619458) baseStart_5619458 baseEnd_5619458 := by
    simpa [prefixWord, tailWord_5619458, baseEnd_5619458] using wordTrace_append hprefix tailTrace_5619458
  have hstable : (prefixWord ++ tailWord_5619458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619458).length < 2 ^ (prefixWord ++ tailWord_5619458).sum := by decide
  have hdescent : baseEnd_5619458 < baseStart_5619458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619468 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 1, 6, 2]
def baseStart_5619468 : Nat := 118140960795 + 5619468 * 2 ^ 59
def prefixEnd_5619468 : Nat := 4983230072969 + 3 ^ 40 * 5619468 * 2
def baseEnd_5619468 : Nat := 2885488106559925039306543

theorem tailTrace_5619468 : CollatzResearch.WordTrace tailWord_5619468 prefixEnd_5619468 2885488106559925039306543 := by
  unfold tailWord_5619468
  simp only [CollatzResearch.WordTrace]
  refine ⟨102479418002817319785801529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136639224003756426381068705 102479418002817319785801529)
  ·
    refine ⟨76859563502112989839351147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102479418002817319785801529 76859563502112989839351147)
    ·
      refine ⟨115289345253169484759026721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76859563502112989839351147 115289345253169484759026721)
      ·
        refine ⟨86467008939877113569270041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115289345253169484759026721 86467008939877113569270041)
        ·
          refine ⟨64850256704907835176952531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86467008939877113569270041 64850256704907835176952531)
          ·
            refine ⟨97275385057361752765428797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64850256704907835176952531 97275385057361752765428797)
            ·
              refine ⟨36478269396510657287035799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97275385057361752765428797 36478269396510657287035799)
              ·
                refine ⟨54717404094765985930553699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36478269396510657287035799 54717404094765985930553699)
                ·
                  refine ⟨82076106142148978895830549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54717404094765985930553699 82076106142148978895830549)
                  ·
                    refine ⟨3847317475413233385742057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82076106142148978895830549 3847317475413233385742057)
                    ·
                      refine ⟨2885488106559925039306543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3847317475413233385742057 2885488106559925039306543)
                      ·
                        rfl

theorem cell23_5619468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_5619468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619468 prefixEnd_5619468 := by exact prefixLift 5619468
  have htrace : WordTrace (prefixWord ++ tailWord_5619468) baseStart_5619468 baseEnd_5619468 := by
    simpa [prefixWord, tailWord_5619468, baseEnd_5619468] using wordTrace_append hprefix tailTrace_5619468
  have hstable : (prefixWord ++ tailWord_5619468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619468).length < 2 ^ (prefixWord ++ tailWord_5619468).sum := by decide
  have hdescent : baseEnd_5619468 < baseStart_5619468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619469 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 7]
def baseStart_5619469 : Nat := 118140960795 + 5619469 * 2 ^ 59
def prefixEnd_5619469 : Nat := 4983230072969 + 3 ^ 40 * 5619469 * 2
def baseEnd_5619469 : Nat := 320609846671175503932671

theorem tailTrace_5619469 : CollatzResearch.WordTrace tailWord_5619469 prefixEnd_5619469 320609846671175503932671 := by
  unfold tailWord_5619469
  simp only [CollatzResearch.WordTrace]
  refine ⟨204958872478631016742389461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136639248319087344494926307 204958872478631016742389461)
  ·
    refine ⟨4803723573717914454899753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 204958872478631016742389461 4803723573717914454899753)
    ·
      refine ⟨3602792680288435841174815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4803723573717914454899753 3602792680288435841174815)
      ·
        refine ⟨5404189020432653761762223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3602792680288435841174815 5404189020432653761762223)
        ·
          refine ⟨8106283530648980642643335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5404189020432653761762223 8106283530648980642643335)
          ·
            refine ⟨12159425295973470963965003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8106283530648980642643335 12159425295973470963965003)
            ·
              refine ⟨18239137943960206445947505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12159425295973470963965003 18239137943960206445947505)
              ·
                refine ⟨13679353457970154834460629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18239137943960206445947505 13679353457970154834460629)
                ·
                  refine ⟨320609846671175503932671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13679353457970154834460629 320609846671175503932671)
                  ·
                    rfl

theorem cell23_5619469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_5619469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619469 prefixEnd_5619469 := by exact prefixLift 5619469
  have htrace : WordTrace (prefixWord ++ tailWord_5619469) baseStart_5619469 baseEnd_5619469 := by
    simpa [prefixWord, tailWord_5619469, baseEnd_5619469] using wordTrace_append hprefix tailTrace_5619469
  have hstable : (prefixWord ++ tailWord_5619469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619469).length < 2 ^ (prefixWord ++ tailWord_5619469).sum := by decide
  have hdescent : baseEnd_5619469 < baseStart_5619469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619488 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 3]
def baseStart_5619488 : Nat := 118140960795 + 5619488 * 2 ^ 59
def prefixEnd_5619488 : Nat := 4983230072969 + 3 ^ 40 * 5619488 * 2
def baseEnd_5619488 : Nat := 2885498376173014961056451

theorem tailTrace_5619488 : CollatzResearch.WordTrace tailWord_5619488 prefixEnd_5619488 2885498376173014961056451 := by
  unfold tailWord_5619488
  simp only [CollatzResearch.WordTrace]
  refine ⟨102479782732781091493665559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136639710310374788658220745 102479782732781091493665559)
  ·
    refine ⟨153719674099171637240498339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102479782732781091493665559 153719674099171637240498339)
    ·
      refine ⟨230579511148757455860747509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153719674099171637240498339 230579511148757455860747509)
      ·
        refine ⟨21616829170196011486945079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 230579511148757455860747509 21616829170196011486945079)
        ·
          refine ⟨32425243755294017230417619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21616829170196011486945079 32425243755294017230417619)
          ·
            refine ⟨48637865632941025845626429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32425243755294017230417619 48637865632941025845626429)
            ·
              refine ⟨18239199612352884692109911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48637865632941025845626429 18239199612352884692109911)
              ·
                refine ⟨27358799418529327038164867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18239199612352884692109911 27358799418529327038164867)
                ·
                  refine ⟨41038199127793990557247301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27358799418529327038164867 41038199127793990557247301)
                  ·
                    refine ⟨7694662336461373229483869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41038199127793990557247301 7694662336461373229483869)
                    ·
                      refine ⟨2885498376173014961056451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7694662336461373229483869 2885498376173014961056451)
                      ·
                        rfl

theorem cell23_5619488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_5619488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619488 prefixEnd_5619488 := by exact prefixLift 5619488
  have htrace : WordTrace (prefixWord ++ tailWord_5619488) baseStart_5619488 baseEnd_5619488 := by
    simpa [prefixWord, tailWord_5619488, baseEnd_5619488] using wordTrace_append hprefix tailTrace_5619488
  have hstable : (prefixWord ++ tailWord_5619488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619488).length < 2 ^ (prefixWord ++ tailWord_5619488).sum := by decide
  have hdescent : baseEnd_5619488 < baseStart_5619488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619545 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 2, 3, 2]
def baseStart_5619545 : Nat := 118140960795 + 5619545 * 2 ^ 59
def prefixEnd_5619545 : Nat := 4983230072969 + 3 ^ 40 * 5619545 * 2
def baseEnd_5619545 : Nat := 2885527644570321238043689

theorem tailTrace_5619545 : CollatzResearch.WordTrace tailWord_5619545 prefixEnd_5619545 2885527644570321238043689 := by
  unfold tailWord_5619545
  simp only [CollatzResearch.WordTrace]
  refine ⟨204961644426355681722156089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136641096284237121148104059 204961644426355681722156089)
  ·
    refine ⟨153721233319766761291617067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204961644426355681722156089 153721233319766761291617067)
    ·
      refine ⟨230581849979650141937425601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153721233319766761291617067 230581849979650141937425601)
      ·
        refine ⟨172936387484737606453069201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230581849979650141937425601 172936387484737606453069201)
        ·
          refine ⟨129702290613553204839801901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172936387484737606453069201 129702290613553204839801901)
          ·
            refine ⟨48638358980082451814925713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129702290613553204839801901 48638358980082451814925713)
            ·
              refine ⟨36478769235061838861194285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48638358980082451814925713 36478769235061838861194285)
              ·
                refine ⟨13679538463148189572947857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36478769235061838861194285 13679538463148189572947857)
                ·
                  refine ⟨10259653847361142179710893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13679538463148189572947857 10259653847361142179710893)
                  ·
                    refine ⟨3847370192760428317391585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10259653847361142179710893 3847370192760428317391585)
                    ·
                      refine ⟨2885527644570321238043689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3847370192760428317391585 2885527644570321238043689)
                      ·
                        rfl

theorem cell23_5619545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 3, 2].length) (baseStart_5619545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619545 prefixEnd_5619545 := by exact prefixLift 5619545
  have htrace : WordTrace (prefixWord ++ tailWord_5619545) baseStart_5619545 baseEnd_5619545 := by
    simpa [prefixWord, tailWord_5619545, baseEnd_5619545] using wordTrace_append hprefix tailTrace_5619545
  have hstable : (prefixWord ++ tailWord_5619545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619545).length < 2 ^ (prefixWord ++ tailWord_5619545).sum := by decide
  have hdescent : baseEnd_5619545 < baseStart_5619545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619569 : List Nat := [1, 2, 2, 2, 1, 3, 5, 2, 1, 1, 3]
def baseStart_5619569 : Nat := 118140960795 + 5619569 * 2 ^ 59
def prefixEnd_5619569 : Nat := 4983230072969 + 3 ^ 40 * 5619569 * 2
def baseEnd_5619569 : Nat := 2885539968106029144143579

theorem tailTrace_5619569 : CollatzResearch.WordTrace tailWord_5619569 prefixEnd_5619569 2885539968106029144143579 := by
  unfold tailWord_5619569
  simp only [CollatzResearch.WordTrace]
  refine ⟨204962519778268733821029761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136641679852179155880686507 204962519778268733821029761)
  ·
    refine ⟨153721889833701550365772321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204962519778268733821029761 153721889833701550365772321)
    ·
      refine ⟨115291417375276162774329241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153721889833701550365772321 115291417375276162774329241)
      ·
        refine ⟨86468563031457122080746931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115291417375276162774329241 86468563031457122080746931)
        ·
          refine ⟨129702844547185683121120397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86468563031457122080746931 129702844547185683121120397)
          ·
            refine ⟨48638566705194631170420149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129702844547185683121120397 48638566705194631170420149)
            ·
              refine ⟨4559865628611996672226889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48638566705194631170420149 4559865628611996672226889)
              ·
                refine ⟨3419899221458997504170167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4559865628611996672226889 3419899221458997504170167)
                ·
                  refine ⟨5129848832188496256255251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3419899221458997504170167 5129848832188496256255251)
                  ·
                    refine ⟨7694773248282744384382877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5129848832188496256255251 7694773248282744384382877)
                    ·
                      refine ⟨2885539968106029144143579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7694773248282744384382877 2885539968106029144143579)
                      ·
                        rfl

theorem cell23_5619569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_5619569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619569 prefixEnd_5619569 := by exact prefixLift 5619569
  have htrace : WordTrace (prefixWord ++ tailWord_5619569) baseStart_5619569 baseEnd_5619569 := by
    simpa [prefixWord, tailWord_5619569, baseEnd_5619569] using wordTrace_append hprefix tailTrace_5619569
  have hstable : (prefixWord ++ tailWord_5619569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619569).length < 2 ^ (prefixWord ++ tailWord_5619569).sum := by decide
  have hdescent : baseEnd_5619569 < baseStart_5619569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619578 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5]
def baseStart_5619578 : Nat := 118140960795 + 5619578 * 2 ^ 59
def prefixEnd_5619578 : Nat := 4983230072969 + 3 ^ 40 * 5619578 * 2
def baseEnd_5619578 : Nat := 2885544589431919608931037

theorem tailTrace_5619578 : CollatzResearch.WordTrace tailWord_5619578 prefixEnd_5619578 2885544589431919608931037 := by
  unfold tailWord_5619578
  simp only [CollatzResearch.WordTrace]
  refine ⟨51240712008809032089526847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136641898690157418905404925 51240712008809032089526847)
  ·
    refine ⟨76861068013213548134290271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51240712008809032089526847 76861068013213548134290271)
    ·
      refine ⟨115291602019820322201435407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76861068013213548134290271 115291602019820322201435407)
      ·
        refine ⟨172937403029730483302153111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115291602019820322201435407 172937403029730483302153111)
        ·
          refine ⟨259406104544595724953229667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172937403029730483302153111 259406104544595724953229667)
          ·
            refine ⟨389109156816893587429844501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259406104544595724953229667 389109156816893587429844501)
            ·
              refine ⟨18239491725791886910773961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 389109156816893587429844501 18239491725791886910773961)
              ·
                refine ⟨13679618794343915183080471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18239491725791886910773961 13679618794343915183080471)
                ·
                  refine ⟨20519428191515872774620707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13679618794343915183080471 20519428191515872774620707)
                  ·
                    refine ⟨30779142287273809161931061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20519428191515872774620707 30779142287273809161931061)
                    ·
                      refine ⟨2885544589431919608931037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30779142287273809161931061 2885544589431919608931037)
                      ·
                        rfl

theorem cell23_5619578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_5619578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619578 prefixEnd_5619578 := by exact prefixLift 5619578
  have htrace : WordTrace (prefixWord ++ tailWord_5619578) baseStart_5619578 baseEnd_5619578 := by
    simpa [prefixWord, tailWord_5619578, baseEnd_5619578] using wordTrace_append hprefix tailTrace_5619578
  have hstable : (prefixWord ++ tailWord_5619578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619578).length < 2 ^ (prefixWord ++ tailWord_5619578).sum := by decide
  have hdescent : baseEnd_5619578 < baseStart_5619578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619588 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_5619588 : Nat := 118140960795 + 5619588 * 2 ^ 59
def prefixEnd_5619588 : Nat := 4983230072969 + 3 ^ 40 * 5619588 * 2
def baseEnd_5619588 : Nat := 2885549724238464569805991

theorem tailTrace_5619588 : CollatzResearch.WordTrace tailWord_5619588 prefixEnd_5619588 2885549724238464569805991 := by
  unfold tailWord_5619588
  simp only [CollatzResearch.WordTrace]
  refine ⟨102481606382599950032985709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136642141843466600043980945 102481606382599950032985709)
  ·
    refine ⟨38430602393474981262369641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102481606382599950032985709 38430602393474981262369641)
    ·
      refine ⟨28822951795106235946777231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38430602393474981262369641 28822951795106235946777231)
      ·
        refine ⟨43234427692659353920165847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28822951795106235946777231 43234427692659353920165847)
        ·
          refine ⟨64851641538989030880248771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43234427692659353920165847 64851641538989030880248771)
          ·
            refine ⟨97277462308483546320373157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64851641538989030880248771 97277462308483546320373157)
            ·
              refine ⟨18239524182840664935069967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97277462308483546320373157 18239524182840664935069967)
              ·
                refine ⟨27359286274260997402604951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18239524182840664935069967 27359286274260997402604951)
                ·
                  refine ⟨41038929411391496103907427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27359286274260997402604951 41038929411391496103907427)
                  ·
                    refine ⟨61558394117087244155861141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41038929411391496103907427 61558394117087244155861141)
                    ·
                      refine ⟨2885549724238464569805991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61558394117087244155861141 2885549724238464569805991)
                      ·
                        rfl

theorem cell23_5619588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_5619588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619588 prefixEnd_5619588 := by exact prefixLift 5619588
  have htrace : WordTrace (prefixWord ++ tailWord_5619588) baseStart_5619588 baseEnd_5619588 := by
    simpa [prefixWord, tailWord_5619588, baseEnd_5619588] using wordTrace_append hprefix tailTrace_5619588
  have hstable : (prefixWord ++ tailWord_5619588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619588).length < 2 ^ (prefixWord ++ tailWord_5619588).sum := by decide
  have hdescent : baseEnd_5619588 < baseStart_5619588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619612 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_5619612 : Nat := 118140960795 + 5619612 * 2 ^ 59
def prefixEnd_5619612 : Nat := 4983230072969 + 3 ^ 40 * 5619612 * 2
def baseEnd_5619612 : Nat := 2885562047774172475905881

theorem tailTrace_5619612 : CollatzResearch.WordTrace tailWord_5619612 prefixEnd_5619612 2885562047774172475905881 := by
  unfold tailWord_5619612
  simp only [CollatzResearch.WordTrace]
  refine ⟨102482044058556476082422545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136642725411408634776563393 102482044058556476082422545)
  ·
    refine ⟨76861533043917357061816909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102482044058556476082422545 76861533043917357061816909)
    ·
      refine ⟨28823074891469008898181341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76861533043917357061816909 28823074891469008898181341)
      ·
        refine ⟨10808653084300878336818003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28823074891469008898181341 10808653084300878336818003)
        ·
          refine ⟨16212979626451317505227005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10808653084300878336818003 16212979626451317505227005)
          ·
            refine ⟨6079867359919244064460127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16212979626451317505227005 6079867359919244064460127)
            ·
              refine ⟨9119801039878866096690191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6079867359919244064460127 9119801039878866096690191)
              ·
                refine ⟨13679701559818299145035287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9119801039878866096690191 13679701559818299145035287)
                ·
                  refine ⟨20519552339727448717552931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13679701559818299145035287 20519552339727448717552931)
                  ·
                    refine ⟨30779328509591173076329397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20519552339727448717552931 30779328509591173076329397)
                    ·
                      refine ⟨2885562047774172475905881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30779328509591173076329397 2885562047774172475905881)
                      ·
                        rfl

theorem cell23_5619612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_5619612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619612 prefixEnd_5619612 := by exact prefixLift 5619612
  have htrace : WordTrace (prefixWord ++ tailWord_5619612) baseStart_5619612 baseEnd_5619612 := by
    simpa [prefixWord, tailWord_5619612, baseEnd_5619612] using wordTrace_append hprefix tailTrace_5619612
  have hstable : (prefixWord ++ tailWord_5619612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619612).length < 2 ^ (prefixWord ++ tailWord_5619612).sum := by decide
  have hdescent : baseEnd_5619612 < baseStart_5619612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619635 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 5, 3, 2]
def baseStart_5619635 : Nat := 118140960795 + 5619635 * 2 ^ 59
def prefixEnd_5619635 : Nat := 4983230072969 + 3 ^ 40 * 5619635 * 2
def baseEnd_5619635 : Nat := 2885573857829225885918275

theorem tailTrace_5619635 : CollatzResearch.WordTrace tailWord_5619635 prefixEnd_5619635 2885573857829225885918275 := by
  unfold tailWord_5619635
  simp only [CollatzResearch.WordTrace]
  refine ⟨204964926996029627092932359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136643284664019751395288239 204964926996029627092932359)
  ·
    refine ⟨307447390494044440639398539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204964926996029627092932359 307447390494044440639398539)
    ·
      refine ⟨461171085741066660959097809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307447390494044440639398539 461171085741066660959097809)
      ·
        refine ⟨345878314305799995719323357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461171085741066660959097809 345878314305799995719323357)
        ·
          refine ⟨129704367864674998394746259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345878314305799995719323357 129704367864674998394746259)
          ·
            refine ⟨194556551797012497592119389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129704367864674998394746259 194556551797012497592119389)
            ·
              refine ⟨72958706923879686597044771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194556551797012497592119389 72958706923879686597044771)
              ·
                refine ⟨109438060385819529895567157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72958706923879686597044771 109438060385819529895567157)
                ·
                  refine ⟨10259818161170580927709421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109438060385819529895567157 10259818161170580927709421)
                  ·
                    refine ⟨3847431810438967847891033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10259818161170580927709421 3847431810438967847891033)
                    ·
                      refine ⟨2885573857829225885918275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3847431810438967847891033 2885573857829225885918275)
                      ·
                        rfl

theorem cell23_5619635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 3, 2].length) (baseStart_5619635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619635 prefixEnd_5619635 := by exact prefixLift 5619635
  have htrace : WordTrace (prefixWord ++ tailWord_5619635) baseStart_5619635 baseEnd_5619635 := by
    simpa [prefixWord, tailWord_5619635, baseEnd_5619635] using wordTrace_append hprefix tailTrace_5619635
  have hstable : (prefixWord ++ tailWord_5619635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619635).length < 2 ^ (prefixWord ++ tailWord_5619635).sum := by decide
  have hdescent : baseEnd_5619635 < baseStart_5619635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619648 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 4]
def baseStart_5619648 : Nat := 118140960795 + 5619648 * 2 ^ 59
def prefixEnd_5619648 : Nat := 4983230072969 + 3 ^ 40 * 5619648 * 2
def baseEnd_5619648 : Nat := 2885580533077734335055715

theorem tailTrace_5619648 : CollatzResearch.WordTrace tailWord_5619648 prefixEnd_5619648 2885580533077734335055715 := by
  unfold tailWord_5619648
  simp only [CollatzResearch.WordTrace]
  refine ⟨102482700572491265156577799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136643600763321686875437065 102482700572491265156577799)
  ·
    refine ⟨153724050858736897734866699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102482700572491265156577799 153724050858736897734866699)
    ·
      refine ⟨230586076288105346602300049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153724050858736897734866699 230586076288105346602300049)
      ·
        refine ⟨172939557216079009951725037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230586076288105346602300049 172939557216079009951725037)
        ·
          refine ⟨64852333956029628731896889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172939557216079009951725037 64852333956029628731896889)
          ·
            refine ⟨48639250467022221548922667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64852333956029628731896889 48639250467022221548922667)
            ·
              refine ⟨72958875700533332323384001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48639250467022221548922667 72958875700533332323384001)
              ·
                refine ⟨54719156775399999242538001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72958875700533332323384001 54719156775399999242538001)
                ·
                  refine ⟨41039367581549999431903501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54719156775399999242538001 41039367581549999431903501)
                  ·
                    refine ⟨15389762843081249786963813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41039367581549999431903501 15389762843081249786963813)
                    ·
                      refine ⟨2885580533077734335055715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15389762843081249786963813 2885580533077734335055715)
                      ·
                        rfl

theorem cell23_5619648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_5619648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619648 prefixEnd_5619648 := by exact prefixLift 5619648
  have htrace : WordTrace (prefixWord ++ tailWord_5619648) baseStart_5619648 baseEnd_5619648 := by
    simpa [prefixWord, tailWord_5619648, baseEnd_5619648] using wordTrace_append hprefix tailTrace_5619648
  have hstable : (prefixWord ++ tailWord_5619648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619648).length < 2 ^ (prefixWord ++ tailWord_5619648).sum := by decide
  have hdescent : baseEnd_5619648 < baseStart_5619648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619665 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 3, 4, 2]
def baseStart_5619665 : Nat := 118140960795 + 5619665 * 2 ^ 59
def prefixEnd_5619665 : Nat := 4983230072969 + 3 ^ 40 * 5619665 * 2
def baseEnd_5619665 : Nat := 2885589262248860768543137

theorem tailTrace_5619665 : CollatzResearch.WordTrace tailWord_5619665 prefixEnd_5619665 2885589262248860768543137 := by
  unfold tailWord_5619665
  simp only [CollatzResearch.WordTrace]
  refine ⟨204966021185920942216524449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136644014123947294811016299 204966021185920942216524449)
  ·
    refine ⟨153724515889440706662393337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204966021185920942216524449 153724515889440706662393337)
    ·
      refine ⟨115293386917080529996795003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153724515889440706662393337 115293386917080529996795003)
      ·
        refine ⟨172940080375620794995192505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115293386917080529996795003 172940080375620794995192505)
        ·
          refine ⟨129705060281715596246394379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172940080375620794995192505 129705060281715596246394379)
          ·
            refine ⟨194557590422573394369591569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129705060281715596246394379 194557590422573394369591569)
            ·
              refine ⟨145918192816930045777193677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194557590422573394369591569 145918192816930045777193677)
              ·
                refine ⟨54719322306348767166447629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145918192816930045777193677 54719322306348767166447629)
                ·
                  refine ⟨20519745864880787687417861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54719322306348767166447629 20519745864880787687417861)
                  ·
                    refine ⟨3847452349665147691390849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20519745864880787687417861 3847452349665147691390849)
                    ·
                      refine ⟨2885589262248860768543137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3847452349665147691390849 2885589262248860768543137)
                      ·
                        rfl

theorem cell23_5619665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 4, 2].length) (baseStart_5619665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619665 prefixEnd_5619665 := by exact prefixLift 5619665
  have htrace : WordTrace (prefixWord ++ tailWord_5619665) baseStart_5619665 baseEnd_5619665 := by
    simpa [prefixWord, tailWord_5619665, baseEnd_5619665] using wordTrace_append hprefix tailTrace_5619665
  have hstable : (prefixWord ++ tailWord_5619665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619665).length < 2 ^ (prefixWord ++ tailWord_5619665).sum := by decide
  have hdescent : baseEnd_5619665 < baseStart_5619665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619669 : List Nat := [1, 3, 2, 3, 2, 2, 1, 3, 1, 3, 2]
def baseStart_5619669 : Nat := 118140960795 + 5619669 * 2 ^ 59
def prefixEnd_5619669 : Nat := 4983230072969 + 3 ^ 40 * 5619669 * 2
def baseEnd_5619669 : Nat := 2885591316171478752893119

theorem tailTrace_5619669 : CollatzResearch.WordTrace tailWord_5619669 prefixEnd_5619669 2885591316171478752893119 := by
  unfold tailWord_5619669
  simp only [CollatzResearch.WordTrace]
  refine ⟨204966167077906450899670061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136644111385270967266446707 204966167077906450899670061)
  ·
    refine ⟨76862312654214919087376273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204966167077906450899670061 76862312654214919087376273)
    ·
      refine ⟨57646734490661189315532205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76862312654214919087376273 57646734490661189315532205)
      ·
        refine ⟨21617525433997945993324577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57646734490661189315532205 21617525433997945993324577)
        ·
          refine ⟨16213144075498459494993433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21617525433997945993324577 16213144075498459494993433)
          ·
            refine ⟨12159858056623844621245075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16213144075498459494993433 12159858056623844621245075)
            ·
              refine ⟨18239787084935766931867613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12159858056623844621245075 18239787084935766931867613)
              ·
                refine ⟨6839920156850912599450355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18239787084935766931867613 6839920156850912599450355)
                ·
                  refine ⟨10259880235276368899175533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6839920156850912599450355 10259880235276368899175533)
                  ·
                    refine ⟨3847455088228638337190825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10259880235276368899175533 3847455088228638337190825)
                    ·
                      refine ⟨2885591316171478752893119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3847455088228638337190825 2885591316171478752893119)
                      ·
                        rfl

theorem cell23_5619669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_5619669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619669 prefixEnd_5619669 := by exact prefixLift 5619669
  have htrace : WordTrace (prefixWord ++ tailWord_5619669) baseStart_5619669 baseEnd_5619669 := by
    simpa [prefixWord, tailWord_5619669, baseEnd_5619669] using wordTrace_append hprefix tailTrace_5619669
  have hstable : (prefixWord ++ tailWord_5619669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619669).length < 2 ^ (prefixWord ++ tailWord_5619669).sum := by decide
  have hdescent : baseEnd_5619669 < baseStart_5619669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619693 : List Nat := [1, 5, 1, 4, 1, 1, 3, 1, 2, 1, 3]
def baseStart_5619693 : Nat := 118140960795 + 5619693 * 2 ^ 59
def prefixEnd_5619693 : Nat := 4983230072969 + 3 ^ 40 * 5619693 * 2
def baseEnd_5619693 : Nat := 2885603639707186658993009

theorem tailTrace_5619693 : CollatzResearch.WordTrace tailWord_5619693 prefixEnd_5619693 2885603639707186658993009 := by
  unfold tailWord_5619693
  simp only [CollatzResearch.WordTrace]
  refine ⟨204967042429819502998543733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136644694953213001999029155 204967042429819502998543733)
  ·
    refine ⟨19215660227795578406113475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204967042429819502998543733 19215660227795578406113475)
    ·
      refine ⟨28823490341693367609170213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19215660227795578406113475 28823490341693367609170213)
      ·
        refine ⟨5404404439067506426719415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28823490341693367609170213 5404404439067506426719415)
        ·
          refine ⟨8106606658601259640079123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5404404439067506426719415 8106606658601259640079123)
          ·
            refine ⟨12159909987901889460118685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8106606658601259640079123 12159909987901889460118685)
            ·
              refine ⟨4559966245463208547544507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12159909987901889460118685 4559966245463208547544507)
              ·
                refine ⟨6839949368194812821316761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4559966245463208547544507 6839949368194812821316761)
                ·
                  refine ⟨5129962026146109615987571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6839949368194812821316761 5129962026146109615987571)
                  ·
                    refine ⟨7694943039219164423981357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5129962026146109615987571 7694943039219164423981357)
                    ·
                      refine ⟨2885603639707186658993009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7694943039219164423981357 2885603639707186658993009)
                      ·
                        rfl

theorem cell23_5619693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_5619693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619693 prefixEnd_5619693 := by exact prefixLift 5619693
  have htrace : WordTrace (prefixWord ++ tailWord_5619693) baseStart_5619693 baseEnd_5619693 := by
    simpa [prefixWord, tailWord_5619693, baseEnd_5619693] using wordTrace_append hprefix tailTrace_5619693
  have hstable : (prefixWord ++ tailWord_5619693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619693).length < 2 ^ (prefixWord ++ tailWord_5619693).sum := by decide
  have hdescent : baseEnd_5619693 < baseStart_5619693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619728 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 5]
def baseStart_5619728 : Nat := 118140960795 + 5619728 * 2 ^ 59
def prefixEnd_5619728 : Nat := 4983230072969 + 3 ^ 40 * 5619728 * 2
def baseEnd_5619728 : Nat := 2885621611530094022055347

theorem tailTrace_5619728 : CollatzResearch.WordTrace tailWord_5619728 prefixEnd_5619728 2885621611530094022055347 := by
  unfold tailWord_5619728
  simp only [CollatzResearch.WordTrace]
  refine ⟨102484159492346351988033919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136645545989795135984045225 102484159492346351988033919)
  ·
    refine ⟨153726239238519527982050879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102484159492346351988033919 153726239238519527982050879)
    ·
      refine ⟨230589358857779291973076319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153726239238519527982050879 230589358857779291973076319)
      ·
        refine ⟨345884038286668937959614479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230589358857779291973076319 345884038286668937959614479)
        ·
          refine ⟨518826057430003406939421719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345884038286668937959614479 518826057430003406939421719)
          ·
            refine ⟨778239086145005110409132579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518826057430003406939421719 778239086145005110409132579)
            ·
              refine ⟨1167358629217507665613698869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778239086145005110409132579 1167358629217507665613698869)
              ·
                refine ⟨109439871489141343651284269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1167358629217507665613698869 109439871489141343651284269)
                ·
                  refine ⟨41039951808428003869231601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109439871489141343651284269 41039951808428003869231601)
                  ·
                    refine ⟨30779963856321002901923701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41039951808428003869231601 30779963856321002901923701)
                    ·
                      refine ⟨2885621611530094022055347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30779963856321002901923701 2885621611530094022055347)
                      ·
                        rfl

theorem cell23_5619728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_5619728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619728 prefixEnd_5619728 := by exact prefixLift 5619728
  have htrace : WordTrace (prefixWord ++ tailWord_5619728) baseStart_5619728 baseEnd_5619728 := by
    simpa [prefixWord, tailWord_5619728, baseEnd_5619728] using wordTrace_append hprefix tailTrace_5619728
  have hstable : (prefixWord ++ tailWord_5619728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619728).length < 2 ^ (prefixWord ++ tailWord_5619728).sum := by decide
  have hdescent : baseEnd_5619728 < baseStart_5619728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619772 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 2, 1, 4]
def baseStart_5619772 : Nat := 118140960795 + 5619772 * 2 ^ 59
def prefixEnd_5619772 : Nat := 4983230072969 + 3 ^ 40 * 5619772 * 2
def baseEnd_5619772 : Nat := 2885644204678891849905145

theorem tailTrace_5619772 : CollatzResearch.WordTrace tailWord_5619772 prefixEnd_5619772 2885644204678891849905145 := by
  unfold tailWord_5619772
  simp only [CollatzResearch.WordTrace]
  refine ⟨102484961898266649745334785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136646615864355532993779713 102484961898266649745334785)
  ·
    refine ⟨76863721423699987309001089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102484961898266649745334785 76863721423699987309001089)
    ·
      refine ⟨57647791067774990481750817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76863721423699987309001089 57647791067774990481750817)
      ·
        refine ⟨43235843300831242861313113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57647791067774990481750817 43235843300831242861313113)
        ·
          refine ⟨32426882475623432145984835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43235843300831242861313113 32426882475623432145984835)
          ·
            refine ⟨48640323713435148218977253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32426882475623432145984835 48640323713435148218977253)
            ·
              refine ⟨9120060696269090291058235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48640323713435148218977253 9120060696269090291058235)
              ·
                refine ⟨13680091044403635436587353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9120060696269090291058235 13680091044403635436587353)
                ·
                  refine ⟨10260068283302726577440515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13680091044403635436587353 10260068283302726577440515)
                  ·
                    refine ⟨15390102424954089866160773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10260068283302726577440515 15390102424954089866160773)
                    ·
                      refine ⟨2885644204678891849905145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15390102424954089866160773 2885644204678891849905145)
                      ·
                        rfl

theorem cell23_5619772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_5619772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619772 prefixEnd_5619772 := by exact prefixLift 5619772
  have htrace : WordTrace (prefixWord ++ tailWord_5619772) baseStart_5619772 baseEnd_5619772 := by
    simpa [prefixWord, tailWord_5619772, baseEnd_5619772] using wordTrace_append hprefix tailTrace_5619772
  have hstable : (prefixWord ++ tailWord_5619772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619772).length < 2 ^ (prefixWord ++ tailWord_5619772).sum := by decide
  have hdescent : baseEnd_5619772 < baseStart_5619772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619775 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 3]
def baseStart_5619775 : Nat := 118140960795 + 5619775 * 2 ^ 59
def prefixEnd_5619775 : Nat := 4983230072969 + 3 ^ 40 * 5619775 * 2
def baseEnd_5619775 : Nat := 2885645745120855338167631

theorem tailTrace_5619775 : CollatzResearch.WordTrace tailWord_5619775 prefixEnd_5619775 2885645745120855338167631 := by
  unfold tailWord_5619775
  simp only [CollatzResearch.WordTrace]
  refine ⟨204970033215522431003028779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136646688810348287335352519 204970033215522431003028779)
  ·
    refine ⟨307455049823283646504543169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204970033215522431003028779 307455049823283646504543169)
    ·
      refine ⟨230591287367462734878407377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307455049823283646504543169 230591287367462734878407377)
      ·
        refine ⟨172943465525597051158805533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230591287367462734878407377 172943465525597051158805533)
        ·
          refine ⟨64853799572098894184552075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172943465525597051158805533 64853799572098894184552075)
          ·
            refine ⟨97280699358148341276828113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64853799572098894184552075 97280699358148341276828113)
            ·
              refine ⟨72960524518611255957621085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97280699358148341276828113 72960524518611255957621085)
              ·
                refine ⟨27360196694479220984107907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72960524518611255957621085 27360196694479220984107907)
                ·
                  refine ⟨41040295041718831476161861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27360196694479220984107907 41040295041718831476161861)
                  ·
                    refine ⟨7695055320322280901780349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41040295041718831476161861 7695055320322280901780349)
                    ·
                      refine ⟨2885645745120855338167631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7695055320322280901780349 2885645745120855338167631)
                      ·
                        rfl

theorem cell23_5619775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_5619775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619775 prefixEnd_5619775 := by exact prefixLift 5619775
  have htrace : WordTrace (prefixWord ++ tailWord_5619775) baseStart_5619775 baseEnd_5619775 := by
    simpa [prefixWord, tailWord_5619775, baseEnd_5619775] using wordTrace_append hprefix tailTrace_5619775
  have hstable : (prefixWord ++ tailWord_5619775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619775).length < 2 ^ (prefixWord ++ tailWord_5619775).sum := by decide
  have hdescent : baseEnd_5619775 < baseStart_5619775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619789 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_5619789 : Nat := 118140960795 + 5619789 * 2 ^ 59
def prefixEnd_5619789 : Nat := 4983230072969 + 3 ^ 40 * 5619789 * 2
def baseEnd_5619789 : Nat := 2885652933850018283392567

theorem tailTrace_5619789 : CollatzResearch.WordTrace tailWord_5619789 prefixEnd_5619789 2885652933850018283392567 := by
  unfold tailWord_5619789
  simp only [CollatzResearch.WordTrace]
  refine ⟨204970543837471711394038421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136647029224981140929358947 204970543837471711394038421)
  ·
    refine ⟨9607994242381486471595551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 204970543837471711394038421 9607994242381486471595551)
    ·
      refine ⟨14411991363572229707393327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9607994242381486471595551 14411991363572229707393327)
      ·
        refine ⟨21617987045358344561089991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14411991363572229707393327 21617987045358344561089991)
        ·
          refine ⟨32426980568037516841634987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21617987045358344561089991 32426980568037516841634987)
          ·
            refine ⟨48640470852056275262452481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32426980568037516841634987 48640470852056275262452481)
            ·
              refine ⟨36480353139042206446839361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48640470852056275262452481 36480353139042206446839361)
              ·
                refine ⟨27360264854281654835129521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36480353139042206446839361 27360264854281654835129521)
                ·
                  refine ⟨20520198640711241126347141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27360264854281654835129521 20520198640711241126347141)
                  ·
                    refine ⟨3847537245133357711190089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20520198640711241126347141 3847537245133357711190089)
                    ·
                      refine ⟨2885652933850018283392567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3847537245133357711190089 2885652933850018283392567)
                      ·
                        rfl

theorem cell23_5619789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_5619789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619789 prefixEnd_5619789 := by exact prefixLift 5619789
  have htrace : WordTrace (prefixWord ++ tailWord_5619789) baseStart_5619789 baseEnd_5619789 := by
    simpa [prefixWord, tailWord_5619789, baseEnd_5619789] using wordTrace_append hprefix tailTrace_5619789
  have hstable : (prefixWord ++ tailWord_5619789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619789).length < 2 ^ (prefixWord ++ tailWord_5619789).sum := by decide
  have hdescent : baseEnd_5619789 < baseStart_5619789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619825 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 3, 5]
def baseStart_5619825 : Nat := 118140960795 + 5619825 * 2 ^ 59
def prefixEnd_5619825 : Nat := 4983230072969 + 3 ^ 40 * 5619825 * 2
def baseEnd_5619825 : Nat := 961890473051193380847467

theorem tailTrace_5619825 : CollatzResearch.WordTrace tailWord_5619825 prefixEnd_5619825 961890473051193380847467 := by
  unfold tailWord_5619825
  simp only [CollatzResearch.WordTrace]
  refine ⟨204971856865341289542348929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136647904576894193028232619 204971856865341289542348929)
  ·
    refine ⟨153728892649005967156761697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204971856865341289542348929 153728892649005967156761697)
    ·
      refine ⟨115296669486754475367571273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153728892649005967156761697 115296669486754475367571273)
      ·
        refine ⟨86472502115065856525678455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115296669486754475367571273 86472502115065856525678455)
        ·
          refine ⟨129708753172598784788517683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86472502115065856525678455 129708753172598784788517683)
          ·
            refine ⟨194563129758898177182776525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129708753172598784788517683 194563129758898177182776525)
            ·
              refine ⟨72961173659586816443541197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194563129758898177182776525 72961173659586816443541197)
              ·
                refine ⟨27360440122345056166327949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72961173659586816443541197 27360440122345056166327949)
                ·
                  refine ⟨10260165045879396062372981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27360440122345056166327949 10260165045879396062372981)
                  ·
                    refine ⟨961890473051193380847467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10260165045879396062372981 961890473051193380847467)
                    ·
                      rfl

theorem cell23_5619825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_5619825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619825 prefixEnd_5619825 := by exact prefixLift 5619825
  have htrace : WordTrace (prefixWord ++ tailWord_5619825) baseStart_5619825 baseEnd_5619825 := by
    simpa [prefixWord, tailWord_5619825, baseEnd_5619825] using wordTrace_append hprefix tailTrace_5619825
  have hstable : (prefixWord ++ tailWord_5619825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619825).length < 2 ^ (prefixWord ++ tailWord_5619825).sum := by decide
  have hdescent : baseEnd_5619825 < baseStart_5619825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619872 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 1, 6]
def baseStart_5619872 : Nat := 118140960795 + 5619872 * 2 ^ 59
def prefixEnd_5619872 : Nat := 4983230072969 + 3 ^ 40 * 5619872 * 2
def baseEnd_5619872 : Nat := 961898517581447152884895

theorem tailTrace_5619872 : CollatzResearch.WordTrace tailWord_5619872 prefixEnd_5619872 961898517581447152884895 := by
  unfold tailWord_5619872
  simp only [CollatzResearch.WordTrace]
  refine ⟨102486785548085508284654935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136649047397447344379539913 102486785548085508284654935)
  ·
    refine ⟨153730178322128262426982403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102486785548085508284654935 153730178322128262426982403)
    ·
      refine ⟨230595267483192393640473605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153730178322128262426982403 230595267483192393640473605)
      ·
        refine ⟨43236612653098573807588801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230595267483192393640473605 43236612653098573807588801)
        ·
          refine ⟨32427459489823930355691601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43236612653098573807588801 32427459489823930355691601)
          ·
            refine ⟨24320594617367947766768701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32427459489823930355691601 24320594617367947766768701)
            ·
              refine ⟨9120222981512980412538263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24320594617367947766768701 9120222981512980412538263)
              ·
                refine ⟨13680334472269470618807395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9120222981512980412538263 13680334472269470618807395)
                ·
                  refine ⟨20520501708404205928211093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13680334472269470618807395 20520501708404205928211093)
                  ·
                    refine ⟨961898517581447152884895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20520501708404205928211093 961898517581447152884895)
                    ·
                      rfl

theorem cell23_5619872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 1, 6].length) (baseStart_5619872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619872 prefixEnd_5619872 := by exact prefixLift 5619872
  have htrace : WordTrace (prefixWord ++ tailWord_5619872) baseStart_5619872 baseEnd_5619872 := by
    simpa [prefixWord, tailWord_5619872, baseEnd_5619872] using wordTrace_append hprefix tailTrace_5619872
  have hstable : (prefixWord ++ tailWord_5619872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619872).length < 2 ^ (prefixWord ++ tailWord_5619872).sum := by decide
  have hdescent : baseEnd_5619872 < baseStart_5619872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619915 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 2, 7]
def baseStart_5619915 : Nat := 118140960795 + 5619915 * 2 ^ 59
def prefixEnd_5619915 : Nat := 4983230072969 + 3 ^ 40 * 5619915 * 2
def baseEnd_5619915 : Nat := 961905877470828263472329

theorem tailTrace_5619915 : CollatzResearch.WordTrace tailWord_5619915 prefixEnd_5619915 961905877470828263472329 := by
  unfold tailWord_5619915
  simp only [CollatzResearch.WordTrace]
  refine ⟨204975139435015234913125199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136650092956676823275416799 204975139435015234913125199)
  ·
    refine ⟨307462709152522852369687799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204975139435015234913125199 307462709152522852369687799)
    ·
      refine ⟨461194063728784278554531699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307462709152522852369687799 461194063728784278554531699)
      ·
        refine ⟨691791095593176417831797549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461194063728784278554531699 691791095593176417831797549)
        ·
          refine ⟨259421660847441156686924081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 691791095593176417831797549 259421660847441156686924081)
          ·
            refine ⟨194566245635580867515193061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259421660847441156686924081 194566245635580867515193061)
            ·
              refine ⟨36481171056671412659098699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194566245635580867515193061 36481171056671412659098699)
              ·
                refine ⟨54721756585007118988648049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36481171056671412659098699 54721756585007118988648049)
                ·
                  refine ⟨41041317438755339241486037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54721756585007118988648049 41041317438755339241486037)
                  ·
                    refine ⟨961905877470828263472329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41041317438755339241486037 961905877470828263472329)
                    ·
                      rfl

theorem cell23_5619915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 7].length) (baseStart_5619915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619915 prefixEnd_5619915 := by exact prefixLift 5619915
  have htrace : WordTrace (prefixWord ++ tailWord_5619915) baseStart_5619915 baseEnd_5619915 := by
    simpa [prefixWord, tailWord_5619915, baseEnd_5619915] using wordTrace_append hprefix tailTrace_5619915
  have hstable : (prefixWord ++ tailWord_5619915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619915).length < 2 ^ (prefixWord ++ tailWord_5619915).sum := by decide
  have hdescent : baseEnd_5619915 < baseStart_5619915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619933 : List Nat := [1, 4, 3, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_5619933 : Nat := 118140960795 + 5619933 * 2 ^ 59
def prefixEnd_5619933 : Nat := 4983230072969 + 3 ^ 40 * 5619933 * 2
def baseEnd_5619933 : Nat := 2885726875064265719991905

theorem tailTrace_5619933 : CollatzResearch.WordTrace tailWord_5619933 prefixEnd_5619933 2885726875064265719991905 := by
  unfold tailWord_5619933
  simp only [CollatzResearch.WordTrace]
  refine ⟨204975795948950023987280453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136650530632633349324853635 204975795948950023987280453)
  ·
    refine ⟨38432961740428129497615085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204975795948950023987280453 38432961740428129497615085)
    ·
      refine ⟨14412360652660548561605657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38432961740428129497615085 14412360652660548561605657)
      ·
        refine ⟨10809270489495411421204243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14412360652660548561605657 10809270489495411421204243)
        ·
          refine ⟨16213905734243117131806365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10809270489495411421204243 16213905734243117131806365)
          ·
            refine ⟨6080214650341168924427387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16213905734243117131806365 6080214650341168924427387)
            ·
              refine ⟨9120321975511753386641081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6080214650341168924427387 9120321975511753386641081)
              ·
                refine ⟨6840241481633815039980811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9120321975511753386641081 6840241481633815039980811)
                ·
                  refine ⟨10260362222450722559971217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6840241481633815039980811 10260362222450722559971217)
                  ·
                    refine ⟨7695271666838041919978413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10260362222450722559971217 7695271666838041919978413)
                    ·
                      refine ⟨2885726875064265719991905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7695271666838041919978413 2885726875064265719991905)
                      ·
                        rfl

theorem cell23_5619933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_5619933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619933 prefixEnd_5619933 := by exact prefixLift 5619933
  have htrace : WordTrace (prefixWord ++ tailWord_5619933) baseStart_5619933 baseEnd_5619933 := by
    simpa [prefixWord, tailWord_5619933, baseEnd_5619933] using wordTrace_append hprefix tailTrace_5619933
  have hstable : (prefixWord ++ tailWord_5619933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619933).length < 2 ^ (prefixWord ++ tailWord_5619933).sum := by decide
  have hdescent : baseEnd_5619933 < baseStart_5619933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619935 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 8]
def baseStart_5619935 : Nat := 118140960795 + 5619935 * 2 ^ 59
def prefixEnd_5619935 : Nat := 4983230072969 + 3 ^ 40 * 5619935 * 2
def baseEnd_5619935 : Nat := 2885727902025574712166895

theorem tailTrace_5619935 : CollatzResearch.WordTrace tailWord_5619935 prefixEnd_5619935 2885727902025574712166895 := by
  unfold tailWord_5619935
  simp only [CollatzResearch.WordTrace]
  refine ⟨204975868894942778328853259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136650579263295185552568839 204975868894942778328853259)
  ·
    refine ⟨307463803342414167493279889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204975868894942778328853259 307463803342414167493279889)
    ·
      refine ⟨230597852506810625619959917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307463803342414167493279889 230597852506810625619959917)
      ·
        refine ⟨86474194690053984607484969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230597852506810625619959917 86474194690053984607484969)
        ·
          refine ⟨64855646017540488455613727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86474194690053984607484969 64855646017540488455613727)
          ·
            refine ⟨97283469026310732683420591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64855646017540488455613727 97283469026310732683420591)
            ·
              refine ⟨145925203539466099025130887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97283469026310732683420591 145925203539466099025130887)
              ·
                refine ⟨218887805309199148537696331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145925203539466099025130887 218887805309199148537696331)
                ·
                  refine ⟨328331707963798722806544497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218887805309199148537696331 328331707963798722806544497)
                  ·
                    refine ⟨246248780972849042104908373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 328331707963798722806544497 246248780972849042104908373)
                    ·
                      refine ⟨2885727902025574712166895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 246248780972849042104908373 2885727902025574712166895)
                      ·
                        rfl

theorem cell23_5619935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_5619935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619935 prefixEnd_5619935 := by exact prefixLift 5619935
  have htrace : WordTrace (prefixWord ++ tailWord_5619935) baseStart_5619935 baseEnd_5619935 := by
    simpa [prefixWord, tailWord_5619935, baseEnd_5619935] using wordTrace_append hprefix tailTrace_5619935
  have hstable : (prefixWord ++ tailWord_5619935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619935).length < 2 ^ (prefixWord ++ tailWord_5619935).sum := by decide
  have hdescent : baseEnd_5619935 < baseStart_5619935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619945 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 1, 8]
def baseStart_5619945 : Nat := 118140960795 + 5619945 * 2 ^ 59
def prefixEnd_5619945 : Nat := 4983230072969 + 3 ^ 40 * 5619945 * 2
def baseEnd_5619945 : Nat := 961911012277373224347283

theorem tailTrace_5619945 : CollatzResearch.WordTrace tailWord_5619945 prefixEnd_5619945 961911012277373224347283 := by
  unfold tailWord_5619945
  simp only [CollatzResearch.WordTrace]
  refine ⟨204976233624906550036717289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136650822416604366691144859 204976233624906550036717289)
  ·
    refine ⟨153732175218679912527537967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204976233624906550036717289 153732175218679912527537967)
    ·
      refine ⟨230598262828019868791306951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153732175218679912527537967 230598262828019868791306951)
      ·
        refine ⟨345897394242029803186960427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230598262828019868791306951 345897394242029803186960427)
        ·
          refine ⟨518846091363044704780440641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345897394242029803186960427 518846091363044704780440641)
          ·
            refine ⟨389134568522283528585330481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 518846091363044704780440641 389134568522283528585330481)
            ·
              refine ⟨291850926391712646438997861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389134568522283528585330481 291850926391712646438997861)
              ·
                refine ⟨54722048698446121207312099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 291850926391712646438997861 54722048698446121207312099)
                ·
                  refine ⟨82083073047669181810968149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54722048698446121207312099 82083073047669181810968149)
                  ·
                    refine ⟨961911012277373224347283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82083073047669181810968149 961911012277373224347283)
                    ·
                      rfl

theorem cell23_5619945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 8].length) (baseStart_5619945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619945 prefixEnd_5619945 := by exact prefixLift 5619945
  have htrace : WordTrace (prefixWord ++ tailWord_5619945) baseStart_5619945 baseEnd_5619945 := by
    simpa [prefixWord, tailWord_5619945, baseEnd_5619945] using wordTrace_append hprefix tailTrace_5619945
  have hstable : (prefixWord ++ tailWord_5619945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619945).length < 2 ^ (prefixWord ++ tailWord_5619945).sum := by decide
  have hdescent : baseEnd_5619945 < baseStart_5619945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619969 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 3, 4, 2]
def baseStart_5619969 : Nat := 118140960795 + 5619969 * 2 ^ 59
def prefixEnd_5619969 : Nat := 4983230072969 + 3 ^ 40 * 5619969 * 2
def baseEnd_5619969 : Nat := 2885745360367827579141739

theorem tailTrace_5619969 : CollatzResearch.WordTrace tailWord_5619969 prefixEnd_5619969 2885745360367827579141739 := by
  unfold tailWord_5619969
  simp only [CollatzResearch.WordTrace]
  refine ⟨204977108976819602135590961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136651405984546401423727307 204977108976819602135590961)
  ·
    refine ⟨153732831732614701601693221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204977108976819602135590961 153732831732614701601693221)
    ·
      refine ⟨28824905949865256550317479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153732831732614701601693221 28824905949865256550317479)
      ·
        refine ⟨43237358924797884825476219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28824905949865256550317479 43237358924797884825476219)
        ·
          refine ⟨64856038387196827238214329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43237358924797884825476219 64856038387196827238214329)
          ·
            refine ⟨48642028790397620428660747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64856038387196827238214329 48642028790397620428660747)
            ·
              refine ⟨72963043185596430642991121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48642028790397620428660747 72963043185596430642991121)
              ·
                refine ⟨54722282389197322982243341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72963043185596430642991121 54722282389197322982243341)
                ·
                  refine ⟨20520855895948996118341253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54722282389197322982243341 20520855895948996118341253)
                  ·
                    refine ⟨3847660480490436772188985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20520855895948996118341253 3847660480490436772188985)
                    ·
                      refine ⟨2885745360367827579141739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3847660480490436772188985 2885745360367827579141739)
                      ·
                        rfl

theorem cell23_5619969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_5619969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619969 prefixEnd_5619969 := by exact prefixLift 5619969
  have htrace : WordTrace (prefixWord ++ tailWord_5619969) baseStart_5619969 baseEnd_5619969 := by
    simpa [prefixWord, tailWord_5619969, baseEnd_5619969] using wordTrace_append hprefix tailTrace_5619969
  have hstable : (prefixWord ++ tailWord_5619969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619969).length < 2 ^ (prefixWord ++ tailWord_5619969).sum := by decide
  have hdescent : baseEnd_5619969 < baseStart_5619969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5619992 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 7]
def baseStart_5619992 : Nat := 118140960795 + 5619992 * 2 ^ 59
def prefixEnd_5619992 : Nat := 4983230072969 + 3 ^ 40 * 5619992 * 2
def baseEnd_5619992 : Nat := 320639685602542332128237

theorem tailTrace_5619992 : CollatzResearch.WordTrace tailWord_5619992 prefixEnd_5619992 320639685602542332128237 := by
  unfold tailWord_5619992
  simp only [CollatzResearch.WordTrace]
  refine ⟨102488973927868138531839115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136651965237157518042452153 102488973927868138531839115)
  ·
    refine ⟨153733460891802207797758673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102488973927868138531839115 153733460891802207797758673)
    ·
      refine ⟨115300095668851655848319005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153733460891802207797758673 115300095668851655848319005)
      ·
        refine ⟨43237535875819370943119627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115300095668851655848319005 43237535875819370943119627)
        ·
          refine ⟨64856303813729056414679441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43237535875819370943119627 64856303813729056414679441)
          ·
            refine ⟨48642227860296792311009581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64856303813729056414679441 48642227860296792311009581)
            ·
              refine ⟨18240835447611297116628593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48642227860296792311009581 18240835447611297116628593)
              ·
                refine ⟨13680626585708472837471445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18240835447611297116628593 13680626585708472837471445)
                ·
                  refine ⟨320639685602542332128237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13680626585708472837471445 320639685602542332128237)
                  ·
                    rfl

theorem cell23_5619992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 7].length) (baseStart_5619992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5619992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5619992 prefixEnd_5619992 := by exact prefixLift 5619992
  have htrace : WordTrace (prefixWord ++ tailWord_5619992) baseStart_5619992 baseEnd_5619992 := by
    simpa [prefixWord, tailWord_5619992, baseEnd_5619992] using wordTrace_append hprefix tailTrace_5619992
  have hstable : (prefixWord ++ tailWord_5619992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5619992).length < 2 ^ (prefixWord ++ tailWord_5619992).sum := by decide
  have hdescent : baseEnd_5619992 < baseStart_5619992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5619992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620007 : List Nat := [1, 1, 8, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_5620007 : Nat := 118140960795 + 5620007 * 2 ^ 59
def prefixEnd_5620007 : Nat := 4983230072969 + 3 ^ 40 * 5620007 * 2
def baseEnd_5620007 : Nat := 2885764872632698430466565

theorem tailTrace_5620007 : CollatzResearch.WordTrace tailWord_5620007 prefixEnd_5620007 2885764872632698430466565 := by
  unfold tailWord_5620007
  simp only [CollatzResearch.WordTrace]
  refine ⟨204978494950681934625474275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136652329967121289750316183 204978494950681934625474275)
  ·
    refine ⟨307467742426022901938211413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204978494950681934625474275 307467742426022901938211413)
    ·
      refine ⟨3603137606554955882088415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 307467742426022901938211413 3603137606554955882088415)
      ·
        refine ⟨5404706409832433823132623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3603137606554955882088415 5404706409832433823132623)
        ·
          refine ⟨8107059614748650734698935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5404706409832433823132623 8107059614748650734698935)
          ·
            refine ⟨12160589422122976102048403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8107059614748650734698935 12160589422122976102048403)
            ·
              refine ⟨18240884133184464153072605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12160589422122976102048403 18240884133184464153072605)
              ·
                refine ⟨6840331549944174057402227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18240884133184464153072605 6840331549944174057402227)
                ·
                  refine ⟨10260497324916261086103341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6840331549944174057402227 10260497324916261086103341)
                  ·
                    refine ⟨3847686496843597907288753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10260497324916261086103341 3847686496843597907288753)
                    ·
                      refine ⟨2885764872632698430466565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3847686496843597907288753 2885764872632698430466565)
                      ·
                        rfl

theorem cell23_5620007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_5620007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620007 prefixEnd_5620007 := by exact prefixLift 5620007
  have htrace : WordTrace (prefixWord ++ tailWord_5620007) baseStart_5620007 baseEnd_5620007 := by
    simpa [prefixWord, tailWord_5620007, baseEnd_5620007] using wordTrace_append hprefix tailTrace_5620007
  have hstable : (prefixWord ++ tailWord_5620007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620007).length < 2 ^ (prefixWord ++ tailWord_5620007).sum := by decide
  have hdescent : baseEnd_5620007 < baseStart_5620007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620020 : List Nat := [2, 5, 1, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_5620020 : Nat := 118140960795 + 5620020 * 2 ^ 59
def prefixEnd_5620020 : Nat := 4983230072969 + 3 ^ 40 * 5620020 * 2
def baseEnd_5620020 : Nat := 2885771547881206879604005

theorem tailTrace_5620020 : CollatzResearch.WordTrace tailWord_5620020 prefixEnd_5620020 2885771547881206879604005 := by
  unfold tailWord_5620020
  simp only [CollatzResearch.WordTrace]
  refine ⟨102489484549817418922848757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136652646066423225230465009 102489484549817418922848757)
  ·
    refine ⟨9608389176545383024017071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102489484549817418922848757 9608389176545383024017071)
    ·
      refine ⟨14412583764818074536025607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9608389176545383024017071 14412583764818074536025607)
      ·
        refine ⟨21618875647227111804038411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14412583764818074536025607 21618875647227111804038411)
        ·
          refine ⟨32428313470840667706057617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21618875647227111804038411 32428313470840667706057617)
          ·
            refine ⟨24321235103130500779543213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32428313470840667706057617 24321235103130500779543213)
            ·
              refine ⟨9120463163673937792328705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24321235103130500779543213 9120463163673937792328705)
              ·
                refine ⟨6840347372755453344246529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9120463163673937792328705 6840347372755453344246529)
                ·
                  refine ⟨5130260529566590008184897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6840347372755453344246529 5130260529566590008184897)
                  ·
                    refine ⟨3847695397174942506138673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5130260529566590008184897 3847695397174942506138673)
                    ·
                      refine ⟨2885771547881206879604005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3847695397174942506138673 2885771547881206879604005)
                      ·
                        rfl

theorem cell23_5620020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_5620020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620020 prefixEnd_5620020 := by exact prefixLift 5620020
  have htrace : WordTrace (prefixWord ++ tailWord_5620020) baseStart_5620020 baseEnd_5620020 := by
    simpa [prefixWord, tailWord_5620020, baseEnd_5620020] using wordTrace_append hprefix tailTrace_5620020
  have hstable : (prefixWord ++ tailWord_5620020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620020).length < 2 ^ (prefixWord ++ tailWord_5620020).sum := by decide
  have hdescent : baseEnd_5620020 < baseStart_5620020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620060 : List Nat := [2, 2, 4, 3, 1, 2, 1, 3, 5]
def baseStart_5620060 : Nat := 118140960795 + 5620060 * 2 ^ 59
def prefixEnd_5620060 : Nat := 4983230072969 + 3 ^ 40 * 5620060 * 2
def baseEnd_5620060 : Nat := 320643565234154080344869

theorem tailTrace_5620060 : CollatzResearch.WordTrace tailWord_5620060 prefixEnd_5620060 320643565234154080344869 := by
  unfold tailWord_5620060
  simp only [CollatzResearch.WordTrace]
  refine ⟨102490214009744962338576817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136653618679659949784769089 102490214009744962338576817)
  ·
    refine ⟨76867660507308721753932613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102490214009744962338576817 76867660507308721753932613)
    ·
      refine ⟨14412686345120385328862365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76867660507308721753932613 14412686345120385328862365)
      ·
        refine ⟨5404757379420144498323387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14412686345120385328862365 5404757379420144498323387)
        ·
          refine ⟨8107136069130216747485081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5404757379420144498323387 8107136069130216747485081)
          ·
            refine ⟨6080352051847662560613811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8107136069130216747485081 6080352051847662560613811)
            ·
              refine ⟨9120528077771493840920717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6080352051847662560613811 9120528077771493840920717)
              ·
                refine ⟨3420198029164310190345269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9120528077771493840920717 3420198029164310190345269)
                ·
                  refine ⟨320643565234154080344869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3420198029164310190345269 320643565234154080344869)
                  ·
                    rfl

theorem cell23_5620060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 5].length) (baseStart_5620060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620060 prefixEnd_5620060 := by exact prefixLift 5620060
  have htrace : WordTrace (prefixWord ++ tailWord_5620060) baseStart_5620060 baseEnd_5620060 := by
    simpa [prefixWord, tailWord_5620060, baseEnd_5620060] using wordTrace_append hprefix tailTrace_5620060
  have hstable : (prefixWord ++ tailWord_5620060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620060).length < 2 ^ (prefixWord ++ tailWord_5620060).sum := by decide
  have hdescent : baseEnd_5620060 < baseStart_5620060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620076 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 4]
def baseStart_5620076 : Nat := 118140960795 + 5620076 * 2 ^ 59
def prefixEnd_5620076 : Nat := 4983230072969 + 3 ^ 40 * 5620076 * 2
def baseEnd_5620076 : Nat := 2885800302797858660503747

theorem tailTrace_5620076 : CollatzResearch.WordTrace tailWord_5620076 prefixEnd_5620076 2885800302797858660503747 := by
  unfold tailWord_5620076
  simp only [CollatzResearch.WordTrace]
  refine ⟨102490505793715979704868041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136654007724954639606490721 102490505793715979704868041)
  ·
    refine ⟨76867879345286984778651031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102490505793715979704868041 76867879345286984778651031)
    ·
      refine ⟨115301819017930477167976547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76867879345286984778651031 115301819017930477167976547)
      ·
        refine ⟨172952728526895715751964821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115301819017930477167976547 172952728526895715751964821)
        ·
          refine ⟨8107159149698236675873351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 172952728526895715751964821 8107159149698236675873351)
          ·
            refine ⟨12160738724547355013810027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8107159149698236675873351 12160738724547355013810027)
            ·
              refine ⟨18241108086821032520715041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12160738724547355013810027 18241108086821032520715041)
              ·
                refine ⟨13680831065115774390536281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18241108086821032520715041 13680831065115774390536281)
                ·
                  refine ⟨10260623298836830792902211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13680831065115774390536281 10260623298836830792902211)
                  ·
                    refine ⟨15390934948255246189353317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10260623298836830792902211 15390934948255246189353317)
                    ·
                      refine ⟨2885800302797858660503747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15390934948255246189353317 2885800302797858660503747)
                      ·
                        rfl

theorem cell23_5620076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_5620076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620076 prefixEnd_5620076 := by exact prefixLift 5620076
  have htrace : WordTrace (prefixWord ++ tailWord_5620076) baseStart_5620076 baseEnd_5620076 := by
    simpa [prefixWord, tailWord_5620076, baseEnd_5620076] using wordTrace_append hprefix tailTrace_5620076
  have hstable : (prefixWord ++ tailWord_5620076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620076).length < 2 ^ (prefixWord ++ tailWord_5620076).sum := by decide
  have hdescent : baseEnd_5620076 < baseStart_5620076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620159 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 8, 4]
def baseStart_5620159 : Nat := 118140960795 + 5620159 * 2 ^ 59
def prefixEnd_5620159 : Nat := 4983230072969 + 3 ^ 40 * 5620159 * 2
def baseEnd_5620159 : Nat := 961947640564060611921955

theorem tailTrace_5620159 : CollatzResearch.WordTrace tailWord_5620159 prefixEnd_5620159 961947640564060611921955 := by
  unfold tailWord_5620159
  simp only [CollatzResearch.WordTrace]
  refine ⟨204984038846131264585007531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136656025897420843056671687 204984038846131264585007531)
  ·
    refine ⟨307476058269196896877511297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204984038846131264585007531 307476058269196896877511297)
    ·
      refine ⟨230607043701897672658133473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307476058269196896877511297 230607043701897672658133473)
      ·
        refine ⟨172955282776423254493600105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230607043701897672658133473 172955282776423254493600105)
        ·
          refine ⟨129716462082317440870200079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172955282776423254493600105 129716462082317440870200079)
          ·
            refine ⟨194574693123476161305300119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129716462082317440870200079 194574693123476161305300119)
            ·
              refine ⟨291862039685214241957950179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194574693123476161305300119 291862039685214241957950179)
              ·
                refine ⟨437793059527821362936925269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291862039685214241957950179 437793059527821362936925269)
                ·
                  refine ⟨5130387416341656596917093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 437793059527821362936925269 5130387416341656596917093)
                  ·
                    refine ⟨961947640564060611921955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5130387416341656596917093 961947640564060611921955)
                    ·
                      rfl

theorem cell23_5620159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 4].length) (baseStart_5620159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620159 prefixEnd_5620159 := by exact prefixLift 5620159
  have htrace : WordTrace (prefixWord ++ tailWord_5620159) baseStart_5620159 baseEnd_5620159 := by
    simpa [prefixWord, tailWord_5620159, baseEnd_5620159] using wordTrace_append hprefix tailTrace_5620159
  have hstable : (prefixWord ++ tailWord_5620159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620159).length < 2 ^ (prefixWord ++ tailWord_5620159).sum := by decide
  have hdescent : baseEnd_5620159 < baseStart_5620159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620180 : List Nat := [2, 4, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_5620180 : Nat := 118140960795 + 5620180 * 2 ^ 59
def prefixEnd_5620180 : Nat := 4983230072969 + 3 ^ 40 * 5620180 * 2
def baseEnd_5620180 : Nat := 961951234928642084534423

theorem tailTrace_5620180 : CollatzResearch.WordTrace tailWord_5620180 prefixEnd_5620180 961951234928642084534423 := by
  unfold tailWord_5620180
  simp only [CollatzResearch.WordTrace]
  refine ⟨102492402389527592585760997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136656536519370123447681329 102492402389527592585760997)
  ·
    refine ⟨19217325448036423609830187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102492402389527592585760997 19217325448036423609830187)
    ·
      refine ⟨28825988172054635414745281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19217325448036423609830187 28825988172054635414745281)
      ·
        refine ⟨21619491129040976561058961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28825988172054635414745281 21619491129040976561058961)
        ·
          refine ⟨16214618346780732420794221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21619491129040976561058961 16214618346780732420794221)
          ·
            refine ⟨6080481880042774657797833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16214618346780732420794221 6080481880042774657797833)
            ·
              refine ⟨4560361410032080993348375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6080481880042774657797833 4560361410032080993348375)
              ·
                refine ⟨6840542115048121490022563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4560361410032080993348375 6840542115048121490022563)
                ·
                  refine ⟨10260813172572182235033845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6840542115048121490022563 10260813172572182235033845)
                  ·
                    refine ⟨961951234928642084534423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10260813172572182235033845 961951234928642084534423)
                    ·
                      rfl

theorem cell23_5620180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_5620180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620180 prefixEnd_5620180 := by exact prefixLift 5620180
  have htrace : WordTrace (prefixWord ++ tailWord_5620180) baseStart_5620180 baseEnd_5620180 := by
    simpa [prefixWord, tailWord_5620180, baseEnd_5620180] using wordTrace_append hprefix tailTrace_5620180
  have hstable : (prefixWord ++ tailWord_5620180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620180).length < 2 ^ (prefixWord ++ tailWord_5620180).sum := by decide
  have hdescent : baseEnd_5620180 < baseStart_5620180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620189 : List Nat := [1, 4, 3, 1, 1, 1, 12]
def baseStart_5620189 : Nat := 118140960795 + 5620189 * 2 ^ 59
def prefixEnd_5620189 : Nat := 4983230072969 + 3 ^ 40 * 5620189 * 2
def baseEnd_5620189 : Nat := 35627880569281687881367

theorem tailTrace_5620189 : CollatzResearch.WordTrace tailWord_5620189 prefixEnd_5620189 35627880569281687881367 := by
  unfold tailWord_5620189
  simp only [CollatzResearch.WordTrace]
  refine ⟨204985133036022579708599621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136656755357348386472399747 204985133036022579708599621)
  ·
    refine ⟨38434712444254233695362429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204985133036022579708599621 38434712444254233695362429)
    ·
      refine ⟨14413017166595337635760911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38434712444254233695362429 14413017166595337635760911)
      ·
        refine ⟨21619525749893006453641367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14413017166595337635760911 21619525749893006453641367)
        ·
          refine ⟨32429288624839509680462051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21619525749893006453641367 32429288624839509680462051)
          ·
            refine ⟨48643932937259264520693077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32429288624839509680462051 48643932937259264520693077)
            ·
              refine ⟨35627880569281687881367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 48643932937259264520693077 35627880569281687881367)
              ·
                rfl

theorem cell23_5620189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 12].length) (baseStart_5620189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620189 prefixEnd_5620189 := by exact prefixLift 5620189
  have htrace : WordTrace (prefixWord ++ tailWord_5620189) baseStart_5620189 baseEnd_5620189 := by
    simpa [prefixWord, tailWord_5620189, baseEnd_5620189] using wordTrace_append hprefix tailTrace_5620189
  have hstable : (prefixWord ++ tailWord_5620189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620189).length < 2 ^ (prefixWord ++ tailWord_5620189).sum := by decide
  have hdescent : baseEnd_5620189 < baseStart_5620189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620200 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 3, 2, 2]
def baseStart_5620200 : Nat := 118140960795 + 5620200 * 2 ^ 59
def prefixEnd_5620200 : Nat := 4983230072969 + 3 ^ 40 * 5620200 * 2
def baseEnd_5620200 : Nat := 2885863974399016175353177

theorem tailTrace_5620200 : CollatzResearch.WordTrace tailWord_5620200 prefixEnd_5620200 2885863974399016175353177 := by
  unfold tailWord_5620200
  simp only [CollatzResearch.WordTrace]
  refine ⟨102492767119491364293625027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136657022825988485724833369 102492767119491364293625027)
  ·
    refine ⟨153739150679237046440437541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102492767119491364293625027 153739150679237046440437541)
    ·
      refine ⟨28826090752356946207582039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153739150679237046440437541 28826090752356946207582039)
      ·
        refine ⟨43239136128535419311373059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28826090752356946207582039 43239136128535419311373059)
        ·
          refine ⟨64858704192803128967059589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43239136128535419311373059 64858704192803128967059589)
          ·
            refine ⟨12161007036150586681323673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64858704192803128967059589 12161007036150586681323673)
            ·
              refine ⟨9120755277112940010992755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12161007036150586681323673 9120755277112940010992755)
              ·
                refine ⟨13681132915669410016489133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9120755277112940010992755 13681132915669410016489133)
                ·
                  refine ⟨5130424843376028756183425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13681132915669410016489133 5130424843376028756183425)
                  ·
                    refine ⟨3847818632532021567137569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5130424843376028756183425 3847818632532021567137569)
                    ·
                      refine ⟨2885863974399016175353177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3847818632532021567137569 2885863974399016175353177)
                      ·
                        rfl

theorem cell23_5620200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_5620200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620200 prefixEnd_5620200 := by exact prefixLift 5620200
  have htrace : WordTrace (prefixWord ++ tailWord_5620200) baseStart_5620200 baseEnd_5620200 := by
    simpa [prefixWord, tailWord_5620200, baseEnd_5620200] using wordTrace_append hprefix tailTrace_5620200
  have hstable : (prefixWord ++ tailWord_5620200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620200).length < 2 ^ (prefixWord ++ tailWord_5620200).sum := by decide
  have hdescent : baseEnd_5620200 < baseStart_5620200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620210 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 1, 6]
def baseStart_5620210 : Nat := 118140960795 + 5620210 * 2 ^ 59
def prefixEnd_5620210 : Nat := 4983230072969 + 3 ^ 40 * 5620210 * 2
def baseEnd_5620210 : Nat := 961956369735187045409377

theorem tailTrace_5620210 : CollatzResearch.WordTrace tailWord_5620210 prefixEnd_5620210 961956369735187045409377 := by
  unfold tailWord_5620210
  simp only [CollatzResearch.WordTrace]
  refine ⟨51246474742236625073778521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136657265979297666863409389 51246474742236625073778521)
  ·
    refine ⟨38434856056677468805333891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51246474742236625073778521 38434856056677468805333891)
    ·
      refine ⟨57652284085016203208000837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38434856056677468805333891 57652284085016203208000837)
      ·
        refine ⟨10809803265940538101500157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57652284085016203208000837 10809803265940538101500157)
        ·
          refine ⟨4053676224727701788062559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10809803265940538101500157 4053676224727701788062559)
          ·
            refine ⟨6080514337091552682093839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4053676224727701788062559 6080514337091552682093839)
            ·
              refine ⟨9120771505637329023140759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6080514337091552682093839 9120771505637329023140759)
              ·
                refine ⟨13681157258455993534711139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9120771505637329023140759 13681157258455993534711139)
                ·
                  refine ⟨20521735887683990302066709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13681157258455993534711139 20521735887683990302066709)
                  ·
                    refine ⟨961956369735187045409377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20521735887683990302066709 961956369735187045409377)
                    ·
                      rfl

theorem cell23_5620210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_5620210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620210 prefixEnd_5620210 := by exact prefixLift 5620210
  have htrace : WordTrace (prefixWord ++ tailWord_5620210) baseStart_5620210 baseEnd_5620210 := by
    simpa [prefixWord, tailWord_5620210, baseEnd_5620210] using wordTrace_append hprefix tailTrace_5620210
  have hstable : (prefixWord ++ tailWord_5620210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620210).length < 2 ^ (prefixWord ++ tailWord_5620210).sum := by decide
  have hdescent : baseEnd_5620210 < baseStart_5620210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620213 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_5620213 : Nat := 118140960795 + 5620213 * 2 ^ 59
def prefixEnd_5620213 : Nat := 4983230072969 + 3 ^ 40 * 5620213 * 2
def baseEnd_5620213 : Nat := 2885870649647524624490617

theorem tailTrace_5620213 : CollatzResearch.WordTrace tailWord_5620213 prefixEnd_5620213 2885870649647524624490617 := by
  unfold tailWord_5620213
  simp only [CollatzResearch.WordTrace]
  refine ⟨204986008387935631807473293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136657338925290421204982195 204986008387935631807473293)
  ·
    refine ⟨76869753145475861927802485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204986008387935631807473293 76869753145475861927802485)
    ·
      refine ⟨7206539357388362055731483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76869753145475861927802485 7206539357388362055731483)
      ·
        refine ⟨10809809036082543083597225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7206539357388362055731483 10809809036082543083597225)
        ·
          refine ⟨8107356777061907312697919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10809809036082543083597225 8107356777061907312697919)
          ·
            refine ⟨12161035165592860969046879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8107356777061907312697919 12161035165592860969046879)
            ·
              refine ⟨18241552748389291453570319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12161035165592860969046879 18241552748389291453570319)
              ·
                refine ⟨27362329122583937180355479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18241552748389291453570319 27362329122583937180355479)
                ·
                  refine ⟨41043493683875905770533219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27362329122583937180355479 41043493683875905770533219)
                  ·
                    refine ⟨61565240525813858655799829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41043493683875905770533219 61565240525813858655799829)
                    ·
                      refine ⟨2885870649647524624490617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61565240525813858655799829 2885870649647524624490617)
                      ·
                        rfl

theorem cell23_5620213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_5620213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620213 prefixEnd_5620213 := by exact prefixLift 5620213
  have htrace : WordTrace (prefixWord ++ tailWord_5620213) baseStart_5620213 baseEnd_5620213 := by
    simpa [prefixWord, tailWord_5620213, baseEnd_5620213] using wordTrace_append hprefix tailTrace_5620213
  have hstable : (prefixWord ++ tailWord_5620213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620213).length < 2 ^ (prefixWord ++ tailWord_5620213).sum := by decide
  have hdescent : baseEnd_5620213 < baseStart_5620213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620229 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 2, 2, 5]
def baseStart_5620229 : Nat := 118140960795 + 5620229 * 2 ^ 59
def prefixEnd_5620229 : Nat := 4983230072969 + 3 ^ 40 * 5620229 * 2
def baseEnd_5620229 : Nat := 2885878865337996561890543

theorem tailTrace_5620229 : CollatzResearch.WordTrace tailWord_5620229 prefixEnd_5620229 2885878865337996561890543 := by
  unfold tailWord_5620229
  simp only [CollatzResearch.WordTrace]
  refine ⟨204986591955877666540055741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136657727970585111026703827 204986591955877666540055741)
  ·
    refine ⟨76869971983454124952520903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204986591955877666540055741 76869971983454124952520903)
    ·
      refine ⟨115304957975181187428781355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76869971983454124952520903 115304957975181187428781355)
      ·
        refine ⟨172957436962771781143172033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115304957975181187428781355 172957436962771781143172033)
        ·
          refine ⟨129718077722078835857379025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172957436962771781143172033 129718077722078835857379025)
          ·
            refine ⟨97288558291559126893034269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129718077722078835857379025 97288558291559126893034269)
            ·
              refine ⟨36483209359334672584887851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97288558291559126893034269 36483209359334672584887851)
              ·
                refine ⟨54724814039002008877331777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36483209359334672584887851 54724814039002008877331777)
                ·
                  refine ⟨41043610529251506657998833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54724814039002008877331777 41043610529251506657998833)
                  ·
                    refine ⟨30782707896938629993499125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41043610529251506657998833 30782707896938629993499125)
                    ·
                      refine ⟨2885878865337996561890543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30782707896938629993499125 2885878865337996561890543)
                      ·
                        rfl

theorem cell23_5620229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_5620229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620229 prefixEnd_5620229 := by exact prefixLift 5620229
  have htrace : WordTrace (prefixWord ++ tailWord_5620229) baseStart_5620229 baseEnd_5620229 := by
    simpa [prefixWord, tailWord_5620229, baseEnd_5620229] using wordTrace_append hprefix tailTrace_5620229
  have hstable : (prefixWord ++ tailWord_5620229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620229).length < 2 ^ (prefixWord ++ tailWord_5620229).sum := by decide
  have hdescent : baseEnd_5620229 < baseStart_5620229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620237 : List Nat := [1, 7, 1, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_5620237 : Nat := 118140960795 + 5620237 * 2 ^ 59
def prefixEnd_5620237 : Nat := 4983230072969 + 3 ^ 40 * 5620237 * 2
def baseEnd_5620237 : Nat := 2885882973183232530590507

theorem tailTrace_5620237 : CollatzResearch.WordTrace tailWord_5620237 prefixEnd_5620237 2885882973183232530590507 := by
  unfold tailWord_5620237
  simp only [CollatzResearch.WordTrace]
  refine ⟨204986883739848683906346965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136657922493232455937564643 204986883739848683906346965)
  ·
    refine ⟨4804380087652703529055007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 204986883739848683906346965 4804380087652703529055007)
    ·
      refine ⟨7206570131479055293582511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4804380087652703529055007 7206570131479055293582511)
      ·
        refine ⟨10809855197218582940373767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7206570131479055293582511 10809855197218582940373767)
        ·
          refine ⟨16214782795827874410560651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10809855197218582940373767 16214782795827874410560651)
          ·
            refine ⟨24322174193741811615840977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16214782795827874410560651 24322174193741811615840977)
            ·
              refine ⟨18241630645306358711880733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24322174193741811615840977 18241630645306358711880733)
              ·
                refine ⟨6840611491989884516955275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18241630645306358711880733 6840611491989884516955275)
                ·
                  refine ⟨10260917237984826775432913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6840611491989884516955275 10260917237984826775432913)
                  ·
                    refine ⟨7695687928488620081574685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10260917237984826775432913 7695687928488620081574685)
                    ·
                      refine ⟨2885882973183232530590507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7695687928488620081574685 2885882973183232530590507)
                      ·
                        rfl

theorem cell23_5620237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_5620237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620237 prefixEnd_5620237 := by exact prefixLift 5620237
  have htrace : WordTrace (prefixWord ++ tailWord_5620237) baseStart_5620237 baseEnd_5620237 := by
    simpa [prefixWord, tailWord_5620237, baseEnd_5620237] using wordTrace_append hprefix tailTrace_5620237
  have hstable : (prefixWord ++ tailWord_5620237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620237).length < 2 ^ (prefixWord ++ tailWord_5620237).sum := by decide
  have hdescent : baseEnd_5620237 < baseStart_5620237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620243 : List Nat := [1, 1, 1, 2, 1, 5, 1, 5, 1, 3, 2]
def baseStart_5620243 : Nat := 118140960795 + 5620243 * 2 ^ 59
def prefixEnd_5620243 : Nat := 4983230072969 + 3 ^ 40 * 5620243 * 2
def baseEnd_5620243 : Nat := 2885886054067159507115479

theorem tailTrace_5620243 : CollatzResearch.WordTrace tailWord_5620243 prefixEnd_5620243 2885886054067159507115479 := by
  unfold tailWord_5620243
  simp only [CollatzResearch.WordTrace]
  refine ⟨204987102577826946931065383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136658068385217964620710255 204987102577826946931065383)
  ·
    refine ⟨307480653866740420396598075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204987102577826946931065383 307480653866740420396598075)
    ·
      refine ⟨461220980800110630594897113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307480653866740420396598075 461220980800110630594897113)
      ·
        refine ⟨345915735600082972946172835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461220980800110630594897113 345915735600082972946172835)
        ·
          refine ⟨518873603400124459419259253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345915735600082972946172835 518873603400124459419259253)
          ·
            refine ⟨48644400318761668070555555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 518873603400124459419259253 48644400318761668070555555)
            ·
              refine ⟨72966600478142502105833333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48644400318761668070555555 72966600478142502105833333)
              ·
                refine ⟨6840618794825859572421875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72966600478142502105833333 6840618794825859572421875)
                ·
                  refine ⟨10260928192238789358632813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6840618794825859572421875 10260928192238789358632813)
                  ·
                    refine ⟨3847848072089546009487305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10260928192238789358632813 3847848072089546009487305)
                    ·
                      refine ⟨2885886054067159507115479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3847848072089546009487305 2885886054067159507115479)
                      ·
                        rfl

theorem cell23_5620243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 3, 2].length) (baseStart_5620243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620243 prefixEnd_5620243 := by exact prefixLift 5620243
  have htrace : WordTrace (prefixWord ++ tailWord_5620243) baseStart_5620243 baseEnd_5620243 := by
    simpa [prefixWord, tailWord_5620243, baseEnd_5620243] using wordTrace_append hprefix tailTrace_5620243
  have hstable : (prefixWord ++ tailWord_5620243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620243).length < 2 ^ (prefixWord ++ tailWord_5620243).sum := by decide
  have hdescent : baseEnd_5620243 < baseStart_5620243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620279 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 9]
def baseStart_5620279 : Nat := 118140960795 + 5620279 * 2 ^ 59
def prefixEnd_5620279 : Nat := 4983230072969 + 3 ^ 40 * 5620279 * 2
def baseEnd_5620279 : Nat := 320656059930080151807257

theorem tailTrace_5620279 : CollatzResearch.WordTrace tailWord_5620279 prefixEnd_5620279 320656059930080151807257 := by
  unfold tailWord_5620279
  simp only [CollatzResearch.WordTrace]
  refine ⟨204988415605696525079375891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136658943737131016719583927 204988415605696525079375891)
  ·
    refine ⟨307482623408544787619063837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204988415605696525079375891 307482623408544787619063837)
    ·
      refine ⟨115305983778204295357148939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307482623408544787619063837 115305983778204295357148939)
      ·
        refine ⟨172958975667306443035723409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115305983778204295357148939 172958975667306443035723409)
        ·
          refine ⟨129719231750479832276792557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172958975667306443035723409 129719231750479832276792557)
          ·
            refine ⟨48644711906429937103797209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129719231750479832276792557 48644711906429937103797209)
            ·
              refine ⟨36483533929822452827847907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48644711906429937103797209 36483533929822452827847907)
              ·
                refine ⟨54725300894733679241771861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36483533929822452827847907 54725300894733679241771861)
                ·
                  refine ⟨320656059930080151807257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54725300894733679241771861 320656059930080151807257)
                  ·
                    rfl

theorem cell23_5620279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 9].length) (baseStart_5620279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620279 prefixEnd_5620279 := by exact prefixLift 5620279
  have htrace : WordTrace (prefixWord ++ tailWord_5620279) baseStart_5620279 baseEnd_5620279 := by
    simpa [prefixWord, tailWord_5620279, baseEnd_5620279] using wordTrace_append hprefix tailTrace_5620279
  have hstable : (prefixWord ++ tailWord_5620279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620279).length < 2 ^ (prefixWord ++ tailWord_5620279).sum := by decide
  have hdescent : baseEnd_5620279 < baseStart_5620279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620339 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 1, 10]
def baseStart_5620339 : Nat := 118140960795 + 5620339 * 2 ^ 59
def prefixEnd_5620339 : Nat := 4983230072969 + 3 ^ 40 * 5620339 * 2
def baseEnd_5620339 : Nat := 961978449403330377171679

theorem tailTrace_5620339 : CollatzResearch.WordTrace tailWord_5620339 prefixEnd_5620339 961978449403330377171679 := by
  unfold tailWord_5620339
  simp only [CollatzResearch.WordTrace]
  refine ⟨204990603985479155326560071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136660402656986103551040047 204990603985479155326560071)
  ·
    refine ⟨307485905978218732989840107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204990603985479155326560071 307485905978218732989840107)
    ·
      refine ⟨461228858967328099484760161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307485905978218732989840107 461228858967328099484760161)
      ·
        refine ⟨345921644225496074613570121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461228858967328099484760161 345921644225496074613570121)
        ·
          refine ⟨259441233169122055960177591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345921644225496074613570121 259441233169122055960177591)
          ·
            refine ⟨389161849753683083940266387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259441233169122055960177591 389161849753683083940266387)
            ·
              refine ⟨583742774630524625910399581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389161849753683083940266387 583742774630524625910399581)
              ·
                refine ⟨218903540486446734716399843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 583742774630524625910399581 218903540486446734716399843)
                ·
                  refine ⟨328355310729670102074599765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218903540486446734716399843 328355310729670102074599765)
                  ·
                    refine ⟨961978449403330377171679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 328355310729670102074599765 961978449403330377171679)
                    ·
                      rfl

theorem cell23_5620339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 10].length) (baseStart_5620339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620339 prefixEnd_5620339 := by exact prefixLift 5620339
  have htrace : WordTrace (prefixWord ++ tailWord_5620339) baseStart_5620339 baseEnd_5620339 := by
    simpa [prefixWord, tailWord_5620339, baseEnd_5620339] using wordTrace_append hprefix tailTrace_5620339
  have hstable : (prefixWord ++ tailWord_5620339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620339).length < 2 ^ (prefixWord ++ tailWord_5620339).sum := by decide
  have hdescent : baseEnd_5620339 < baseStart_5620339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620376 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 2, 1, 6]
def baseStart_5620376 : Nat := 118140960795 + 5620376 * 2 ^ 59
def prefixEnd_5620376 : Nat := 4983230072969 + 3 ^ 40 * 5620376 * 2
def baseEnd_5620376 : Nat := 2885954346994207486752367

theorem tailTrace_5620376 : CollatzResearch.WordTrace tailWord_5620376 prefixEnd_5620376 2885954346994207486752367 := by
  unfold tailWord_5620376
  simp only [CollatzResearch.WordTrace]
  refine ⟨102495976743172555322828491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136661302324230073763771321 102495976743172555322828491)
  ·
    refine ⟨153743965114758832984242737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102495976743172555322828491 153743965114758832984242737)
    ·
      refine ⟨115307973836069124738182053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153743965114758832984242737 115307973836069124738182053)
      ·
        refine ⟨21620245094262960888409135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115307973836069124738182053 21620245094262960888409135)
        ·
          refine ⟨32430367641394441332613703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21620245094262960888409135 32430367641394441332613703)
          ·
            refine ⟨48645551462091661998920555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32430367641394441332613703 48645551462091661998920555)
            ·
              refine ⟨72968327193137492998380833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48645551462091661998920555 72968327193137492998380833)
              ·
                refine ⟨54726245394853119748785625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72968327193137492998380833 54726245394853119748785625)
                ·
                  refine ⟨41044684046139839811589219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54726245394853119748785625 41044684046139839811589219)
                  ·
                    refine ⟨61567026069209759717383829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41044684046139839811589219 61567026069209759717383829)
                    ·
                      refine ⟨2885954346994207486752367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61567026069209759717383829 2885954346994207486752367)
                      ·
                        rfl

theorem cell23_5620376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_5620376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620376 prefixEnd_5620376 := by exact prefixLift 5620376
  have htrace : WordTrace (prefixWord ++ tailWord_5620376) baseStart_5620376 baseEnd_5620376 := by
    simpa [prefixWord, tailWord_5620376, baseEnd_5620376] using wordTrace_append hprefix tailTrace_5620376
  have hstable : (prefixWord ++ tailWord_5620376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620376).length < 2 ^ (prefixWord ++ tailWord_5620376).sum := by decide
  have hdescent : baseEnd_5620376 < baseStart_5620376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620380 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 2, 4, 2]
def baseStart_5620380 : Nat := 118140960795 + 5620380 * 2 ^ 59
def prefixEnd_5620380 : Nat := 4983230072969 + 3 ^ 40 * 5620380 * 2
def baseEnd_5620380 : Nat := 2885956400916825471102349

theorem tailTrace_5620380 : CollatzResearch.WordTrace tailWord_5620380 prefixEnd_5620380 2885956400916825471102349 := by
  unfold tailWord_5620380
  simp only [CollatzResearch.WordTrace]
  refine ⟨102496049689165309664401297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136661399585553746219201729 102496049689165309664401297)
  ·
    refine ⟨76872037266873982248300973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102496049689165309664401297 76872037266873982248300973)
    ·
      refine ⟨28827013975077743343112865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76872037266873982248300973 28827013975077743343112865)
      ·
        refine ⟨21620260481308307507334649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28827013975077743343112865 21620260481308307507334649)
        ·
          refine ⟨16215195360981230630500987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21620260481308307507334649 16215195360981230630500987)
          ·
            refine ⟨24322793041471845945751481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16215195360981230630500987 24322793041471845945751481)
            ·
              refine ⟨18242094781103884459313611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24322793041471845945751481 18242094781103884459313611)
              ·
                refine ⟨27363142171655826688970417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18242094781103884459313611 27363142171655826688970417)
                ·
                  refine ⟨20522356628741870016727813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27363142171655826688970417 20522356628741870016727813)
                  ·
                    refine ⟨3847941867889100628136465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20522356628741870016727813 3847941867889100628136465)
                    ·
                      refine ⟨2885956400916825471102349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3847941867889100628136465 2885956400916825471102349)
                      ·
                        rfl

theorem cell23_5620380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_5620380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620380 prefixEnd_5620380 := by exact prefixLift 5620380
  have htrace : WordTrace (prefixWord ++ tailWord_5620380) baseStart_5620380 baseEnd_5620380 := by
    simpa [prefixWord, tailWord_5620380, baseEnd_5620380] using wordTrace_append hprefix tailTrace_5620380
  have hstable : (prefixWord ++ tailWord_5620380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620380).length < 2 ^ (prefixWord ++ tailWord_5620380).sum := by decide
  have hdescent : baseEnd_5620380 < baseStart_5620380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620423 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 3, 5, 2]
def baseStart_5620423 : Nat := 118140960795 + 5620423 * 2 ^ 59
def prefixEnd_5620423 : Nat := 4983230072969 + 3 ^ 40 * 5620423 * 2
def baseEnd_5620423 : Nat := 2885978480584968802864651

theorem tailTrace_5620423 : CollatzResearch.WordTrace tailWord_5620423 prefixEnd_5620423 2885978480584968802864651 := by
  unfold tailWord_5620423
  simp only [CollatzResearch.WordTrace]
  refine ⟨204993667717174837672617923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136662445144783225115078615 204993667717174837672617923)
  ·
    refine ⟨307490501575762256508926885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204993667717174837672617923 307490501575762256508926885)
    ·
      refine ⟨57654469045455423095423791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 307490501575762256508926885 57654469045455423095423791)
      ·
        refine ⟨86481703568183134643135687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57654469045455423095423791 86481703568183134643135687)
        ·
          refine ⟨129722555352274701964703531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86481703568183134643135687 129722555352274701964703531)
          ·
            refine ⟨194583833028412052947055297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129722555352274701964703531 194583833028412052947055297)
            ·
              refine ⟨145937874771309039710291473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194583833028412052947055297 145937874771309039710291473)
              ·
                refine ⟨109453406078481779782718605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145937874771309039710291473 109453406078481779782718605)
                ·
                  refine ⟨41045027279430667418519477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109453406078481779782718605 41045027279430667418519477)
                  ·
                    refine ⟨3847971307446625070486201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41045027279430667418519477 3847971307446625070486201)
                    ·
                      refine ⟨2885978480584968802864651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3847971307446625070486201 2885978480584968802864651)
                      ·
                        rfl

theorem cell23_5620423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_5620423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620423 prefixEnd_5620423 := by exact prefixLift 5620423
  have htrace : WordTrace (prefixWord ++ tailWord_5620423) baseStart_5620423 baseEnd_5620423 := by
    simpa [prefixWord, tailWord_5620423, baseEnd_5620423] using wordTrace_append hprefix tailTrace_5620423
  have hstable : (prefixWord ++ tailWord_5620423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620423).length < 2 ^ (prefixWord ++ tailWord_5620423).sum := by decide
  have hdescent : baseEnd_5620423 < baseStart_5620423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620463 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 1, 6]
def baseStart_5620463 : Nat := 118140960795 + 5620463 * 2 ^ 59
def prefixEnd_5620463 : Nat := 4983230072969 + 3 ^ 40 * 5620463 * 2
def baseEnd_5620463 : Nat := 961999673270382882121489

theorem tailTrace_5620463 : CollatzResearch.WordTrace tailWord_5620463 prefixEnd_5620463 961999673270382882121489 := by
  unfold tailWord_5620463
  simp only [CollatzResearch.WordTrace]
  refine ⟨204995126637029924504074043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136663417758019949669382695 204995126637029924504074043)
  ·
    refine ⟨307492689955544886756111065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204995126637029924504074043 307492689955544886756111065)
    ·
      refine ⟨230619517466658665067083299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307492689955544886756111065 230619517466658665067083299)
      ·
        refine ⟨345929276199987997600624949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230619517466658665067083299 345929276199987997600624949)
        ·
          refine ⟨32430869643748874775058589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 345929276199987997600624949 32430869643748874775058589)
          ·
            refine ⟨12161576116405828040646971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32430869643748874775058589 12161576116405828040646971)
            ·
              refine ⟨18242364174608742060970457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12161576116405828040646971 18242364174608742060970457)
              ·
                refine ⟨13681773130956556545727843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18242364174608742060970457 13681773130956556545727843)
                ·
                  refine ⟨20522659696434834818591765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13681773130956556545727843 20522659696434834818591765)
                  ·
                    refine ⟨961999673270382882121489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20522659696434834818591765 961999673270382882121489)
                    ·
                      rfl

theorem cell23_5620463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 6].length) (baseStart_5620463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620463 prefixEnd_5620463 := by exact prefixLift 5620463
  have htrace : WordTrace (prefixWord ++ tailWord_5620463) baseStart_5620463 baseEnd_5620463 := by
    simpa [prefixWord, tailWord_5620463, baseEnd_5620463] using wordTrace_append hprefix tailTrace_5620463
  have hstable : (prefixWord ++ tailWord_5620463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620463).length < 2 ^ (prefixWord ++ tailWord_5620463).sum := by decide
  have hdescent : baseEnd_5620463 < baseStart_5620463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620476 : List Nat := [2, 2, 2, 1, 3, 13]
def baseStart_5620476 : Nat := 118140960795 + 5620476 * 2 ^ 59
def prefixEnd_5620476 : Nat := 4983230072969 + 3 ^ 40 * 5620476 * 2
def baseEnd_5620476 : Nat := 11876566646336037430049

theorem tailTrace_5620476 : CollatzResearch.WordTrace tailWord_5620476 prefixEnd_5620476 11876566646336037430049 := by
  unfold tailWord_5620476
  simp only [CollatzResearch.WordTrace]
  refine ⟨102497800392991413862148641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136663733857321885149531521 102497800392991413862148641)
  ·
    refine ⟨76873350294743560396611481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102497800392991413862148641 76873350294743560396611481)
    ·
      refine ⟨57655012721057670297458611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76873350294743560396611481 57655012721057670297458611)
      ·
        refine ⟨86482519081586505446187917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57655012721057670297458611 86482519081586505446187917)
        ·
          refine ⟨32430944655594939542320469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86482519081586505446187917 32430944655594939542320469)
          ·
            refine ⟨11876566646336037430049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 32430944655594939542320469 11876566646336037430049)
            ·
              rfl

theorem cell23_5620476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 13].length) (baseStart_5620476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620476 prefixEnd_5620476 := by exact prefixLift 5620476
  have htrace : WordTrace (prefixWord ++ tailWord_5620476) baseStart_5620476 baseEnd_5620476 := by
    simpa [prefixWord, tailWord_5620476, baseEnd_5620476] using wordTrace_append hprefix tailTrace_5620476
  have hstable : (prefixWord ++ tailWord_5620476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620476).length < 2 ^ (prefixWord ++ tailWord_5620476).sum := by decide
  have hdescent : baseEnd_5620476 < baseStart_5620476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620520 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_5620520 : Nat := 118140960795 + 5620520 * 2 ^ 59
def prefixEnd_5620520 : Nat := 4983230072969 + 3 ^ 40 * 5620520 * 2
def baseEnd_5620520 : Nat := 2886028288208454923351705

theorem tailTrace_5620520 : CollatzResearch.WordTrace tailWord_5620520 prefixEnd_5620520 2886028288208454923351705 := by
  unfold tailWord_5620520
  simp only [CollatzResearch.WordTrace]
  refine ⟨102498602798911711619449507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136664803731882282159266009 102498602798911711619449507)
  ·
    refine ⟨153747904198367567429174261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102498602798911711619449507 153747904198367567429174261)
    ·
      refine ⟨14413866018596959446485087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153747904198367567429174261 14413866018596959446485087)
      ·
        refine ⟨21620799027895439169727631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14413866018596959446485087 21620799027895439169727631)
        ·
          refine ⟨32431198541843158754591447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21620799027895439169727631 32431198541843158754591447)
          ·
            refine ⟨48646797812764738131887171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32431198541843158754591447 48646797812764738131887171)
            ·
              refine ⟨72970196719147107197830757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48646797812764738131887171 72970196719147107197830757)
              ·
                refine ⟨13681911884840082599593267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72970196719147107197830757 13681911884840082599593267)
                ·
                  refine ⟨20522867827260123899389901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13681911884840082599593267 20522867827260123899389901)
                  ·
                    refine ⟨7696075435222546462271213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20522867827260123899389901 7696075435222546462271213)
                    ·
                      refine ⟨2886028288208454923351705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7696075435222546462271213 2886028288208454923351705)
                      ·
                        rfl

theorem cell23_5620520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_5620520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620520 prefixEnd_5620520 := by exact prefixLift 5620520
  have htrace : WordTrace (prefixWord ++ tailWord_5620520) baseStart_5620520 baseEnd_5620520 := by
    simpa [prefixWord, tailWord_5620520, baseEnd_5620520] using wordTrace_append hprefix tailTrace_5620520
  have hstable : (prefixWord ++ tailWord_5620520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620520).length < 2 ^ (prefixWord ++ tailWord_5620520).sum := by decide
  have hdescent : baseEnd_5620520 < baseStart_5620520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620553 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 2, 6]
def baseStart_5620553 : Nat := 118140960795 + 5620553 * 2 ^ 59
def prefixEnd_5620553 : Nat := 4983230072969 + 3 ^ 40 * 5620553 * 2
def baseEnd_5620553 : Nat := 962015077690017764746351

theorem tailTrace_5620553 : CollatzResearch.WordTrace tailWord_5620553 prefixEnd_5620553 962015077690017764746351 := by
  unfold tailWord_5620553
  simp only [CollatzResearch.WordTrace]
  refine ⟨204998409206703869874850313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136665606137802579916566875 204998409206703869874850313)
  ·
    refine ⟨153748806905027902406137735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204998409206703869874850313 153748806905027902406137735)
    ·
      refine ⟨230623210357541853609206603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153748806905027902406137735 230623210357541853609206603)
      ·
        refine ⟨345934815536312780413809905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230623210357541853609206603 345934815536312780413809905)
        ·
          refine ⟨259451111652234585310357429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345934815536312780413809905 259451111652234585310357429)
          ·
            refine ⟨24323541717396992372846009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 259451111652234585310357429 24323541717396992372846009)
            ·
              refine ⟨18242656288047744279634507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24323541717396992372846009 18242656288047744279634507)
              ·
                refine ⟨27363984432071616419451761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18242656288047744279634507 27363984432071616419451761)
                ·
                  refine ⟨20522988324053712314588821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27363984432071616419451761 20522988324053712314588821)
                  ·
                    refine ⟨962015077690017764746351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20522988324053712314588821 962015077690017764746351)
                    ·
                      rfl

theorem cell23_5620553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 6].length) (baseStart_5620553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620553 prefixEnd_5620553 := by exact prefixLift 5620553
  have htrace : WordTrace (prefixWord ++ tailWord_5620553) baseStart_5620553 baseEnd_5620553 := by
    simpa [prefixWord, tailWord_5620553, baseEnd_5620553] using wordTrace_append hprefix tailTrace_5620553
  have hstable : (prefixWord ++ tailWord_5620553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620553).length < 2 ^ (prefixWord ++ tailWord_5620553).sum := by decide
  have hdescent : baseEnd_5620553 < baseStart_5620553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620563 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 3]
def baseStart_5620563 : Nat := 118140960795 + 5620563 * 2 ^ 59
def prefixEnd_5620563 : Nat := 4983230072969 + 3 ^ 40 * 5620563 * 2
def baseEnd_5620563 : Nat := 2886050367876598255114007

theorem tailTrace_5620563 : CollatzResearch.WordTrace tailWord_5620563 prefixEnd_5620563 2886050367876598255114007 := by
  unfold tailWord_5620563
  simp only [CollatzResearch.WordTrace]
  refine ⟨204998773936667641582714343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136665849291111761055142895 204998773936667641582714343)
  ·
    refine ⟨307498160905001462374071515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204998773936667641582714343 307498160905001462374071515)
    ·
      refine ⟨461247241357502193561107273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307498160905001462374071515 461247241357502193561107273)
      ·
        refine ⟨345935431018126645170830455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461247241357502193561107273 345935431018126645170830455)
        ·
          refine ⟨518903146527189967756245683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345935431018126645170830455 518903146527189967756245683)
          ·
            refine ⟨778354719790784951634368525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518903146527189967756245683 778354719790784951634368525)
            ·
              refine ⟨291883019921544356862888197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 778354719790784951634368525 291883019921544356862888197)
              ·
                refine ⟨54728066235289566911791537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 291883019921544356862888197 54728066235289566911791537)
                ·
                  refine ⟨41046049676467175183843653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54728066235289566911791537 41046049676467175183843653)
                  ·
                    refine ⟨7696134314337595346970685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41046049676467175183843653 7696134314337595346970685)
                    ·
                      refine ⟨2886050367876598255114007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7696134314337595346970685 2886050367876598255114007)
                      ·
                        rfl

theorem cell23_5620563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 3].length) (baseStart_5620563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620563 prefixEnd_5620563 := by exact prefixLift 5620563
  have htrace : WordTrace (prefixWord ++ tailWord_5620563) baseStart_5620563 baseEnd_5620563 := by
    simpa [prefixWord, tailWord_5620563, baseEnd_5620563] using wordTrace_append hprefix tailTrace_5620563
  have hstable : (prefixWord ++ tailWord_5620563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620563).length < 2 ^ (prefixWord ++ tailWord_5620563).sum := by decide
  have hdescent : baseEnd_5620563 < baseStart_5620563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620580 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_5620580 : Nat := 118140960795 + 5620580 * 2 ^ 59
def prefixEnd_5620580 : Nat := 4983230072969 + 3 ^ 40 * 5620580 * 2
def baseEnd_5620580 : Nat := 2886059097047724688601429

theorem tailTrace_5620580 : CollatzResearch.WordTrace tailWord_5620580 prefixEnd_5620580 2886059097047724688601429 := by
  unfold tailWord_5620580
  simp only [CollatzResearch.WordTrace]
  refine ⟨102499696988803026743041597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136666262651737368990722129 102499696988803026743041597)
  ·
    refine ⟨38437386370801135028640599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102499696988803026743041597 38437386370801135028640599)
    ·
      refine ⟨57656079556201702542960899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38437386370801135028640599 57656079556201702542960899)
      ·
        refine ⟨86484119334302553814441349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57656079556201702542960899 86484119334302553814441349)
        ·
          refine ⟨16215772375181728840207753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86484119334302553814441349 16215772375181728840207753)
          ·
            refine ⟨12161829281386296630155815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16215772375181728840207753 12161829281386296630155815)
            ·
              refine ⟨18242743922079444945233723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12161829281386296630155815 18242743922079444945233723)
              ·
                refine ⟨27364115883119167417850585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18242743922079444945233723 27364115883119167417850585)
                ·
                  refine ⟨20523086912339375563387939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27364115883119167417850585 20523086912339375563387939)
                  ·
                    refine ⟨30784630368509063345081909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20523086912339375563387939 30784630368509063345081909)
                    ·
                      refine ⟨2886059097047724688601429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30784630368509063345081909 2886059097047724688601429)
                      ·
                        rfl

theorem cell23_5620580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_5620580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620580 prefixEnd_5620580 := by exact prefixLift 5620580
  have htrace : WordTrace (prefixWord ++ tailWord_5620580) baseStart_5620580 baseEnd_5620580 := by
    simpa [prefixWord, tailWord_5620580, baseEnd_5620580] using wordTrace_append hprefix tailTrace_5620580
  have hstable : (prefixWord ++ tailWord_5620580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620580).length < 2 ^ (prefixWord ++ tailWord_5620580).sum := by decide
  have hdescent : baseEnd_5620580 < baseStart_5620580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620687 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 3]
def baseStart_5620687 : Nat := 118140960795 + 5620687 * 2 ^ 59
def prefixEnd_5620687 : Nat := 4983230072969 + 3 ^ 40 * 5620687 * 2
def baseEnd_5620687 : Nat := 2886114039477755769963437

theorem tailTrace_5620687 : CollatzResearch.WordTrace tailWord_5620687 prefixEnd_5620687 2886114039477755769963437 := by
  unfold tailWord_5620687
  simp only [CollatzResearch.WordTrace]
  refine ⟨205003296588218410760228315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136668864392145607173485543 205003296588218410760228315)
  ·
    refine ⟨307504944882327616140342473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205003296588218410760228315 307504944882327616140342473)
    ·
      refine ⟨230628708661745712105256855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307504944882327616140342473 230628708661745712105256855)
      ·
        refine ⟨345943062992618568157885283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230628708661745712105256855 345943062992618568157885283)
        ·
          refine ⟨518914594488927852236827925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345943062992618568157885283 518914594488927852236827925)
          ·
            refine ⟨24324121616668493073601309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 518914594488927852236827925 24324121616668493073601309)
            ·
              refine ⟨9121545606250684902600491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24324121616668493073601309 9121545606250684902600491)
              ·
                refine ⟨13682318409376027353900737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9121545606250684902600491 13682318409376027353900737)
                ·
                  refine ⟨10261738807032020515425553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13682318409376027353900737 10261738807032020515425553)
                  ·
                    refine ⟨7696304105274015386569165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10261738807032020515425553 7696304105274015386569165)
                    ·
                      refine ⟨2886114039477755769963437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7696304105274015386569165 2886114039477755769963437)
                      ·
                        rfl

theorem cell23_5620687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 3].length) (baseStart_5620687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620687 prefixEnd_5620687 := by exact prefixLift 5620687
  have htrace : WordTrace (prefixWord ++ tailWord_5620687) baseStart_5620687 baseEnd_5620687 := by
    simpa [prefixWord, tailWord_5620687, baseEnd_5620687] using wordTrace_append hprefix tailTrace_5620687
  have hstable : (prefixWord ++ tailWord_5620687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620687).length < 2 ^ (prefixWord ++ tailWord_5620687).sum := by decide
  have hdescent : baseEnd_5620687 < baseStart_5620687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620737 : List Nat := [1, 2, 4, 1, 2, 2, 1, 4, 1, 5]
def baseStart_5620737 : Nat := 118140960795 + 5620737 * 2 ^ 59
def prefixEnd_5620737 : Nat := 4983230072969 + 3 ^ 40 * 5620737 * 2
def baseEnd_5620737 : Nat := 962046571170160191446069

theorem tailTrace_5620737 : CollatzResearch.WordTrace tailWord_5620737 prefixEnd_5620737 962046571170160191446069 := by
  unfold tailWord_5620737
  simp only [CollatzResearch.WordTrace]
  refine ⟨205005120238037269299548465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136670080158691512866365643 205005120238037269299548465)
  ·
    refine ⟨153753840178527951974661349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205005120238037269299548465 153753840178527951974661349)
    ·
      refine ⟨28828845033473990995249003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153753840178527951974661349 28828845033473990995249003)
      ·
        refine ⟨43243267550210986492873505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28828845033473990995249003 43243267550210986492873505)
        ·
          refine ⟨32432450662658239869655129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43243267550210986492873505 32432450662658239869655129)
          ·
            refine ⟨24324337996993679902241347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32432450662658239869655129 24324337996993679902241347)
            ·
              refine ⟨36486506995490519853362021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24324337996993679902241347 36486506995490519853362021)
              ·
                refine ⟨6841220061654472472505379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36486506995490519853362021 6841220061654472472505379)
                ·
                  refine ⟨10261830092481708708758069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6841220061654472472505379 10261830092481708708758069)
                  ·
                    refine ⟨962046571170160191446069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10261830092481708708758069 962046571170160191446069)
                    ·
                      rfl

theorem cell23_5620737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_5620737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620737 prefixEnd_5620737 := by exact prefixLift 5620737
  have htrace : WordTrace (prefixWord ++ tailWord_5620737) baseStart_5620737 baseEnd_5620737 := by
    simpa [prefixWord, tailWord_5620737, baseEnd_5620737] using wordTrace_append hprefix tailTrace_5620737
  have hstable : (prefixWord ++ tailWord_5620737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620737).length < 2 ^ (prefixWord ++ tailWord_5620737).sum := by decide
  have hdescent : baseEnd_5620737 < baseStart_5620737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620767 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 4, 4]
def baseStart_5620767 : Nat := 118140960795 + 5620767 * 2 ^ 59
def prefixEnd_5620767 : Nat := 4983230072969 + 3 ^ 40 * 5620767 * 2
def baseEnd_5620767 : Nat := 962051705976705152321023

theorem tailTrace_5620767 : CollatzResearch.WordTrace tailWord_5620767 prefixEnd_5620767 962051705976705152321023 := by
  unfold tailWord_5620767
  simp only [CollatzResearch.WordTrace]
  refine ⟨205006214427928584423140555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136670809618619056282093703 205006214427928584423140555)
  ·
    refine ⟨307509321641892876634710833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205006214427928584423140555 307509321641892876634710833)
    ·
      refine ⟨230631991231419657476033125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307509321641892876634710833 230631991231419657476033125)
      ·
        refine ⟨43243498355891185776756211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230631991231419657476033125 43243498355891185776756211)
        ·
          refine ⟨64865247533836778665134317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43243498355891185776756211 64865247533836778665134317)
          ·
            refine ⟨24324467825188791999425369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64865247533836778665134317 24324467825188791999425369)
            ·
              refine ⟨18243350868891593999569027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24324467825188791999425369 18243350868891593999569027)
              ·
                refine ⟨27365026303337390999353541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18243350868891593999569027 27365026303337390999353541)
                ·
                  refine ⟨5130942431875760812378789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27365026303337390999353541 5130942431875760812378789)
                  ·
                    refine ⟨962051705976705152321023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5130942431875760812378789 962051705976705152321023)
                    ·
                      rfl

theorem cell23_5620767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 4].length) (baseStart_5620767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620767 prefixEnd_5620767 := by exact prefixLift 5620767
  have htrace : WordTrace (prefixWord ++ tailWord_5620767) baseStart_5620767 baseEnd_5620767 := by
    simpa [prefixWord, tailWord_5620767, baseEnd_5620767] using wordTrace_append hprefix tailTrace_5620767
  have hstable : (prefixWord ++ tailWord_5620767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620767).length < 2 ^ (prefixWord ++ tailWord_5620767).sum := by decide
  have hdescent : baseEnd_5620767 < baseStart_5620767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620768 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 3, 1, 3]
def baseStart_5620768 : Nat := 118140960795 + 5620768 * 2 ^ 59
def prefixEnd_5620768 : Nat := 4983230072969 + 3 ^ 40 * 5620768 * 2
def baseEnd_5620768 : Nat := 2886155631410769953050565

theorem tailTrace_5620768 : CollatzResearch.WordTrace tailWord_5620768 prefixEnd_5620768 2886155631410769953050565 := by
  unfold tailWord_5620768
  simp only [CollatzResearch.WordTrace]
  refine ⟨102503125450462480796963479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136670833933949974395951305 102503125450462480796963479)
  ·
    refine ⟨153754688175693721195445219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102503125450462480796963479 153754688175693721195445219)
    ·
      refine ⟨230632032263540581793167829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153754688175693721195445219 230632032263540581793167829)
      ·
        refine ⟨5405438256176732385777371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 230632032263540581793167829 5405438256176732385777371)
        ·
          refine ⟨8108157384265098578666057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5405438256176732385777371 8108157384265098578666057)
          ·
            refine ⟨6081118038198823933999543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8108157384265098578666057 6081118038198823933999543)
            ·
              refine ⟨9121677057298235900999315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6081118038198823933999543 9121677057298235900999315)
              ·
                refine ⟨13682515585947353851498973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9121677057298235900999315 13682515585947353851498973)
                ·
                  refine ⟨5130943344730257694312115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13682515585947353851498973 5130943344730257694312115)
                  ·
                    refine ⟨7696415017095386541468173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5130943344730257694312115 7696415017095386541468173)
                    ·
                      refine ⟨2886155631410769953050565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7696415017095386541468173 2886155631410769953050565)
                      ·
                        rfl

theorem cell23_5620768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_5620768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620768 prefixEnd_5620768 := by exact prefixLift 5620768
  have htrace : WordTrace (prefixWord ++ tailWord_5620768) baseStart_5620768 baseEnd_5620768 := by
    simpa [prefixWord, tailWord_5620768, baseEnd_5620768] using wordTrace_append hprefix tailTrace_5620768
  have hstable : (prefixWord ++ tailWord_5620768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620768).length < 2 ^ (prefixWord ++ tailWord_5620768).sum := by decide
  have hdescent : baseEnd_5620768 < baseStart_5620768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620780 : List Nat := [2, 2, 1, 1, 1, 2, 6, 8]
def baseStart_5620780 : Nat := 118140960795 + 5620780 * 2 ^ 59
def prefixEnd_5620780 : Nat := 4983230072969 + 3 ^ 40 * 5620780 * 2
def baseEnd_5620780 : Nat := 106894881228837922448167

theorem tailTrace_5620780 : CollatzResearch.WordTrace tailWord_5620780 prefixEnd_5620780 106894881228837922448167 := by
  unfold tailWord_5620780
  simp only [CollatzResearch.WordTrace]
  refine ⟨102503344288440743821681897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136671125717920991762242529 102503344288440743821681897)
  ·
    refine ⟨76877508216330557866261423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102503344288440743821681897 76877508216330557866261423)
    ·
      refine ⟨115316262324495836799392135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76877508216330557866261423 115316262324495836799392135)
      ·
        refine ⟨172974393486743755199088203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115316262324495836799392135 172974393486743755199088203)
        ·
          refine ⟨259461590230115632798632305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172974393486743755199088203 259461590230115632798632305)
          ·
            refine ⟨194596192672586724598974229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259461590230115632798632305 194596192672586724598974229)
            ·
              refine ⟨9121696531527502715576917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 194596192672586724598974229 9121696531527502715576917)
              ·
                refine ⟨106894881228837922448167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9121696531527502715576917 106894881228837922448167)
                ·
                  rfl

theorem cell23_5620780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 8].length) (baseStart_5620780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620780 prefixEnd_5620780 := by exact prefixLift 5620780
  have htrace : WordTrace (prefixWord ++ tailWord_5620780) baseStart_5620780 baseEnd_5620780 := by
    simpa [prefixWord, tailWord_5620780, baseEnd_5620780] using wordTrace_append hprefix tailTrace_5620780
  have hstable : (prefixWord ++ tailWord_5620780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620780).length < 2 ^ (prefixWord ++ tailWord_5620780).sum := by decide
  have hdescent : baseEnd_5620780 < baseStart_5620780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620794 : List Nat := [3, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3]
def baseStart_5620794 : Nat := 118140960795 + 5620794 * 2 ^ 59
def prefixEnd_5620794 : Nat := 4983230072969 + 3 ^ 40 * 5620794 * 2
def baseEnd_5620794 : Nat := 2886168981907786851325445

theorem tailTrace_5620794 : CollatzResearch.WordTrace tailWord_5620794 prefixEnd_5620794 2886168981907786851325445 := by
  unfold tailWord_5620794
  simp only [CollatzResearch.WordTrace]
  refine ⟨51251799799707692008593359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136671466132553845356248957 51251799799707692008593359)
  ·
    refine ⟨76877699699561538012890039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51251799799707692008593359 76877699699561538012890039)
    ·
      refine ⟨115316549549342307019335059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76877699699561538012890039 115316549549342307019335059)
      ·
        refine ⟨172974824324013460529002589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115316549549342307019335059 172974824324013460529002589)
        ·
          refine ⟨64865559121505047698375971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172974824324013460529002589 64865559121505047698375971)
          ·
            refine ⟨97298338682257571547563957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64865559121505047698375971 97298338682257571547563957)
            ·
              refine ⟨9121719251461647332584121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97298338682257571547563957 9121719251461647332584121)
              ·
                refine ⟨6841289438596235499438091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9121719251461647332584121 6841289438596235499438091)
                ·
                  refine ⟨10261934157894353249157137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6841289438596235499438091 10261934157894353249157137)
                  ·
                    refine ⟨7696450618420764936867853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10261934157894353249157137 7696450618420764936867853)
                    ·
                      refine ⟨2886168981907786851325445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7696450618420764936867853 2886168981907786851325445)
                      ·
                        rfl

theorem cell23_5620794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_5620794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620794 prefixEnd_5620794 := by exact prefixLift 5620794
  have htrace : WordTrace (prefixWord ++ tailWord_5620794) baseStart_5620794 baseEnd_5620794 := by
    simpa [prefixWord, tailWord_5620794, baseEnd_5620794] using wordTrace_append hprefix tailTrace_5620794
  have hstable : (prefixWord ++ tailWord_5620794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620794).length < 2 ^ (prefixWord ++ tailWord_5620794).sum := by decide
  have hdescent : baseEnd_5620794 < baseStart_5620794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620807 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 3]
def baseStart_5620807 : Nat := 118140960795 + 5620807 * 2 ^ 59
def prefixEnd_5620807 : Nat := 4983230072969 + 3 ^ 40 * 5620807 * 2
def baseEnd_5620807 : Nat := 2886175657156295300462885

theorem tailTrace_5620807 : CollatzResearch.WordTrace tailWord_5620807 prefixEnd_5620807 2886175657156295300462885 := by
  unfold tailWord_5620807
  simp only [CollatzResearch.WordTrace]
  refine ⟨205007673347783671254596675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136671782231855780836397783 205007673347783671254596675)
  ·
    refine ⟨307511510021675506881895013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205007673347783671254596675 307511510021675506881895013)
    ·
      refine ⟨57658408129064157540355315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 307511510021675506881895013 57658408129064157540355315)
      ·
        refine ⟨86487612193596236310532973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57658408129064157540355315 86487612193596236310532973)
        ·
          refine ⟨32432854572598588616449865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86487612193596236310532973 32432854572598588616449865)
          ·
            refine ⟨24324640929448941462337399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32432854572598588616449865 24324640929448941462337399)
            ·
              refine ⟨36486961394173412193506099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24324640929448941462337399 36486961394173412193506099)
              ·
                refine ⟨54730442091260118290259149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36486961394173412193506099 54730442091260118290259149)
                ·
                  refine ⟨20523915784222544358847181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54730442091260118290259149 20523915784222544358847181)
                  ·
                    refine ⟨7696468419083454134567693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20523915784222544358847181 7696468419083454134567693)
                    ·
                      refine ⟨2886175657156295300462885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7696468419083454134567693 2886175657156295300462885)
                      ·
                        rfl

theorem cell23_5620807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_5620807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620807 prefixEnd_5620807 := by exact prefixLift 5620807
  have htrace : WordTrace (prefixWord ++ tailWord_5620807) baseStart_5620807 baseEnd_5620807 := by
    simpa [prefixWord, tailWord_5620807, baseEnd_5620807] using wordTrace_append hprefix tailTrace_5620807
  have hstable : (prefixWord ++ tailWord_5620807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620807).length < 2 ^ (prefixWord ++ tailWord_5620807).sum := by decide
  have hdescent : baseEnd_5620807 < baseStart_5620807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620864 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 1, 4, 2]
def baseStart_5620864 : Nat := 118140960795 + 5620864 * 2 ^ 59
def prefixEnd_5620864 : Nat := 4983230072969 + 3 ^ 40 * 5620864 * 2
def baseEnd_5620864 : Nat := 2886204925553601577450123

theorem tailTrace_5620864 : CollatzResearch.WordTrace tailWord_5620864 prefixEnd_5620864 2886204925553601577450123 := by
  unfold tailWord_5620864
  simp only [CollatzResearch.WordTrace]
  refine ⟨102504876154288584994710823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136673168205718113326281097 102504876154288584994710823)
  ·
    refine ⟨153757314231432877492066235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102504876154288584994710823 153757314231432877492066235)
    ·
      refine ⟨230635971347149316238099353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153757314231432877492066235 230635971347149316238099353)
      ·
        refine ⟨172976978510361987178574515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230635971347149316238099353 172976978510361987178574515)
        ·
          refine ⟨259465467765542980767861773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172976978510361987178574515 259465467765542980767861773)
          ·
            refine ⟨97299550412078617787948165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 259465467765542980767861773 97299550412078617787948165)
            ·
              refine ⟨18243665702264740835240281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97299550412078617787948165 18243665702264740835240281)
              ·
                refine ⟨13682749276698555626430211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18243665702264740835240281 13682749276698555626430211)
                ·
                  refine ⟨20524123915047833439645317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13682749276698555626430211 20524123915047833439645317)
                  ·
                    refine ⟨3848273234071468769933497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20524123915047833439645317 3848273234071468769933497)
                    ·
                      refine ⟨2886204925553601577450123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3848273234071468769933497 2886204925553601577450123)
                      ·
                        rfl

theorem cell23_5620864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 1, 4, 2].length) (baseStart_5620864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620864 prefixEnd_5620864 := by exact prefixLift 5620864
  have htrace : WordTrace (prefixWord ++ tailWord_5620864) baseStart_5620864 baseEnd_5620864 := by
    simpa [prefixWord, tailWord_5620864, baseEnd_5620864] using wordTrace_append hprefix tailTrace_5620864
  have hstable : (prefixWord ++ tailWord_5620864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620864).length < 2 ^ (prefixWord ++ tailWord_5620864).sum := by decide
  have hdescent : baseEnd_5620864 < baseStart_5620864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620868 : List Nat := [2, 3, 2, 1, 2, 2, 4, 1, 1, 3, 2]
def baseStart_5620868 : Nat := 118140960795 + 5620868 * 2 ^ 59
def prefixEnd_5620868 : Nat := 4983230072969 + 3 ^ 40 * 5620868 * 2
def baseEnd_5620868 : Nat := 2886206979476219561800105

theorem tailTrace_5620868 : CollatzResearch.WordTrace tailWord_5620868 prefixEnd_5620868 2886206979476219561800105 := by
  unfold tailWord_5620868
  simp only [CollatzResearch.WordTrace]
  refine ⟨102504949100281339336283629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136673265467041785781711505 102504949100281339336283629)
  ·
    refine ⟨38439355912605502251106361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102504949100281339336283629 38439355912605502251106361)
    ·
      refine ⟨28829516934454126688329771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38439355912605502251106361 28829516934454126688329771)
      ·
        refine ⟨43244275401681190032494657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28829516934454126688329771 43244275401681190032494657)
        ·
          refine ⟨32433206551260892524370993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43244275401681190032494657 32433206551260892524370993)
          ·
            refine ⟨24324904913445669393278245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32433206551260892524370993 24324904913445669393278245)
            ·
              refine ⟨4560919671271063011239671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24324904913445669393278245 4560919671271063011239671)
              ·
                refine ⟨6841379506906594516859507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4560919671271063011239671 6841379506906594516859507)
                ·
                  refine ⟨10262069260359891775289261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6841379506906594516859507 10262069260359891775289261)
                  ·
                    refine ⟨3848275972634959415733473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10262069260359891775289261 3848275972634959415733473)
                    ·
                      refine ⟨2886206979476219561800105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3848275972634959415733473 2886206979476219561800105)
                      ·
                        rfl

theorem cell23_5620868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_5620868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620868 prefixEnd_5620868 := by exact prefixLift 5620868
  have htrace : WordTrace (prefixWord ++ tailWord_5620868) baseStart_5620868 baseEnd_5620868 := by
    simpa [prefixWord, tailWord_5620868, baseEnd_5620868] using wordTrace_append hprefix tailTrace_5620868
  have hstable : (prefixWord ++ tailWord_5620868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620868).length < 2 ^ (prefixWord ++ tailWord_5620868).sum := by decide
  have hdescent : baseEnd_5620868 < baseStart_5620868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620880 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 9]
def baseStart_5620880 : Nat := 118140960795 + 5620880 * 2 ^ 59
def prefixEnd_5620880 : Nat := 4983230072969 + 3 ^ 40 * 5620880 * 2
def baseEnd_5620880 : Nat := 2886213141244073514850049

theorem tailTrace_5620880 : CollatzResearch.WordTrace tailWord_5620880 prefixEnd_5620880 2886213141244073514850049 := by
  unfold tailWord_5620880
  simp only [CollatzResearch.WordTrace]
  refine ⟨102505167938259602361002047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136673557251012803148002729 102505167938259602361002047)
  ·
    refine ⟨153757751907389403541503071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102505167938259602361002047 153757751907389403541503071)
    ·
      refine ⟨230636627861084105312254607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153757751907389403541503071 230636627861084105312254607)
      ·
        refine ⟨345954941791626157968381911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230636627861084105312254607 345954941791626157968381911)
        ·
          refine ⟨518932412687439236952572867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345954941791626157968381911 518932412687439236952572867)
          ·
            refine ⟨778398619031158855428859301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518932412687439236952572867 778398619031158855428859301)
            ·
              refine ⟨145949741068342285392911119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 778398619031158855428859301 145949741068342285392911119)
              ·
                refine ⟨218924611602513428089366679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145949741068342285392911119 218924611602513428089366679)
                ·
                  refine ⟨328386917403770142134050019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218924611602513428089366679 328386917403770142134050019)
                  ·
                    refine ⟨492580376105655213201075029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 328386917403770142134050019 492580376105655213201075029)
                    ·
                      refine ⟨2886213141244073514850049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 492580376105655213201075029 2886213141244073514850049)
                      ·
                        rfl

theorem cell23_5620880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_5620880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620880 prefixEnd_5620880 := by exact prefixLift 5620880
  have htrace : WordTrace (prefixWord ++ tailWord_5620880) baseStart_5620880 baseEnd_5620880 := by
    simpa [prefixWord, tailWord_5620880, baseEnd_5620880] using wordTrace_append hprefix tailTrace_5620880
  have hstable : (prefixWord ++ tailWord_5620880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620880).length < 2 ^ (prefixWord ++ tailWord_5620880).sum := by decide
  have hdescent : baseEnd_5620880 < baseStart_5620880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620887 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 7]
def baseStart_5620887 : Nat := 118140960795 + 5620887 * 2 ^ 59
def prefixEnd_5620887 : Nat := 4983230072969 + 3 ^ 40 * 5620887 * 2
def baseEnd_5620887 : Nat := 320690748400961665273613

theorem tailTrace_5620887 : CollatzResearch.WordTrace tailWord_5620887 prefixEnd_5620887 320690748400961665273613 := by
  unfold tailWord_5620887
  simp only [CollatzResearch.WordTrace]
  refine ⟨205010591187493844917508915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136673727458329229945005943 205010591187493844917508915)
  ·
    refine ⟨307515886781240767376263373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205010591187493844917508915 307515886781240767376263373)
    ·
      refine ⟨115318457542965287766098765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307515886781240767376263373 115318457542965287766098765)
      ·
        refine ⟨43244421578611982912287037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115318457542965287766098765 43244421578611982912287037)
        ·
          refine ⟨16216658091979493592107639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43244421578611982912287037 16216658091979493592107639)
          ·
            refine ⟨24324987137969240388161459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16216658091979493592107639 24324987137969240388161459)
            ·
              refine ⟨36487480706953860582242189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24324987137969240388161459 36487480706953860582242189)
              ·
                refine ⟨13682805265107697718340821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36487480706953860582242189 13682805265107697718340821)
                ·
                  refine ⟨320690748400961665273613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13682805265107697718340821 320690748400961665273613)
                  ·
                    rfl

theorem cell23_5620887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 7].length) (baseStart_5620887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620887 prefixEnd_5620887 := by exact prefixLift 5620887
  have htrace : WordTrace (prefixWord ++ tailWord_5620887) baseStart_5620887 baseEnd_5620887 := by
    simpa [prefixWord, tailWord_5620887, baseEnd_5620887] using wordTrace_append hprefix tailTrace_5620887
  have hstable : (prefixWord ++ tailWord_5620887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620887).length < 2 ^ (prefixWord ++ tailWord_5620887).sum := by decide
  have hdescent : baseEnd_5620887 < baseStart_5620887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620918 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_5620918 : Nat := 118140960795 + 5620918 * 2 ^ 59
def prefixEnd_5620918 : Nat := 4983230072969 + 3 ^ 40 * 5620918 * 2
def baseEnd_5620918 : Nat := 2886232653508944366174875

theorem tailTrace_5620918 : CollatzResearch.WordTrace tailWord_5620918 prefixEnd_5620918 2886232653508944366174875 := by
  unfold tailWord_5620918
  simp only [CollatzResearch.WordTrace]
  refine ⟨12813232615648846075742963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136674481233587691474591605 12813232615648846075742963)
  ·
    refine ⟨19219848923473269113614445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12813232615648846075742963 19219848923473269113614445)
    ·
      refine ⟨7207443346302475917605417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19219848923473269113614445 7207443346302475917605417)
      ·
        refine ⟨5405582509726856938204063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7207443346302475917605417 5405582509726856938204063)
        ·
          refine ⟨8108373764590285407306095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5405582509726856938204063 8108373764590285407306095)
          ·
            refine ⟨12162560646885428110959143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8108373764590285407306095 12162560646885428110959143)
            ·
              refine ⟨18243840970328142166438715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12162560646885428110959143 18243840970328142166438715)
              ·
                refine ⟨27365761455492213249658073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18243840970328142166438715 27365761455492213249658073)
                ·
                  refine ⟨20524321091619159937243555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27365761455492213249658073 20524321091619159937243555)
                  ·
                    refine ⟨30786481637428739905865333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20524321091619159937243555 30786481637428739905865333)
                    ·
                      refine ⟨2886232653508944366174875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30786481637428739905865333 2886232653508944366174875)
                      ·
                        rfl

theorem cell23_5620918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_5620918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620918 prefixEnd_5620918 := by exact prefixLift 5620918
  have htrace : WordTrace (prefixWord ++ tailWord_5620918) baseStart_5620918 baseEnd_5620918 := by
    simpa [prefixWord, tailWord_5620918, baseEnd_5620918] using wordTrace_append hprefix tailTrace_5620918
  have hstable : (prefixWord ++ tailWord_5620918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620918).length < 2 ^ (prefixWord ++ tailWord_5620918).sum := by decide
  have hdescent : baseEnd_5620918 < baseStart_5620918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620921 : List Nat := [1, 2, 1, 4, 1, 5, 1, 3, 5]
def baseStart_5620921 : Nat := 118140960795 + 5620921 * 2 ^ 59
def prefixEnd_5620921 : Nat := 4983230072969 + 3 ^ 40 * 5620921 * 2
def baseEnd_5620921 : Nat := 320692688216767539381929

theorem tailTrace_5620921 : CollatzResearch.WordTrace tailWord_5620921 prefixEnd_5620921 320692688216767539381929 := by
  unfold tailWord_5620921
  simp only [CollatzResearch.WordTrace]
  refine ⟨205011831269370668724246617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136674554179580445816164411 205011831269370668724246617)
  ·
    refine ⟨153758873452028001543184963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205011831269370668724246617 153758873452028001543184963)
    ·
      refine ⟨230638310178042002314777445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153758873452028001543184963 230638310178042002314777445)
      ·
        refine ⟨43244683158382875434020771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230638310178042002314777445 43244683158382875434020771)
        ·
          refine ⟨64867024737574313151031157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43244683158382875434020771 64867024737574313151031157)
          ·
            refine ⟨6081283569147591857909171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64867024737574313151031157 6081283569147591857909171)
            ·
              refine ⟨9121925353721387786863757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6081283569147591857909171 9121925353721387786863757)
              ·
                refine ⟨3420722007645520420073909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9121925353721387786863757 3420722007645520420073909)
                ·
                  refine ⟨320692688216767539381929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3420722007645520420073909 320692688216767539381929)
                  ·
                    rfl

theorem cell23_5620921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 5].length) (baseStart_5620921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620921 prefixEnd_5620921 := by exact prefixLift 5620921
  have htrace : WordTrace (prefixWord ++ tailWord_5620921) baseStart_5620921 baseEnd_5620921 := by
    simpa [prefixWord, tailWord_5620921, baseEnd_5620921] using wordTrace_append hprefix tailTrace_5620921
  have hstable : (prefixWord ++ tailWord_5620921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620921).length < 2 ^ (prefixWord ++ tailWord_5620921).sum := by decide
  have hdescent : baseEnd_5620921 < baseStart_5620921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620954 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2]
def baseStart_5620954 : Nat := 118140960795 + 5620954 * 2 ^ 59
def prefixEnd_5620954 : Nat := 4983230072969 + 3 ^ 40 * 5620954 * 2
def baseEnd_5620954 : Nat := 2886251138812506225324709

theorem tailTrace_5620954 : CollatzResearch.WordTrace tailWord_5620954 prefixEnd_5620954 2886251138812506225324709 := by
  unfold tailWord_5620954
  simp only [CollatzResearch.WordTrace]
  refine ⟨51253258719562778840049479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136675356585500743573465277 51253258719562778840049479)
  ·
    refine ⟨76879888079344168260074219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51253258719562778840049479 76879888079344168260074219)
    ·
      refine ⟨115319832119016252390111329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76879888079344168260074219 115319832119016252390111329)
      ·
        refine ⟨86489874089262189292583497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115319832119016252390111329 86489874089262189292583497)
        ·
          refine ⟨64867405566946641969437623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86489874089262189292583497 64867405566946641969437623)
          ·
            refine ⟨97301108350419962954156435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64867405566946641969437623 97301108350419962954156435)
            ·
              refine ⟨145951662525629944431234653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97301108350419962954156435 145951662525629944431234653)
              ·
                refine ⟨54731873447111229161712995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145951662525629944431234653 54731873447111229161712995)
                ·
                  refine ⟨82097810170666843742569493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54731873447111229161712995 82097810170666843742569493)
                  ·
                    refine ⟨3848334851750008300432945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82097810170666843742569493 3848334851750008300432945)
                    ·
                      refine ⟨2886251138812506225324709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3848334851750008300432945 2886251138812506225324709)
                      ·
                        rfl

theorem cell23_5620954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_5620954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620954 prefixEnd_5620954 := by exact prefixLift 5620954
  have htrace : WordTrace (prefixWord ++ tailWord_5620954) baseStart_5620954 baseEnd_5620954 := by
    simpa [prefixWord, tailWord_5620954, baseEnd_5620954] using wordTrace_append hprefix tailTrace_5620954
  have hstable : (prefixWord ++ tailWord_5620954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620954).length < 2 ^ (prefixWord ++ tailWord_5620954).sum := by decide
  have hdescent : baseEnd_5620954 < baseStart_5620954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620964 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 3, 4]
def baseStart_5620964 : Nat := 118140960795 + 5620964 * 2 ^ 59
def prefixEnd_5620964 : Nat := 4983230072969 + 3 ^ 40 * 5620964 * 2
def baseEnd_5620964 : Nat := 962085424539683728733221

theorem tailTrace_5620964 : CollatzResearch.WordTrace tailWord_5620964 prefixEnd_5620964 962085424539683728733221 := by
  unfold tailWord_5620964
  simp only [CollatzResearch.WordTrace]
  refine ⟨102506699804107443534030973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136675599738809924712041297 102506699804107443534030973)
  ·
    refine ⟨38440012426540291325261615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102506699804107443534030973 38440012426540291325261615)
    ·
      refine ⟨57660018639810436987892423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38440012426540291325261615 57660018639810436987892423)
      ·
        refine ⟨86490027959715655481838635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57660018639810436987892423 86490027959715655481838635)
        ·
          refine ⟨129735041939573483222757953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86490027959715655481838635 129735041939573483222757953)
          ·
            refine ⟨97301281454680112417068465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129735041939573483222757953 97301281454680112417068465)
            ·
              refine ⟨72975961091010084312801349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97301281454680112417068465 72975961091010084312801349)
              ·
                refine ⟨13682992704564390808650253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72975961091010084312801349 13682992704564390808650253)
                ·
                  refine ⟨5131122264211646553243845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13682992704564390808650253 5131122264211646553243845)
                  ·
                    refine ⟨962085424539683728733221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5131122264211646553243845 962085424539683728733221)
                    ·
                      rfl

theorem cell23_5620964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_5620964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620964 prefixEnd_5620964 := by exact prefixLift 5620964
  have htrace : WordTrace (prefixWord ++ tailWord_5620964) baseStart_5620964 baseEnd_5620964 := by
    simpa [prefixWord, tailWord_5620964, baseEnd_5620964] using wordTrace_append hprefix tailTrace_5620964
  have hstable : (prefixWord ++ tailWord_5620964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620964).length < 2 ^ (prefixWord ++ tailWord_5620964).sum := by decide
  have hdescent : baseEnd_5620964 < baseStart_5620964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620974 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_5620974 : Nat := 118140960795 + 5620974 * 2 ^ 59
def prefixEnd_5620974 : Nat := 4983230072969 + 3 ^ 40 * 5620974 * 2
def baseEnd_5620974 : Nat := 2886261408425596147074617

theorem tailTrace_5620974 : CollatzResearch.WordTrace tailWord_5620974 prefixEnd_5620974 2886261408425596147074617 := by
  unfold tailWord_5620974
  simp only [CollatzResearch.WordTrace]
  refine ⟨25626720542272332346990747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136675842892119105850617317 25626720542272332346990747)
  ·
    refine ⟨38440080813408498520486121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25626720542272332346990747 38440080813408498520486121)
    ·
      refine ⟨28830060610056373890364591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38440080813408498520486121 28830060610056373890364591)
      ·
        refine ⟨43245090915084560835546887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28830060610056373890364591 43245090915084560835546887)
        ·
          refine ⟨64867636372626841253320331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43245090915084560835546887 64867636372626841253320331)
          ·
            refine ⟨97301454558940261879980497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64867636372626841253320331 97301454558940261879980497)
            ·
              refine ⟨72976090919205196409985373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97301454558940261879980497 72976090919205196409985373)
              ·
                refine ⟨27366034094701948653744515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72976090919205196409985373 27366034094701948653744515)
                ·
                  refine ⟨41049051142052922980616773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27366034094701948653744515 41049051142052922980616773)
                  ·
                    refine ⟨7696697089134923058865645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41049051142052922980616773 7696697089134923058865645)
                    ·
                      refine ⟨2886261408425596147074617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7696697089134923058865645 2886261408425596147074617)
                      ·
                        rfl

theorem cell23_5620974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_5620974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620974 prefixEnd_5620974 := by exact prefixLift 5620974
  have htrace : WordTrace (prefixWord ++ tailWord_5620974) baseStart_5620974 baseEnd_5620974 := by
    simpa [prefixWord, tailWord_5620974, baseEnd_5620974] using wordTrace_append hprefix tailTrace_5620974
  have hstable : (prefixWord ++ tailWord_5620974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620974).length < 2 ^ (prefixWord ++ tailWord_5620974).sum := by decide
  have hdescent : baseEnd_5620974 < baseStart_5620974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5620997 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 1, 2, 6]
def baseStart_5620997 : Nat := 118140960795 + 5620997 * 2 ^ 59
def prefixEnd_5620997 : Nat := 4983230072969 + 3 ^ 40 * 5620997 * 2
def baseEnd_5620997 : Nat := 2886273218480649557087011

theorem tailTrace_5620997 : CollatzResearch.WordTrace tailWord_5620997 prefixEnd_5620997 2886273218480649557087011 := by
  unfold tailWord_5620997
  simp only [CollatzResearch.WordTrace]
  refine ⟨205014603217095333704013245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136676402144730222469342163 205014603217095333704013245)
  ·
    refine ⟨76880476206410750139004967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205014603217095333704013245 76880476206410750139004967)
    ·
      refine ⟨115320714309616125208507451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76880476206410750139004967 115320714309616125208507451)
      ·
        refine ⟨172981071464424187812761177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115320714309616125208507451 172981071464424187812761177)
        ·
          refine ⟨129735803598318140859570883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172981071464424187812761177 129735803598318140859570883)
          ·
            refine ⟨194603705397477211289356325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129735803598318140859570883 194603705397477211289356325)
            ·
              refine ⟨36488194762026977116754311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194603705397477211289356325 36488194762026977116754311)
              ·
                refine ⟨54732292143040465675131467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36488194762026977116754311 54732292143040465675131467)
                ·
                  refine ⟨82098438214560698512697201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54732292143040465675131467 82098438214560698512697201)
                  ·
                    refine ⟨61573828660920523884522901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82098438214560698512697201 61573828660920523884522901)
                    ·
                      refine ⟨2886273218480649557087011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61573828660920523884522901 2886273218480649557087011)
                      ·
                        rfl

theorem cell23_5620997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_5620997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5620997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5620997 prefixEnd_5620997 := by exact prefixLift 5620997
  have htrace : WordTrace (prefixWord ++ tailWord_5620997) baseStart_5620997 baseEnd_5620997 := by
    simpa [prefixWord, tailWord_5620997, baseEnd_5620997] using wordTrace_append hprefix tailTrace_5620997
  have hstable : (prefixWord ++ tailWord_5620997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5620997).length < 2 ^ (prefixWord ++ tailWord_5620997).sum := by decide
  have hdescent : baseEnd_5620997 < baseStart_5620997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5620997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621022 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_5621022 : Nat := 118140960795 + 5621022 * 2 ^ 59
def prefixEnd_5621022 : Nat := 4983230072969 + 3 ^ 40 * 5621022 * 2
def baseEnd_5621022 : Nat := 2886286055497011959274397

theorem tailTrace_5621022 : CollatzResearch.WordTrace tailWord_5621022 prefixEnd_5621022 2886286055497011959274397 := by
  unfold tailWord_5621022
  simp only [CollatzResearch.WordTrace]
  refine ⟨25626939380250595371709165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136677010028003175315782213 25626939380250595371709165)
  ·
    refine ⟨9610102267593973264390937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25626939380250595371709165 9610102267593973264390937)
    ·
      refine ⟨7207576700695479948293203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9610102267593973264390937 7207576700695479948293203)
      ·
        refine ⟨10811365051043219922439805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7207576700695479948293203 10811365051043219922439805)
        ·
          refine ⟨4054261894141207470914927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10811365051043219922439805 4054261894141207470914927)
          ·
            refine ⟨6081392841211811206372391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4054261894141207470914927 6081392841211811206372391)
            ·
              refine ⟨9122089261817716809558587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6081392841211811206372391 9122089261817716809558587)
              ·
                refine ⟨13683133892726575214337881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9122089261817716809558587 13683133892726575214337881)
                ·
                  refine ⟨10262350419544931410753411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13683133892726575214337881 10262350419544931410753411)
                  ·
                    refine ⟨15393525629317397116130117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10262350419544931410753411 15393525629317397116130117)
                    ·
                      refine ⟨2886286055497011959274397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15393525629317397116130117 2886286055497011959274397)
                      ·
                        rfl

theorem cell23_5621022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_5621022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621022 prefixEnd_5621022 := by exact prefixLift 5621022
  have htrace : WordTrace (prefixWord ++ tailWord_5621022) baseStart_5621022 baseEnd_5621022 := by
    simpa [prefixWord, tailWord_5621022, baseEnd_5621022] using wordTrace_append hprefix tailTrace_5621022
  have hstable : (prefixWord ++ tailWord_5621022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621022).length < 2 ^ (prefixWord ++ tailWord_5621022).sum := by decide
  have hdescent : baseEnd_5621022 < baseStart_5621022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621041 : List Nat := [1, 2, 2, 3, 3, 2, 1, 3, 1, 5]
def baseStart_5621041 : Nat := 118140960795 + 5621041 * 2 ^ 59
def prefixEnd_5621041 : Nat := 4983230072969 + 3 ^ 40 * 5621041 * 2
def baseEnd_5621041 : Nat := 962098603876482461645603

theorem tailTrace_5621041 : CollatzResearch.WordTrace tailWord_5621041 prefixEnd_5621041 962098603876482461645603 := by
  unfold tailWord_5621041
  simp only [CollatzResearch.WordTrace]
  refine ⟨205016208028935929218614977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136677472019290619479076651 205016208028935929218614977)
  ·
    refine ⟨153762156021701946913961233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205016208028935929218614977 153762156021701946913961233)
    ·
      refine ⟨115321617016276460185470925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153762156021701946913961233 115321617016276460185470925)
      ·
        refine ⟨43245606381103672569551597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115321617016276460185470925 43245606381103672569551597)
        ·
          refine ⟨16217102392913877213581849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43245606381103672569551597 16217102392913877213581849)
          ·
            refine ⟨12162826794685407910186387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16217102392913877213581849 12162826794685407910186387)
            ·
              refine ⟨18244240192028111865279581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12162826794685407910186387 18244240192028111865279581)
              ·
                refine ⟨6841590072010541949479843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18244240192028111865279581 6841590072010541949479843)
                ·
                  refine ⟨10262385108015812924219765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6841590072010541949479843 10262385108015812924219765)
                  ·
                    refine ⟨962098603876482461645603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10262385108015812924219765 962098603876482461645603)
                    ·
                      rfl

theorem cell23_5621041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_5621041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621041 prefixEnd_5621041 := by exact prefixLift 5621041
  have htrace : WordTrace (prefixWord ++ tailWord_5621041) baseStart_5621041 baseEnd_5621041 := by
    simpa [prefixWord, tailWord_5621041, baseEnd_5621041] using wordTrace_append hprefix tailTrace_5621041
  have hstable : (prefixWord ++ tailWord_5621041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621041).length < 2 ^ (prefixWord ++ tailWord_5621041).sum := by decide
  have hdescent : baseEnd_5621041 < baseStart_5621041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621062 : List Nat := [6, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_5621062 : Nat := 118140960795 + 5621062 * 2 ^ 59
def prefixEnd_5621062 : Nat := 4983230072969 + 3 ^ 40 * 5621062 * 2
def baseEnd_5621062 : Nat := 320700732747021311419357

theorem tailTrace_5621062 : CollatzResearch.WordTrace tailWord_5621062 prefixEnd_5621062 320700732747021311419357 := by
  unfold tailWord_5621062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6406780436308120306410295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 136677982641239899870086293 6406780436308120306410295)
  ·
    refine ⟨9610170654462180459615443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6406780436308120306410295 9610170654462180459615443)
    ·
      refine ⟨14415255981693270689423165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9610170654462180459615443 14415255981693270689423165)
      ·
        refine ⟨5405720993134976508533687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14415255981693270689423165 5405720993134976508533687)
        ·
          refine ⟨8108581489702464762800531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5405720993134976508533687 8108581489702464762800531)
          ·
            refine ⟨12162872234553697144200797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8108581489702464762800531 12162872234553697144200797)
            ·
              refine ⟨4561077087957636429075299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12162872234553697144200797 4561077087957636429075299)
              ·
                refine ⟨6841615631936454643612949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4561077087957636429075299 6841615631936454643612949)
                ·
                  refine ⟨320700732747021311419357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6841615631936454643612949 320700732747021311419357)
                  ·
                    rfl

theorem cell23_5621062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_5621062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621062 prefixEnd_5621062 := by exact prefixLift 5621062
  have htrace : WordTrace (prefixWord ++ tailWord_5621062) baseStart_5621062 baseEnd_5621062 := by
    simpa [prefixWord, tailWord_5621062, baseEnd_5621062] using wordTrace_append hprefix tailTrace_5621062
  have hstable : (prefixWord ++ tailWord_5621062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621062).length < 2 ^ (prefixWord ++ tailWord_5621062).sum := by decide
  have hdescent : baseEnd_5621062 < baseStart_5621062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621081 : List Nat := [1, 2, 1, 2, 2, 2, 3, 4, 1, 2, 3]
def baseStart_5621081 : Nat := 118140960795 + 5621081 * 2 ^ 59
def prefixEnd_5621081 : Nat := 4983230072969 + 3 ^ 40 * 5621081 * 2
def baseEnd_5621081 : Nat := 2886316350855627228436625

theorem tailTrace_5621081 : CollatzResearch.WordTrace tailWord_5621081 prefixEnd_5621081 2886316350855627228436625 := by
  unfold tailWord_5621081
  simp only [CollatzResearch.WordTrace]
  refine ⟨205017666948791016050071097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136678444632527344033380731 205017666948791016050071097)
  ·
    refine ⟨153763250211593262037553323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205017666948791016050071097 153763250211593262037553323)
    ·
      refine ⟨230644875317389893056329985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153763250211593262037553323 230644875317389893056329985)
      ·
        refine ⟨172983656488042419792247489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230644875317389893056329985 172983656488042419792247489)
        ·
          refine ⟨129737742366031814844185617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172983656488042419792247489 129737742366031814844185617)
          ·
            refine ⟨97303306774523861133139213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129737742366031814844185617 97303306774523861133139213)
            ·
              refine ⟨36488740040446447924927205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97303306774523861133139213 36488740040446447924927205)
              ·
                refine ⟨6841638757583708985923851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36488740040446447924927205 6841638757583708985923851)
                ·
                  refine ⟨10262458136375563478885777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6841638757583708985923851 10262458136375563478885777)
                  ·
                    refine ⟨7696843602281672609164333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10262458136375563478885777 7696843602281672609164333)
                    ·
                      refine ⟨2886316350855627228436625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7696843602281672609164333 2886316350855627228436625)
                      ·
                        rfl

theorem cell23_5621081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_5621081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621081 prefixEnd_5621081 := by exact prefixLift 5621081
  have htrace : WordTrace (prefixWord ++ tailWord_5621081) baseStart_5621081 baseEnd_5621081 := by
    simpa [prefixWord, tailWord_5621081, baseEnd_5621081] using wordTrace_append hprefix tailTrace_5621081
  have hstable : (prefixWord ++ tailWord_5621081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621081).length < 2 ^ (prefixWord ++ tailWord_5621081).sum := by decide
  have hdescent : baseEnd_5621081 < baseStart_5621081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621098 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_5621098 : Nat := 118140960795 + 5621098 * 2 ^ 59
def prefixEnd_5621098 : Nat := 4983230072969 + 3 ^ 40 * 5621098 * 2
def baseEnd_5621098 : Nat := 2886325080026753661924047

theorem tailTrace_5621098 : CollatzResearch.WordTrace tailWord_5621098 prefixEnd_5621098 2886325080026753661924047 := by
  unfold tailWord_5621098
  simp only [CollatzResearch.WordTrace]
  refine ⟨51254571747432356988359987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136678857993152951968959965 51254571747432356988359987)
  ·
    refine ⟨76881857621148535482539981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51254571747432356988359987 76881857621148535482539981)
    ·
      refine ⟨28830696607930700805952493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76881857621148535482539981 28830696607930700805952493)
      ·
        refine ⟨10811511227974012802232185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28830696607930700805952493 10811511227974012802232185)
        ·
          refine ⟨8108633420980509601674139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10811511227974012802232185 8108633420980509601674139)
          ·
            refine ⟨12162950131470764402511209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8108633420980509601674139 12162950131470764402511209)
            ·
              refine ⟨9122212598603073301883407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12162950131470764402511209 9122212598603073301883407)
              ·
                refine ⟨13683318897904609952825111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9122212598603073301883407 13683318897904609952825111)
                ·
                  refine ⟨20524978346856914929237667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13683318897904609952825111 20524978346856914929237667)
                  ·
                    refine ⟨30787467520285372393856501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20524978346856914929237667 30787467520285372393856501)
                    ·
                      refine ⟨2886325080026753661924047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30787467520285372393856501 2886325080026753661924047)
                      ·
                        rfl

theorem cell23_5621098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_5621098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621098 prefixEnd_5621098 := by exact prefixLift 5621098
  have htrace : WordTrace (prefixWord ++ tailWord_5621098) baseStart_5621098 baseEnd_5621098 := by
    simpa [prefixWord, tailWord_5621098, baseEnd_5621098] using wordTrace_append hprefix tailTrace_5621098
  have hstable : (prefixWord ++ tailWord_5621098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621098).length < 2 ^ (prefixWord ++ tailWord_5621098).sum := by decide
  have hdescent : baseEnd_5621098 < baseStart_5621098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621111 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 4, 1, 3]
def baseStart_5621111 : Nat := 118140960795 + 5621111 * 2 ^ 59
def prefixEnd_5621111 : Nat := 4983230072969 + 3 ^ 40 * 5621111 * 2
def baseEnd_5621111 : Nat := 2886331755275262111061487

theorem tailTrace_5621111 : CollatzResearch.WordTrace tailWord_5621111 prefixEnd_5621111 2886331755275262111061487 := by
  unfold tailWord_5621111
  simp only [CollatzResearch.WordTrace]
  refine ⟨205018761138682331173663187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136679174092454887449108791 205018761138682331173663187)
  ·
    refine ⟨307528141708023496760494781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205018761138682331173663187 307528141708023496760494781)
    ·
      refine ⟨115323053140508811285185543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307528141708023496760494781 115323053140508811285185543)
      ·
        refine ⟨172984579710763216927778315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115323053140508811285185543 172984579710763216927778315)
        ·
          refine ⟨259476869566144825391667473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172984579710763216927778315 259476869566144825391667473)
          ·
            refine ⟨194607652174608619043750605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259476869566144825391667473 194607652174608619043750605)
            ·
              refine ⟨72977869565478232141406477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194607652174608619043750605 72977869565478232141406477)
              ·
                refine ⟨27366701087054337053027429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72977869565478232141406477 27366701087054337053027429)
                ·
                  refine ⟨5131256453822688197442643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27366701087054337053027429 5131256453822688197442643)
                  ·
                    refine ⟨7696884680734032296163965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5131256453822688197442643 7696884680734032296163965)
                    ·
                      refine ⟨2886331755275262111061487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7696884680734032296163965 2886331755275262111061487)
                      ·
                        rfl

theorem cell23_5621111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_5621111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621111 prefixEnd_5621111 := by exact prefixLift 5621111
  have htrace : WordTrace (prefixWord ++ tailWord_5621111) baseStart_5621111 baseEnd_5621111 := by
    simpa [prefixWord, tailWord_5621111, baseEnd_5621111] using wordTrace_append hprefix tailTrace_5621111
  have hstable : (prefixWord ++ tailWord_5621111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621111).length < 2 ^ (prefixWord ++ tailWord_5621111).sum := by decide
  have hdescent : baseEnd_5621111 < baseStart_5621111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621122 : List Nat := [3, 4, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_5621122 : Nat := 118140960795 + 5621122 * 2 ^ 59
def prefixEnd_5621122 : Nat := 4983230072969 + 3 ^ 40 * 5621122 * 2
def baseEnd_5621122 : Nat := 962112467854153856007979

theorem tailTrace_5621122 : CollatzResearch.WordTrace tailWord_5621122 prefixEnd_5621122 962112467854153856007979 := by
  unfold tailWord_5621122
  simp only [CollatzResearch.WordTrace]
  refine ⟨51254790585410620013078405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136679441561094986701542413 51254790585410620013078405)
  ·
    refine ⟨9610273234764491252452201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51254790585410620013078405 9610273234764491252452201)
    ·
      refine ⟨7207704926073368439339151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9610273234764491252452201 7207704926073368439339151)
      ·
        refine ⟨10811557389110052659008727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7207704926073368439339151 10811557389110052659008727)
        ·
          refine ⟨16217336083665078988513091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10811557389110052659008727 16217336083665078988513091)
          ·
            refine ⟨24326004125497618482769637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16217336083665078988513091 24326004125497618482769637)
            ·
              refine ⟨4561125773530803465519307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24326004125497618482769637 4561125773530803465519307)
              ·
                refine ⟨6841688660296205198278961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4561125773530803465519307 6841688660296205198278961)
                ·
                  refine ⟨5131266495222153898709221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6841688660296205198278961 5131266495222153898709221)
                  ·
                    refine ⟨962112467854153856007979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5131266495222153898709221 962112467854153856007979)
                    ·
                      rfl

theorem cell23_5621122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_5621122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621122 prefixEnd_5621122 := by exact prefixLift 5621122
  have htrace : WordTrace (prefixWord ++ tailWord_5621122) baseStart_5621122 baseEnd_5621122 := by
    simpa [prefixWord, tailWord_5621122, baseEnd_5621122] using wordTrace_append hprefix tailTrace_5621122
  have hstable : (prefixWord ++ tailWord_5621122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621122).length < 2 ^ (prefixWord ++ tailWord_5621122).sum := by decide
  have hdescent : baseEnd_5621122 < baseStart_5621122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621155 : List Nat := [1, 1, 1, 4, 1, 3, 5, 1, 1, 3, 2]
def baseStart_5621155 : Nat := 118140960795 + 5621155 * 2 ^ 59
def prefixEnd_5621155 : Nat := 4983230072969 + 3 ^ 40 * 5621155 * 2
def baseEnd_5621155 : Nat := 2886354348424059938911285

theorem tailTrace_5621155 : CollatzResearch.WordTrace tailWord_5621155 prefixEnd_5621155 2886354348424059938911285 := by
  unfold tailWord_5621155
  simp only [CollatzResearch.WordTrace]
  refine ⟨205020365950522926688264919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136680243967015284458843279 205020365950522926688264919)
  ·
    refine ⟨307530548925784390032397379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205020365950522926688264919 307530548925784390032397379)
    ·
      refine ⟨461295823388676585048596069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307530548925784390032397379 461295823388676585048596069)
      ·
        refine ⟨86492966885376859696611763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 461295823388676585048596069 86492966885376859696611763)
        ·
          refine ⟨129739450328065289544917645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86492966885376859696611763 129739450328065289544917645)
          ·
            refine ⟨48652293873024483579344117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129739450328065289544917645 48652293873024483579344117)
            ·
              refine ⟨4561152550596045335563511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48652293873024483579344117 4561152550596045335563511)
              ·
                refine ⟨6841728825894068003345267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4561152550596045335563511 6841728825894068003345267)
                ·
                  refine ⟨10262593238841102005017901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6841728825894068003345267 10262593238841102005017901)
                  ·
                    refine ⟨3848472464565413251881713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10262593238841102005017901 3848472464565413251881713)
                    ·
                      refine ⟨2886354348424059938911285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3848472464565413251881713 2886354348424059938911285)
                      ·
                        rfl

theorem cell23_5621155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_5621155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621155 prefixEnd_5621155 := by exact prefixLift 5621155
  have htrace : WordTrace (prefixWord ++ tailWord_5621155) baseStart_5621155 baseEnd_5621155 := by
    simpa [prefixWord, tailWord_5621155, baseEnd_5621155] using wordTrace_append hprefix tailTrace_5621155
  have hstable : (prefixWord ++ tailWord_5621155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621155).length < 2 ^ (prefixWord ++ tailWord_5621155).sum := by decide
  have hdescent : baseEnd_5621155 < baseStart_5621155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621181 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_5621181 : Nat := 118140960795 + 5621181 * 2 ^ 59
def prefixEnd_5621181 : Nat := 4983230072969 + 3 ^ 40 * 5621181 * 2
def baseEnd_5621181 : Nat := 2886367698921076837186165

theorem tailTrace_5621181 : CollatzResearch.WordTrace tailWord_5621181 prefixEnd_5621181 2886367698921076837186165 := by
  unfold tailWord_5621181
  simp only [CollatzResearch.WordTrace]
  refine ⟨205021314248428733128711397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136680876165619155419140931 205021314248428733128711397)
  ·
    refine ⟨38441496421580387461633387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205021314248428733128711397 38441496421580387461633387)
    ·
      refine ⟨57662244632370581192450081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38441496421580387461633387 57662244632370581192450081)
      ·
        refine ⟨43246683474277935894337561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57662244632370581192450081 43246683474277935894337561)
        ·
          refine ⟨32435012605708451920753171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43246683474277935894337561 32435012605708451920753171)
          ·
            refine ⟨48652518908562677881129757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32435012605708451920753171 48652518908562677881129757)
            ·
              refine ⟨18244694590711004205423659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48652518908562677881129757 18244694590711004205423659)
              ·
                refine ⟨27367041886066506308135489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18244694590711004205423659 27367041886066506308135489)
                ·
                  refine ⟨20525281414549879731101617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27367041886066506308135489 20525281414549879731101617)
                  ·
                    refine ⟨15393961060912409798326213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20525281414549879731101617 15393961060912409798326213)
                    ·
                      refine ⟨2886367698921076837186165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15393961060912409798326213 2886367698921076837186165)
                      ·
                        rfl

theorem cell23_5621181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_5621181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621181 prefixEnd_5621181 := by exact prefixLift 5621181
  have htrace : WordTrace (prefixWord ++ tailWord_5621181) baseStart_5621181 baseEnd_5621181 := by
    simpa [prefixWord, tailWord_5621181, baseEnd_5621181] using wordTrace_append hprefix tailTrace_5621181
  have hstable : (prefixWord ++ tailWord_5621181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621181).length < 2 ^ (prefixWord ++ tailWord_5621181).sum := by decide
  have hdescent : baseEnd_5621181 < baseStart_5621181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621251 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 5, 4]
def baseStart_5621251 : Nat := 118140960795 + 5621251 * 2 ^ 59
def prefixEnd_5621251 : Nat := 4983230072969 + 3 ^ 40 * 5621251 * 2
def baseEnd_5621251 : Nat := 962134547522297187770281

theorem tailTrace_5621251 : CollatzResearch.WordTrace tailWord_5621251 prefixEnd_5621251 962134547522297187770281 := by
  unfold tailWord_5621251
  simp only [CollatzResearch.WordTrace]
  refine ⟨205023867358175135083759607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136682578238783423389173071 205023867358175135083759607)
  ·
    refine ⟨307535801037262702625639411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205023867358175135083759607 307535801037262702625639411)
    ·
      refine ⟨461303701555894053938459117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307535801037262702625639411 461303701555894053938459117)
      ·
        refine ⟨172988888083460270226922169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 461303701555894053938459117 172988888083460270226922169)
        ·
          refine ⟨129741666062595202670191627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172988888083460270226922169 129741666062595202670191627)
          ·
            refine ⟨194612499093892804005287441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129741666062595202670191627 194612499093892804005287441)
            ·
              refine ⟨145959374320419603003965581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194612499093892804005287441 145959374320419603003965581)
              ·
                refine ⟨54734765370157351126487093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145959374320419603003965581 54734765370157351126487093)
                ·
                  refine ⟨5131384253452251668108165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54734765370157351126487093 5131384253452251668108165)
                  ·
                    refine ⟨962134547522297187770281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5131384253452251668108165 962134547522297187770281)
                    ·
                      rfl

theorem cell23_5621251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 4].length) (baseStart_5621251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621251 prefixEnd_5621251 := by exact prefixLift 5621251
  have htrace : WordTrace (prefixWord ++ tailWord_5621251) baseStart_5621251 baseEnd_5621251 := by
    simpa [prefixWord, tailWord_5621251, baseEnd_5621251] using wordTrace_append hprefix tailTrace_5621251
  have hstable : (prefixWord ++ tailWord_5621251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621251).length < 2 ^ (prefixWord ++ tailWord_5621251).sum := by decide
  have hdescent : baseEnd_5621251 < baseStart_5621251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621281 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 8]
def baseStart_5621281 : Nat := 118140960795 + 5621281 * 2 ^ 59
def prefixEnd_5621281 : Nat := 4983230072969 + 3 ^ 40 * 5621281 * 2
def baseEnd_5621281 : Nat := 320713227442947382881745

theorem tailTrace_5621281 : CollatzResearch.WordTrace tailWord_5621281 prefixEnd_5621281 320713227442947382881745 := by
  unfold tailWord_5621281
  simp only [CollatzResearch.WordTrace]
  refine ⟨205024961548066450207351697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136683307698710966804901131 205024961548066450207351697)
  ·
    refine ⟨153768721161049837655513773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205024961548066450207351697 153768721161049837655513773)
    ·
      refine ⟨57663270435393689120817665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153768721161049837655513773 57663270435393689120817665)
      ·
        refine ⟨43247452826545266840613249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57663270435393689120817665 43247452826545266840613249)
        ·
          refine ⟨32435589619908950130459937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43247452826545266840613249 32435589619908950130459937)
          ·
            refine ⟨24326692214931712597844953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32435589619908950130459937 24326692214931712597844953)
            ·
              refine ⟨18245019161198784448383715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24326692214931712597844953 18245019161198784448383715)
              ·
                refine ⟨27367528741798176672575573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18245019161198784448383715 27367528741798176672575573)
                ·
                  refine ⟨320713227442947382881745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27367528741798176672575573 320713227442947382881745)
                  ·
                    rfl

theorem cell23_5621281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 8].length) (baseStart_5621281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621281 prefixEnd_5621281 := by exact prefixLift 5621281
  have htrace : WordTrace (prefixWord ++ tailWord_5621281) baseStart_5621281 baseEnd_5621281 := by
    simpa [prefixWord, tailWord_5621281, baseEnd_5621281] using wordTrace_append hprefix tailTrace_5621281
  have hstable : (prefixWord ++ tailWord_5621281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621281).length < 2 ^ (prefixWord ++ tailWord_5621281).sum := by decide
  have hdescent : baseEnd_5621281 < baseStart_5621281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621335 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 2, 3, 2]
def baseStart_5621335 : Nat := 118140960795 + 5621335 * 2 ^ 59
def prefixEnd_5621335 : Nat := 4983230072969 + 3 ^ 40 * 5621335 * 2
def baseEnd_5621335 : Nat := 2886446774941869234660457

theorem tailTrace_5621335 : CollatzResearch.WordTrace tailWord_5621335 prefixEnd_5621335 2886446774941869234660457 := by
  unfold tailWord_5621335
  simp only [CollatzResearch.WordTrace]
  refine ⟨205026931089870817429817459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136684620726580544953211639 205026931089870817429817459)
  ·
    refine ⟨307540396634806226144726189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205026931089870817429817459 307540396634806226144726189)
    ·
      refine ⟨115327648738052334804272321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307540396634806226144726189 115327648738052334804272321)
      ·
        refine ⟨86495736553539251103204241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115327648738052334804272321 86495736553539251103204241)
        ·
          refine ⟨64871802415154438327403181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86495736553539251103204241 64871802415154438327403181)
          ·
            refine ⟨24326925905682914372776193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64871802415154438327403181 24326925905682914372776193)
            ·
              refine ⟨18245194429262185779582145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24326925905682914372776193 18245194429262185779582145)
              ·
                refine ⟨13683895821946639334686609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18245194429262185779582145 13683895821946639334686609)
                ·
                  refine ⟨10262921866459979501014957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13683895821946639334686609 10262921866459979501014957)
                  ·
                    refine ⟨3848595699922492312880609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10262921866459979501014957 3848595699922492312880609)
                    ·
                      refine ⟨2886446774941869234660457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3848595699922492312880609 2886446774941869234660457)
                      ·
                        rfl

theorem cell23_5621335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_5621335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621335 prefixEnd_5621335 := by exact prefixLift 5621335
  have htrace : WordTrace (prefixWord ++ tailWord_5621335) baseStart_5621335 baseEnd_5621335 := by
    simpa [prefixWord, tailWord_5621335, baseEnd_5621335] using wordTrace_append hprefix tailTrace_5621335
  have hstable : (prefixWord ++ tailWord_5621335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621335).length < 2 ^ (prefixWord ++ tailWord_5621335).sum := by decide
  have hdescent : baseEnd_5621335 < baseStart_5621335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621348 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_5621348 : Nat := 118140960795 + 5621348 * 2 ^ 59
def prefixEnd_5621348 : Nat := 4983230072969 + 3 ^ 40 * 5621348 * 2
def baseEnd_5621348 : Nat := 2886453450190377683797897

theorem tailTrace_5621348 : CollatzResearch.WordTrace tailWord_5621348 prefixEnd_5621348 2886453450190377683797897 := by
  unfold tailWord_5621348
  simp only [CollatzResearch.WordTrace]
  refine ⟨102513702619411860325020349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136684936825882480433360465 102513702619411860325020349)
  ·
    refine ⟨38442638482279447621882631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102513702619411860325020349 38442638482279447621882631)
    ·
      refine ⟨57663957723419171432823947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38442638482279447621882631 57663957723419171432823947)
      ·
        refine ⟨86495936585128757149235921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57663957723419171432823947 86495936585128757149235921)
        ·
          refine ⟨64871952438846567861926941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86495936585128757149235921 64871952438846567861926941)
          ·
            refine ⟨24326982164567462948222603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64871952438846567861926941 24326982164567462948222603)
            ·
              refine ⟨36490473246851194422333905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24326982164567462948222603 36490473246851194422333905)
              ·
                refine ⟨27367854935138395816750429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36490473246851194422333905 27367854935138395816750429)
                ·
                  refine ⟨10262945600676898431281411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27367854935138395816750429 10262945600676898431281411)
                  ·
                    refine ⟨15394418401015347646922117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10262945600676898431281411 15394418401015347646922117)
                    ·
                      refine ⟨2886453450190377683797897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15394418401015347646922117 2886453450190377683797897)
                      ·
                        rfl

theorem cell23_5621348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_5621348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621348 prefixEnd_5621348 := by exact prefixLift 5621348
  have htrace : WordTrace (prefixWord ++ tailWord_5621348) baseStart_5621348 baseEnd_5621348 := by
    simpa [prefixWord, tailWord_5621348, baseEnd_5621348] using wordTrace_append hprefix tailTrace_5621348
  have hstable : (prefixWord ++ tailWord_5621348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621348).length < 2 ^ (prefixWord ++ tailWord_5621348).sum := by decide
  have hdescent : baseEnd_5621348 < baseStart_5621348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621361 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 1, 1, 6]
def baseStart_5621361 : Nat := 118140960795 + 5621361 * 2 ^ 59
def prefixEnd_5621361 : Nat := 4983230072969 + 3 ^ 40 * 5621361 * 2
def baseEnd_5621361 : Nat := 2886460125438886132935337

theorem tailTrace_5621361 : CollatzResearch.WordTrace tailWord_5621361 prefixEnd_5621361 2886460125438886132935337 := by
  unfold tailWord_5621361
  simp only [CollatzResearch.WordTrace]
  refine ⟨205027879387776623870263937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136685252925184415913509291 205027879387776623870263937)
  ·
    refine ⟨153770909540832467902697953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205027879387776623870263937 153770909540832467902697953)
    ·
      refine ⟨115328182155624350927023465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153770909540832467902697953 115328182155624350927023465)
      ·
        refine ⟨86496136616718263195267599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115328182155624350927023465 86496136616718263195267599)
        ·
          refine ⟨129744204925077394792901399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86496136616718263195267599 129744204925077394792901399)
          ·
            refine ⟨194616307387616092189352099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129744204925077394792901399 194616307387616092189352099)
            ·
              refine ⟨291924461081424138284028149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194616307387616092189352099 291924461081424138284028149)
              ·
                refine ⟨27367918226383512964127639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 291924461081424138284028149 27367918226383512964127639)
                ·
                  refine ⟨41051877339575269446191459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27367918226383512964127639 41051877339575269446191459)
                  ·
                    refine ⟨61577816009362904169287189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41051877339575269446191459 61577816009362904169287189)
                    ·
                      refine ⟨2886460125438886132935337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61577816009362904169287189 2886460125438886132935337)
                      ·
                        rfl

theorem cell23_5621361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_5621361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621361 prefixEnd_5621361 := by exact prefixLift 5621361
  have htrace : WordTrace (prefixWord ++ tailWord_5621361) baseStart_5621361 baseEnd_5621361 := by
    simpa [prefixWord, tailWord_5621361, baseEnd_5621361] using wordTrace_append hprefix tailTrace_5621361
  have hstable : (prefixWord ++ tailWord_5621361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621361).length < 2 ^ (prefixWord ++ tailWord_5621361).sum := by decide
  have hdescent : baseEnd_5621361 < baseStart_5621361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621365 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5621365 : Nat := 118140960795 + 5621365 * 2 ^ 59
def prefixEnd_5621365 : Nat := 4983230072969 + 3 ^ 40 * 5621365 * 2
def baseEnd_5621365 : Nat := 2886462179361504117285319

theorem tailTrace_5621365 : CollatzResearch.WordTrace tailWord_5621365 prefixEnd_5621365 2886462179361504117285319 := by
  unfold tailWord_5621365
  simp only [CollatzResearch.WordTrace]
  refine ⟨205028025279762132553409549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136685350186508088368939699 205028025279762132553409549)
  ·
    refine ⟨76885509479910799707528581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205028025279762132553409549 76885509479910799707528581)
    ·
      refine ⟨14416033027483274945161609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76885509479910799707528581 14416033027483274945161609)
      ·
        refine ⟨10812024770612456208871207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14416033027483274945161609 10812024770612456208871207)
        ·
          refine ⟨16218037155918684313306811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10812024770612456208871207 16218037155918684313306811)
          ·
            refine ⟨24327055733878026469960217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16218037155918684313306811 24327055733878026469960217)
            ·
              refine ⟨18245291800408519852470163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24327055733878026469960217 18245291800408519852470163)
              ·
                refine ⟨27367937700612779778705245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18245291800408519852470163 27367937700612779778705245)
                ·
                  refine ⟨10262976637729792417014467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27367937700612779778705245 10262976637729792417014467)
                  ·
                    refine ⟨15394464956594688625521701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10262976637729792417014467 15394464956594688625521701)
                    ·
                      refine ⟨2886462179361504117285319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15394464956594688625521701 2886462179361504117285319)
                      ·
                        rfl

theorem cell23_5621365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5621365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621365 prefixEnd_5621365 := by exact prefixLift 5621365
  have htrace : WordTrace (prefixWord ++ tailWord_5621365) baseStart_5621365 baseEnd_5621365 := by
    simpa [prefixWord, tailWord_5621365, baseEnd_5621365] using wordTrace_append hprefix tailTrace_5621365
  have hstable : (prefixWord ++ tailWord_5621365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621365).length < 2 ^ (prefixWord ++ tailWord_5621365).sum := by decide
  have hdescent : baseEnd_5621365 < baseStart_5621365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621399 : List Nat := [1, 1, 3, 3, 2, 2, 2, 4, 1, 2, 2]
def baseStart_5621399 : Nat := 118140960795 + 5621399 * 2 ^ 59
def prefixEnd_5621399 : Nat := 4983230072969 + 3 ^ 40 * 5621399 * 2
def baseEnd_5621399 : Nat := 2886479637703756984260163

theorem tailTrace_5621399 : CollatzResearch.WordTrace tailWord_5621399 prefixEnd_5621399 2886479637703756984260163 := by
  unfold tailWord_5621399
  simp only [CollatzResearch.WordTrace]
  refine ⟨205029265361638956360147251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136686176907759304240098167 205029265361638956360147251)
  ·
    refine ⟨307543898042458434540220877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205029265361638956360147251 307543898042458434540220877)
    ·
      refine ⟨115328961765921912952582829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307543898042458434540220877 115328961765921912952582829)
      ·
        refine ⟨43248360662220717357218561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115328961765921912952582829 43248360662220717357218561)
        ·
          refine ⟨32436270496665538017913921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43248360662220717357218561 32436270496665538017913921)
          ·
            refine ⟨24327202872499153513435441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32436270496665538017913921 24327202872499153513435441)
            ·
              refine ⟨18245402154374365135076581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24327202872499153513435441 18245402154374365135076581)
              ·
                refine ⟨3421012903945193462826859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18245402154374365135076581 3421012903945193462826859)
                ·
                  refine ⟨5131519355917790194240289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3421012903945193462826859 5131519355917790194240289)
                  ·
                    refine ⟨3848639516938342645680217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5131519355917790194240289 3848639516938342645680217)
                    ·
                      refine ⟨2886479637703756984260163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3848639516938342645680217 2886479637703756984260163)
                      ·
                        rfl

theorem cell23_5621399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_5621399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621399 prefixEnd_5621399 := by exact prefixLift 5621399
  have htrace : WordTrace (prefixWord ++ tailWord_5621399) baseStart_5621399 baseEnd_5621399 := by
    simpa [prefixWord, tailWord_5621399, baseEnd_5621399] using wordTrace_append hprefix tailTrace_5621399
  have hstable : (prefixWord ++ tailWord_5621399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621399).length < 2 ^ (prefixWord ++ tailWord_5621399).sum := by decide
  have hdescent : baseEnd_5621399 < baseStart_5621399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621401 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 2, 7]
def baseStart_5621401 : Nat := 118140960795 + 5621401 * 2 ^ 59
def prefixEnd_5621401 : Nat := 4983230072969 + 3 ^ 40 * 5621401 * 2
def baseEnd_5621401 : Nat := 962160221555021992145051

theorem tailTrace_5621401 : CollatzResearch.WordTrace tailWord_5621401 prefixEnd_5621401 962160221555021992145051 := by
  unfold tailWord_5621401
  simp only [CollatzResearch.WordTrace]
  refine ⟨205029338307631710701720057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136686225538421140467813371 205029338307631710701720057)
  ·
    refine ⟨153772003730723783026290043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205029338307631710701720057 153772003730723783026290043)
    ·
      refine ⟨230658005596085674539435065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153772003730723783026290043 230658005596085674539435065)
      ·
        refine ⟨172993504197064255904576299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230658005596085674539435065 172993504197064255904576299)
        ·
          refine ⟨259490256295596383856864449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172993504197064255904576299 259490256295596383856864449)
          ·
            refine ⟨194617692221697287892648337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259490256295596383856864449 194617692221697287892648337)
            ·
              refine ⟨145963269166272965919486253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194617692221697287892648337 145963269166272965919486253)
              ·
                refine ⟨54736225937352362219807345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145963269166272965919486253 54736225937352362219807345)
                ·
                  refine ⟨41052169453014271664855509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54736225937352362219807345 41052169453014271664855509)
                  ·
                    refine ⟨962160221555021992145051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41052169453014271664855509 962160221555021992145051)
                    ·
                      rfl

theorem cell23_5621401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 7].length) (baseStart_5621401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621401 prefixEnd_5621401 := by exact prefixLift 5621401
  have htrace : WordTrace (prefixWord ++ tailWord_5621401) baseStart_5621401 baseEnd_5621401 := by
    simpa [prefixWord, tailWord_5621401, baseEnd_5621401] using wordTrace_append hprefix tailTrace_5621401
  have hstable : (prefixWord ++ tailWord_5621401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621401).length < 2 ^ (prefixWord ++ tailWord_5621401).sum := by decide
  have hdescent : baseEnd_5621401 < baseStart_5621401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621416 : List Nat := [2, 1, 7, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_5621416 : Nat := 118140960795 + 5621416 * 2 ^ 59
def prefixEnd_5621416 : Nat := 4983230072969 + 3 ^ 40 * 5621416 * 2
def baseEnd_5621416 : Nat := 2886488366874883417747585

theorem tailTrace_5621416 : CollatzResearch.WordTrace tailWord_5621416 prefixEnd_5621416 2886488366874883417747585 := by
  unfold tailWord_5621416
  simp only [CollatzResearch.WordTrace]
  refine ⟨102514942701288684131758051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136686590268384912175677401 102514942701288684131758051)
  ·
    refine ⟨153772414051933026197637077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102514942701288684131758051 153772414051933026197637077)
    ·
      refine ⟨3604040954342180301507119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 153772414051933026197637077 3604040954342180301507119)
      ·
        refine ⟨5406061431513270452260679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3604040954342180301507119 5406061431513270452260679)
        ·
          refine ⟨8109092147269905678391019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5406061431513270452260679 8109092147269905678391019)
          ·
            refine ⟨12163638220904858517586529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8109092147269905678391019 12163638220904858517586529)
            ·
              refine ⟨9122728665678643888189897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12163638220904858517586529 9122728665678643888189897)
              ·
                refine ⟨6842046499258982916142423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9122728665678643888189897 6842046499258982916142423)
                ·
                  refine ⟨10263069748888474374213635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6842046499258982916142423 10263069748888474374213635)
                  ·
                    refine ⟨15394604623332711561320453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10263069748888474374213635 15394604623332711561320453)
                    ·
                      refine ⟨2886488366874883417747585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15394604623332711561320453 2886488366874883417747585)
                      ·
                        rfl

theorem cell23_5621416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_5621416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621416 prefixEnd_5621416 := by exact prefixLift 5621416
  have htrace : WordTrace (prefixWord ++ tailWord_5621416) baseStart_5621416 baseEnd_5621416 := by
    simpa [prefixWord, tailWord_5621416, baseEnd_5621416] using wordTrace_append hprefix tailTrace_5621416
  have hstable : (prefixWord ++ tailWord_5621416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621416).length < 2 ^ (prefixWord ++ tailWord_5621416).sum := by decide
  have hdescent : baseEnd_5621416 < baseStart_5621416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621488 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 3]
def baseStart_5621488 : Nat := 118140960795 + 5621488 * 2 ^ 59
def prefixEnd_5621488 : Nat := 4983230072969 + 3 ^ 40 * 5621488 * 2
def baseEnd_5621488 : Nat := 2886525337482007136047253

theorem tailTrace_5621488 : CollatzResearch.WordTrace tailWord_5621488 prefixEnd_5621488 2886525337482007136047253 := by
  unfold tailWord_5621488
  simp only [CollatzResearch.WordTrace]
  refine ⟨102516255729158262280068559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136688340972211016373424745 102516255729158262280068559)
  ·
    refine ⟨153774383593737393420102839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102516255729158262280068559 153774383593737393420102839)
    ·
      refine ⟨230661575390606090130154259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153774383593737393420102839 230661575390606090130154259)
      ·
        refine ⟨345992363085909135195231389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230661575390606090130154259 345992363085909135195231389)
        ·
          refine ⟨129747136157215925698211771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345992363085909135195231389 129747136157215925698211771)
          ·
            refine ⟨194620704235823888547317657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129747136157215925698211771 194620704235823888547317657)
            ·
              refine ⟨145965528176867916410488243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194620704235823888547317657 145965528176867916410488243)
              ·
                refine ⟨218948292265301874615732365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145965528176867916410488243 218948292265301874615732365)
                ·
                  refine ⟨82105609599488202980899637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218948292265301874615732365 82105609599488202980899637)
                  ·
                    refine ⟨7697400899952019029459341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82105609599488202980899637 7697400899952019029459341)
                    ·
                      refine ⟨2886525337482007136047253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7697400899952019029459341 2886525337482007136047253)
                      ·
                        rfl

theorem cell23_5621488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 3].length) (baseStart_5621488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621488 prefixEnd_5621488 := by exact prefixLift 5621488
  have htrace : WordTrace (prefixWord ++ tailWord_5621488) baseStart_5621488 baseEnd_5621488 := by
    simpa [prefixWord, tailWord_5621488, baseEnd_5621488] using wordTrace_append hprefix tailTrace_5621488
  have hstable : (prefixWord ++ tailWord_5621488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621488).length < 2 ^ (prefixWord ++ tailWord_5621488).sum := by decide
  have hdescent : baseEnd_5621488 < baseStart_5621488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621506 : List Nat := [3, 4, 1, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_5621506 : Nat := 118140960795 + 5621506 * 2 ^ 59
def prefixEnd_5621506 : Nat := 4983230072969 + 3 ^ 40 * 5621506 * 2
def baseEnd_5621506 : Nat := 2886534580133788065622171

theorem tailTrace_5621506 : CollatzResearch.WordTrace tailWord_5621506 prefixEnd_5621506 2886534580133788065622171 := by
  unfold tailWord_5621506
  simp only [CollatzResearch.WordTrace]
  refine ⟨51258291993062828408573093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136688778648167542422861581 51258291993062828408573093)
  ·
    refine ⟨9610929748699280326607455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51258291993062828408573093 9610929748699280326607455)
    ·
      refine ⟨14416394623048920489911183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9610929748699280326607455 14416394623048920489911183)
      ·
        refine ⟨21624591934573380734866775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14416394623048920489911183 21624591934573380734866775)
        ·
          refine ⟨32436887901860071102300163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21624591934573380734866775 32436887901860071102300163)
          ·
            refine ⟨48655331852790106653450245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32436887901860071102300163 48655331852790106653450245)
            ·
              refine ⟨9122874722398144997521921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48655331852790106653450245 9122874722398144997521921)
              ·
                refine ⟨6842156041798608748141441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9122874722398144997521921 6842156041798608748141441)
                ·
                  refine ⟨5131617031348956561106081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6842156041798608748141441 5131617031348956561106081)
                  ·
                    refine ⟨3848712773511717420829561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5131617031348956561106081 3848712773511717420829561)
                    ·
                      refine ⟨2886534580133788065622171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3848712773511717420829561 2886534580133788065622171)
                      ·
                        rfl

theorem cell23_5621506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_5621506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621506 prefixEnd_5621506 := by exact prefixLift 5621506
  have htrace : WordTrace (prefixWord ++ tailWord_5621506) baseStart_5621506 baseEnd_5621506 := by
    simpa [prefixWord, tailWord_5621506, baseEnd_5621506] using wordTrace_append hprefix tailTrace_5621506
  have hstable : (prefixWord ++ tailWord_5621506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621506).length < 2 ^ (prefixWord ++ tailWord_5621506).sum := by decide
  have hdescent : baseEnd_5621506 < baseStart_5621506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621515 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 2, 5, 2]
def baseStart_5621515 : Nat := 118140960795 + 5621515 * 2 ^ 59
def prefixEnd_5621515 : Nat := 4983230072969 + 3 ^ 40 * 5621515 * 2
def baseEnd_5621515 : Nat := 2886539201459678530409629

theorem tailTrace_5621515 : CollatzResearch.WordTrace tailWord_5621515 prefixEnd_5621515 2886539201459678530409629 := by
  unfold tailWord_5621515
  simp only [CollatzResearch.WordTrace]
  refine ⟨205033496229218708171369999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136688997486145805447579999 205033496229218708171369999)
  ·
    refine ⟨307550244343828062257054999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205033496229218708171369999 307550244343828062257054999)
    ·
      refine ⟨461325366515742093385582499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307550244343828062257054999 461325366515742093385582499)
      ·
        refine ⟨691988049773613140078373749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461325366515742093385582499 691988049773613140078373749)
        ·
          refine ⟨64873879666276231882347539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 691988049773613140078373749 64873879666276231882347539)
          ·
            refine ⟨97310819499414347823521309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64873879666276231882347539 97310819499414347823521309)
            ·
              refine ⟨36491557312280380433820491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97310819499414347823521309 36491557312280380433820491)
              ·
                refine ⟨54737335968420570650730737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36491557312280380433820491 54737335968420570650730737)
                ·
                  refine ⟨41053001976315427988048053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54737335968420570650730737 41053001976315427988048053)
                  ·
                    refine ⟨3848718935279571373879505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41053001976315427988048053 3848718935279571373879505)
                    ·
                      refine ⟨2886539201459678530409629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3848718935279571373879505 2886539201459678530409629)
                      ·
                        rfl

theorem cell23_5621515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 5, 2].length) (baseStart_5621515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621515 prefixEnd_5621515 := by exact prefixLift 5621515
  have htrace : WordTrace (prefixWord ++ tailWord_5621515) baseStart_5621515 baseEnd_5621515 := by
    simpa [prefixWord, tailWord_5621515, baseEnd_5621515] using wordTrace_append hprefix tailTrace_5621515
  have hstable : (prefixWord ++ tailWord_5621515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621515).length < 2 ^ (prefixWord ++ tailWord_5621515).sum := by decide
  have hdescent : baseEnd_5621515 < baseStart_5621515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621522 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_5621522 : Nat := 118140960795 + 5621522 * 2 ^ 59
def prefixEnd_5621522 : Nat := 4983230072969 + 3 ^ 40 * 5621522 * 2
def baseEnd_5621522 : Nat := 2886542795824260003022097

theorem tailTrace_5621522 : CollatzResearch.WordTrace tailWord_5621522 prefixEnd_5621522 2886542795824260003022097 := by
  unfold tailWord_5621522
  simp only [CollatzResearch.WordTrace]
  refine ⟨51258437885048337091718705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136689167693462232244583213 51258437885048337091718705)
  ·
    refine ⟨38443828413786252818789029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51258437885048337091718705 38443828413786252818789029)
    ·
      refine ⟨7208217827584922403522943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38443828413786252818789029 7208217827584922403522943)
      ·
        refine ⟨10812326741377383605284415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7208217827584922403522943 10812326741377383605284415)
        ·
          refine ⟨16218490112066075407926623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10812326741377383605284415 16218490112066075407926623)
          ·
            refine ⟨24327735168099113111889935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16218490112066075407926623 24327735168099113111889935)
            ·
              refine ⟨36491602752148669667834903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24327735168099113111889935 36491602752148669667834903)
              ·
                refine ⟨54737404128223004501752355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36491602752148669667834903 54737404128223004501752355)
                ·
                  refine ⟨82106106192334506752628533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54737404128223004501752355 82106106192334506752628533)
                  ·
                    refine ⟨7697447455531360008058925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82106106192334506752628533 7697447455531360008058925)
                    ·
                      refine ⟨2886542795824260003022097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7697447455531360008058925 2886542795824260003022097)
                      ·
                        rfl

theorem cell23_5621522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_5621522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621522 prefixEnd_5621522 := by exact prefixLift 5621522
  have htrace : WordTrace (prefixWord ++ tailWord_5621522) baseStart_5621522 baseEnd_5621522 := by
    simpa [prefixWord, tailWord_5621522, baseEnd_5621522] using wordTrace_append hprefix tailTrace_5621522
  have hstable : (prefixWord ++ tailWord_5621522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621522).length < 2 ^ (prefixWord ++ tailWord_5621522).sum := by decide
  have hdescent : baseEnd_5621522 < baseStart_5621522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621545 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 6, 4, 2]
def baseStart_5621545 : Nat := 118140960795 + 5621545 * 2 ^ 59
def prefixEnd_5621545 : Nat := 4983230072969 + 3 ^ 40 * 5621545 * 2
def baseEnd_5621545 : Nat := 2886554605879313413034491

theorem tailTrace_5621545 : CollatzResearch.WordTrace tailWord_5621545 prefixEnd_5621545 2886554605879313413034491 := by
  unfold tailWord_5621545
  simp only [CollatzResearch.WordTrace]
  refine ⟨205034590419110023294962089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136689726946073348863308059 205034590419110023294962089)
  ·
    refine ⟨153775942814332517471221567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205034590419110023294962089 153775942814332517471221567)
    ·
      refine ⟨230663914221498776206832351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153775942814332517471221567 230663914221498776206832351)
      ·
        refine ⟨345995871332248164310248527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230663914221498776206832351 345995871332248164310248527)
        ·
          refine ⟨518993806998372246465372791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345995871332248164310248527 518993806998372246465372791)
          ·
            refine ⟨778490710497558369698059187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518993806998372246465372791 778490710497558369698059187)
            ·
              refine ⟨1167736065746337554547088781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778490710497558369698059187 1167736065746337554547088781)
              ·
                refine ⟨437901024654876582955158293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1167736065746337554547088781 437901024654876582955158293)
                ·
                  refine ⟨20526610530697339826023045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 437901024654876582955158293 20526610530697339826023045)
                  ·
                    refine ⟨3848739474505751217379321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20526610530697339826023045 3848739474505751217379321)
                    ·
                      refine ⟨2886554605879313413034491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3848739474505751217379321 2886554605879313413034491)
                      ·
                        rfl

theorem cell23_5621545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 4, 2].length) (baseStart_5621545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621545 prefixEnd_5621545 := by exact prefixLift 5621545
  have htrace : WordTrace (prefixWord ++ tailWord_5621545) baseStart_5621545 baseEnd_5621545 := by
    simpa [prefixWord, tailWord_5621545, baseEnd_5621545] using wordTrace_append hprefix tailTrace_5621545
  have hstable : (prefixWord ++ tailWord_5621545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621545).length < 2 ^ (prefixWord ++ tailWord_5621545).sum := by decide
  have hdescent : baseEnd_5621545 < baseStart_5621545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621562 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2]
def baseStart_5621562 : Nat := 118140960795 + 5621562 * 2 ^ 59
def prefixEnd_5621562 : Nat := 4983230072969 + 3 ^ 40 * 5621562 * 2
def baseEnd_5621562 : Nat := 2886563335050439846521913

theorem tailTrace_5621562 : CollatzResearch.WordTrace tailWord_5621562 prefixEnd_5621562 2886563335050439846521913 := by
  unfold tailWord_5621562
  simp only [CollatzResearch.WordTrace]
  refine ⟨51258802615012108799582735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136690140306698956798887293 51258802615012108799582735)
  ·
    refine ⟨76888203922518163199374103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51258802615012108799582735 76888203922518163199374103)
    ·
      refine ⟨115332305883777244799061155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76888203922518163199374103 115332305883777244799061155)
      ·
        refine ⟨172998458825665867198591733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115332305883777244799061155 172998458825665867198591733)
        ·
          refine ⟨16218605514906175049867975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172998458825665867198591733 16218605514906175049867975)
          ·
            refine ⟨24327908272359262574801963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16218605514906175049867975 24327908272359262574801963)
            ·
              refine ⟨36491862408538893862202945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24327908272359262574801963 36491862408538893862202945)
              ·
                refine ⟨27368896806404170396652209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36491862408538893862202945 27368896806404170396652209)
                ·
                  refine ⟨20526672604803127797489157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27368896806404170396652209 20526672604803127797489157)
                  ·
                    refine ⟨3848751113400586462029217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20526672604803127797489157 3848751113400586462029217)
                    ·
                      refine ⟨2886563335050439846521913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3848751113400586462029217 2886563335050439846521913)
                      ·
                        rfl

theorem cell23_5621562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2].length) (baseStart_5621562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621562 prefixEnd_5621562 := by exact prefixLift 5621562
  have htrace : WordTrace (prefixWord ++ tailWord_5621562) baseStart_5621562 baseEnd_5621562 := by
    simpa [prefixWord, tailWord_5621562, baseEnd_5621562] using wordTrace_append hprefix tailTrace_5621562
  have hstable : (prefixWord ++ tailWord_5621562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621562).length < 2 ^ (prefixWord ++ tailWord_5621562).sum := by decide
  have hdescent : baseEnd_5621562 < baseStart_5621562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621666 : List Nat := [3, 3, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_5621666 : Nat := 118140960795 + 5621666 * 2 ^ 59
def prefixEnd_5621666 : Nat := 4983230072969 + 3 ^ 40 * 5621666 * 2
def baseEnd_5621666 : Nat := 962205579012835813207145

theorem tailTrace_5621666 : CollatzResearch.WordTrace tailWord_5621666 prefixEnd_5621666 962205579012835813207145 := by
  unfold tailWord_5621666
  simp only [CollatzResearch.WordTrace]
  refine ⟨51259750912917915240029213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136692669101114440640077901 51259750912917915240029213)
  ·
    refine ⟨19222406592344218215010955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51259750912917915240029213 19222406592344218215010955)
    ·
      refine ⟨28833609888516327322516433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19222406592344218215010955 28833609888516327322516433)
      ·
        refine ⟨21625207416387245491887325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28833609888516327322516433 21625207416387245491887325)
        ·
          refine ⟨8109452781145217059457747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21625207416387245491887325 8109452781145217059457747)
          ·
            refine ⟨12164179171717825589186621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8109452781145217059457747 12164179171717825589186621)
            ·
              refine ⟨4561567189394184595944983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12164179171717825589186621 4561567189394184595944983)
              ·
                refine ⟨6842350784091276893917475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4561567189394184595944983 6842350784091276893917475)
                ·
                  refine ⟨10263526176136915340876213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6842350784091276893917475 10263526176136915340876213)
                  ·
                    refine ⟨962205579012835813207145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10263526176136915340876213 962205579012835813207145)
                    ·
                      rfl

theorem cell23_5621666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_5621666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621666 prefixEnd_5621666 := by exact prefixLift 5621666
  have htrace : WordTrace (prefixWord ++ tailWord_5621666) baseStart_5621666 baseEnd_5621666 := by
    simpa [prefixWord, tailWord_5621666, baseEnd_5621666] using wordTrace_append hprefix tailTrace_5621666
  have hstable : (prefixWord ++ tailWord_5621666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621666).length < 2 ^ (prefixWord ++ tailWord_5621666).sum := by decide
  have hdescent : baseEnd_5621666 < baseStart_5621666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621730 : List Nat := [3, 3, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_5621730 : Nat := 118140960795 + 5621730 * 2 ^ 59
def prefixEnd_5621730 : Nat := 4983230072969 + 3 ^ 40 * 5621730 * 2
def baseEnd_5621730 : Nat := 962216533266798396407047

theorem tailTrace_5621730 : CollatzResearch.WordTrace tailWord_5621730 prefixEnd_5621730 962216533266798396407047 := by
  unfold tailWord_5621730
  simp only [CollatzResearch.WordTrace]
  refine ⟨51260334480859949972611661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136694225282293199926964429 51260334480859949972611661)
  ·
    refine ⟨19222625430322481239729373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51260334480859949972611661 19222625430322481239729373)
    ·
      refine ⟨7208484536370930464898515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19222625430322481239729373 7208484536370930464898515)
      ·
        refine ⟨10812726804556395697347773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7208484536370930464898515 10812726804556395697347773)
        ·
          refine ⟨4054772551708648386505415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10812726804556395697347773 4054772551708648386505415)
          ·
            refine ⟨6082158827562972579758123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4054772551708648386505415 6082158827562972579758123)
            ·
              refine ⟨9123238241344458869637185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6082158827562972579758123 9123238241344458869637185)
              ·
                refine ⟨6842428681008344152227889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9123238241344458869637185 6842428681008344152227889)
                ·
                  refine ⟨5131821510756258114170917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6842428681008344152227889 5131821510756258114170917)
                  ·
                    refine ⟨962216533266798396407047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5131821510756258114170917 962216533266798396407047)
                    ·
                      rfl

theorem cell23_5621730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_5621730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621730 prefixEnd_5621730 := by exact prefixLift 5621730
  have htrace : WordTrace (prefixWord ++ tailWord_5621730) baseStart_5621730 baseEnd_5621730 := by
    simpa [prefixWord, tailWord_5621730, baseEnd_5621730] using wordTrace_append hprefix tailTrace_5621730
  have hstable : (prefixWord ++ tailWord_5621730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621730).length < 2 ^ (prefixWord ++ tailWord_5621730).sum := by decide
  have hdescent : baseEnd_5621730 < baseStart_5621730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621810 : List Nat := [3, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2]
def baseStart_5621810 : Nat := 118140960795 + 5621810 * 2 ^ 59
def prefixEnd_5621810 : Nat := 4983230072969 + 3 ^ 40 * 5621810 * 2
def baseEnd_5621810 : Nat := 2886690678252754876220773

theorem tailTrace_5621810 : CollatzResearch.WordTrace tailWord_5621810 prefixEnd_5621810 2886690678252754876220773 := by
  unfold tailWord_5621810
  simp only [CollatzResearch.WordTrace]
  refine ⟨51261063940787493388339721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136696170508766649035572589 51261063940787493388339721)
  ·
    refine ⟨38445797955590620041254791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51261063940787493388339721 38445797955590620041254791)
    ·
      refine ⟨57668696933385930061882187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38445797955590620041254791 57668696933385930061882187)
      ·
        refine ⟨86503045400078895092823281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57668696933385930061882187 86503045400078895092823281)
        ·
          refine ⟨64877284050059171319617461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86503045400078895092823281 64877284050059171319617461)
          ·
            refine ⟨6082245379693047311214137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64877284050059171319617461 6082245379693047311214137)
            ·
              refine ⟨4561684034769785483410603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6082245379693047311214137 4561684034769785483410603)
              ·
                refine ⟨6842526052154678225115905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4561684034769785483410603 6842526052154678225115905)
                ·
                  refine ⟨5131894539116008668836929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6842526052154678225115905 5131894539116008668836929)
                  ·
                    refine ⟨3848920904337006501627697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5131894539116008668836929 3848920904337006501627697)
                    ·
                      refine ⟨2886690678252754876220773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3848920904337006501627697 2886690678252754876220773)
                      ·
                        rfl

theorem cell23_5621810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_5621810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621810 prefixEnd_5621810 := by exact prefixLift 5621810
  have htrace : WordTrace (prefixWord ++ tailWord_5621810) baseStart_5621810 baseEnd_5621810 := by
    simpa [prefixWord, tailWord_5621810, baseEnd_5621810] using wordTrace_append hprefix tailTrace_5621810
  have hstable : (prefixWord ++ tailWord_5621810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621810).length < 2 ^ (prefixWord ++ tailWord_5621810).sum := by decide
  have hdescent : baseEnd_5621810 < baseStart_5621810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621849 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 2, 4, 2]
def baseStart_5621849 : Nat := 118140960795 + 5621849 * 2 ^ 59
def prefixEnd_5621849 : Nat := 4983230072969 + 3 ^ 40 * 5621849 * 2
def baseEnd_5621849 : Nat := 2886710703998280223633093

theorem tailTrace_5621849 : CollatzResearch.WordTrace tailWord_5621849 prefixEnd_5621849 2886710703998280223633093 := by
  unfold tailWord_5621849
  simp only [CollatzResearch.WordTrace]
  refine ⟨205045678210008683214028601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136697118806672455476019067 205045678210008683214028601)
  ·
    refine ⟨153784258657506512410521451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205045678210008683214028601 153784258657506512410521451)
    ·
      refine ⟨230676387986259768615782177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153784258657506512410521451 230676387986259768615782177)
      ·
        refine ⟨173007290989694826461836633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230676387986259768615782177 173007290989694826461836633)
        ·
          refine ⟨129755468242271119846377475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173007290989694826461836633 129755468242271119846377475)
          ·
            refine ⟨194633202363406679769566213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129755468242271119846377475 194633202363406679769566213)
            ·
              refine ⟨36493725443138752456793665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194633202363406679769566213 36493725443138752456793665)
              ·
                refine ⟨27370294082354064342595249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36493725443138752456793665 27370294082354064342595249)
                ·
                  refine ⟨20527720561765548256946437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27370294082354064342595249 20527720561765548256946437)
                  ·
                    refine ⟨3848947605331040298177457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20527720561765548256946437 3848947605331040298177457)
                    ·
                      refine ⟨2886710703998280223633093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3848947605331040298177457 2886710703998280223633093)
                      ·
                        rfl

theorem cell23_5621849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 4, 2].length) (baseStart_5621849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621849 prefixEnd_5621849 := by exact prefixLift 5621849
  have htrace : WordTrace (prefixWord ++ tailWord_5621849) baseStart_5621849 baseEnd_5621849 := by
    simpa [prefixWord, tailWord_5621849, baseEnd_5621849] using wordTrace_append hprefix tailTrace_5621849
  have hstable : (prefixWord ++ tailWord_5621849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621849).length < 2 ^ (prefixWord ++ tailWord_5621849).sum := by decide
  have hdescent : baseEnd_5621849 < baseStart_5621849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621869 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_5621869 : Nat := 118140960795 + 5621869 * 2 ^ 59
def prefixEnd_5621869 : Nat := 4983230072969 + 3 ^ 40 * 5621869 * 2
def baseEnd_5621869 : Nat := 2886720973611370145383001

theorem tailTrace_5621869 : CollatzResearch.WordTrace tailWord_5621869 prefixEnd_5621869 2886720973611370145383001 := by
  unfold tailWord_5621869
  simp only [CollatzResearch.WordTrace]
  refine ⟨205046407669936226629756661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136697605113290817753171107 205046407669936226629756661)
  ·
    refine ⟨19223100719056521246539687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 205046407669936226629756661 19223100719056521246539687)
    ·
      refine ⟨28834651078584781869809531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19223100719056521246539687 28834651078584781869809531)
      ·
        refine ⟨43251976617877172804714297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28834651078584781869809531 43251976617877172804714297)
        ·
          refine ⟨32438982463407879603535723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43251976617877172804714297 32438982463407879603535723)
          ·
            refine ⟨48658473695111819405303585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32438982463407879603535723 48658473695111819405303585)
            ·
              refine ⟨36493855271333864553977689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48658473695111819405303585 36493855271333864553977689)
              ·
                refine ⟨27370391453500398415483267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36493855271333864553977689 27370391453500398415483267)
                ·
                  refine ⟨41055587180250597623224901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27370391453500398415483267 41055587180250597623224901)
                  ·
                    refine ⟨7697922596296987054354669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41055587180250597623224901 7697922596296987054354669)
                    ·
                      refine ⟨2886720973611370145383001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7697922596296987054354669 2886720973611370145383001)
                      ·
                        rfl

theorem cell23_5621869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_5621869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621869 prefixEnd_5621869 := by exact prefixLift 5621869
  have htrace : WordTrace (prefixWord ++ tailWord_5621869) baseStart_5621869 baseEnd_5621869 := by
    simpa [prefixWord, tailWord_5621869, baseEnd_5621869] using wordTrace_append hprefix tailTrace_5621869
  have hstable : (prefixWord ++ tailWord_5621869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621869).length < 2 ^ (prefixWord ++ tailWord_5621869).sum := by decide
  have hdescent : baseEnd_5621869 < baseStart_5621869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621893 : List Nat := [1, 3, 1, 1, 5, 2, 2, 3, 1, 4]
def baseStart_5621893 : Nat := 118140960795 + 5621893 * 2 ^ 59
def prefixEnd_5621893 : Nat := 4983230072969 + 3 ^ 40 * 5621893 * 2
def baseEnd_5621893 : Nat := 962244432382359350494297

theorem tailTrace_5621893 : CollatzResearch.WordTrace tailWord_5621893 prefixEnd_5621893 962244432382359350494297 := by
  unfold tailWord_5621893
  simp only [CollatzResearch.WordTrace]
  refine ⟨205047283021849278728630333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136698188681232852485753555 205047283021849278728630333)
  ·
    refine ⟨76892731133193479523236375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205047283021849278728630333 76892731133193479523236375)
    ·
      refine ⟨115339096699790219284854563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76892731133193479523236375 115339096699790219284854563)
      ·
        refine ⟨173008645049685328927281845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115339096699790219284854563 173008645049685328927281845)
        ·
          refine ⟨16219560473407999586932673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173008645049685328927281845 16219560473407999586932673)
          ·
            refine ⟨12164670355055999690199505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16219560473407999586932673 12164670355055999690199505)
            ·
              refine ⟨9123502766291999767649629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12164670355055999690199505 9123502766291999767649629)
              ·
                refine ⟨3421313537359499912868611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9123502766291999767649629 3421313537359499912868611)
                ·
                  refine ⟨5131970306039249869302917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3421313537359499912868611 5131970306039249869302917)
                  ·
                    refine ⟨962244432382359350494297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5131970306039249869302917 962244432382359350494297)
                    ·
                      rfl

theorem cell23_5621893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 1, 4].length) (baseStart_5621893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621893 prefixEnd_5621893 := by exact prefixLift 5621893
  have htrace : WordTrace (prefixWord ++ tailWord_5621893) baseStart_5621893 baseEnd_5621893 := by
    simpa [prefixWord, tailWord_5621893, baseEnd_5621893] using wordTrace_append hprefix tailTrace_5621893
  have hstable : (prefixWord ++ tailWord_5621893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621893).length < 2 ^ (prefixWord ++ tailWord_5621893).sum := by decide
  have hdescent : baseEnd_5621893 < baseStart_5621893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621933 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_5621933 : Nat := 118140960795 + 5621933 * 2 ^ 59
def prefixEnd_5621933 : Nat := 4983230072969 + 3 ^ 40 * 5621933 * 2
def baseEnd_5621933 : Nat := 2886753836373257894982707

theorem tailTrace_5621933 : CollatzResearch.WordTrace tailWord_5621933 prefixEnd_5621933 2886753836373257894982707 := by
  unfold tailWord_5621933
  simp only [CollatzResearch.WordTrace]
  refine ⟨205048741941704365560086453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136699161294469577040057635 205048741941704365560086453)
  ·
    refine ⟨19223319557034784271258105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 205048741941704365560086453 19223319557034784271258105)
    ·
      refine ⟨14417489667776088203443579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19223319557034784271258105 14417489667776088203443579)
      ·
        refine ⟨21626234501664132305165369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14417489667776088203443579 21626234501664132305165369)
        ·
          refine ⟨16219675876248099228874027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21626234501664132305165369 16219675876248099228874027)
          ·
            refine ⟨24329513814372148843311041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16219675876248099228874027 24329513814372148843311041)
            ·
              refine ⟨18247135360779111632483281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24329513814372148843311041 18247135360779111632483281)
              ·
                refine ⟨13685351520584333724362461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18247135360779111632483281 13685351520584333724362461)
                ·
                  refine ⟨5132006820219125146635923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13685351520584333724362461 5132006820219125146635923)
                  ·
                    refine ⟨7698010230328687719953885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5132006820219125146635923 7698010230328687719953885)
                    ·
                      refine ⟨2886753836373257894982707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7698010230328687719953885 2886753836373257894982707)
                      ·
                        rfl

theorem cell23_5621933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_5621933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621933 prefixEnd_5621933 := by exact prefixLift 5621933
  have htrace : WordTrace (prefixWord ++ tailWord_5621933) baseStart_5621933 baseEnd_5621933 := by
    simpa [prefixWord, tailWord_5621933, baseEnd_5621933] using wordTrace_append hprefix tailTrace_5621933
  have hstable : (prefixWord ++ tailWord_5621933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621933).length < 2 ^ (prefixWord ++ tailWord_5621933).sum := by decide
  have hdescent : baseEnd_5621933 < baseStart_5621933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621939 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 1, 8, 2]
def baseStart_5621939 : Nat := 118140960795 + 5621939 * 2 ^ 59
def prefixEnd_5621939 : Nat := 4983230072969 + 3 ^ 40 * 5621939 * 2
def baseEnd_5621939 : Nat := 2886756917257184871507679

theorem tailTrace_5621939 : CollatzResearch.WordTrace tailWord_5621939 prefixEnd_5621939 2886756917257184871507679 := by
  unfold tailWord_5621939
  simp only [CollatzResearch.WordTrace]
  refine ⟨205048960779682628584804871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136699307186455085723203247 205048960779682628584804871)
  ·
    refine ⟨307573441169523942877207307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205048960779682628584804871 307573441169523942877207307)
    ·
      refine ⟨461360161754285914315810961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307573441169523942877207307 461360161754285914315810961)
      ·
        refine ⟨346020121315714435736858221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461360161754285914315810961 346020121315714435736858221)
        ·
          refine ⟨129757545493392913401321833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346020121315714435736858221 129757545493392913401321833)
          ·
            refine ⟨97318159120044685050991375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129757545493392913401321833 97318159120044685050991375)
            ·
              refine ⟨145977238680067027576487063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97318159120044685050991375 145977238680067027576487063)
              ·
                refine ⟨218965858020100541364730595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145977238680067027576487063 218965858020100541364730595)
                ·
                  refine ⟨328448787030150812047095893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218965858020100541364730595 328448787030150812047095893)
                  ·
                    refine ⟨3849009223009579828676905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 328448787030150812047095893 3849009223009579828676905)
                    ·
                      refine ⟨2886756917257184871507679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3849009223009579828676905 2886756917257184871507679)
                      ·
                        rfl

theorem cell23_5621939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 8, 2].length) (baseStart_5621939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621939 prefixEnd_5621939 := by exact prefixLift 5621939
  have htrace : WordTrace (prefixWord ++ tailWord_5621939) baseStart_5621939 baseEnd_5621939 := by
    simpa [prefixWord, tailWord_5621939, baseEnd_5621939] using wordTrace_append hprefix tailTrace_5621939
  have hstable : (prefixWord ++ tailWord_5621939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621939).length < 2 ^ (prefixWord ++ tailWord_5621939).sum := by decide
  have hdescent : baseEnd_5621939 < baseStart_5621939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621959 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 3]
def baseStart_5621959 : Nat := 118140960795 + 5621959 * 2 ^ 59
def prefixEnd_5621959 : Nat := 4983230072969 + 3 ^ 40 * 5621959 * 2
def baseEnd_5621959 : Nat := 2886767186870274793257587

theorem tailTrace_5621959 : CollatzResearch.WordTrace tailWord_5621959 prefixEnd_5621959 2886767186870274793257587 := by
  unfold tailWord_5621959
  simp only [CollatzResearch.WordTrace]
  refine ⟨205049690239610172000532931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136699793493073448000355287 205049690239610172000532931)
  ·
    refine ⟨307574535359415258000799397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205049690239610172000532931 307574535359415258000799397)
    ·
      refine ⟨57670225379890360875149887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 307574535359415258000799397 57670225379890360875149887)
      ·
        refine ⟨86505338069835541312724831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57670225379890360875149887 86505338069835541312724831)
        ·
          refine ⟨129758007104753311969087247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86505338069835541312724831 129758007104753311969087247)
          ·
            refine ⟨194637010657129967953630871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129758007104753311969087247 194637010657129967953630871)
            ·
              refine ⟨291955515985694951930446307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194637010657129967953630871 291955515985694951930446307)
              ·
                refine ⟨437933273978542427895669461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291955515985694951930446307 437933273978542427895669461)
                ·
                  refine ⟨10264061108872088153804753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 437933273978542427895669461 10264061108872088153804753)
                  ·
                    refine ⟨7698045831654066115353565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10264061108872088153804753 7698045831654066115353565)
                    ·
                      refine ⟨2886767186870274793257587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7698045831654066115353565 2886767186870274793257587)
                      ·
                        rfl

theorem cell23_5621959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_5621959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621959 prefixEnd_5621959 := by exact prefixLift 5621959
  have htrace : WordTrace (prefixWord ++ tailWord_5621959) baseStart_5621959 baseEnd_5621959 := by
    simpa [prefixWord, tailWord_5621959, baseEnd_5621959] using wordTrace_append hprefix tailTrace_5621959
  have hstable : (prefixWord ++ tailWord_5621959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621959).length < 2 ^ (prefixWord ++ tailWord_5621959).sum := by decide
  have hdescent : baseEnd_5621959 < baseStart_5621959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5621966 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 4, 4]
def baseStart_5621966 : Nat := 118140960795 + 5621966 * 2 ^ 59
def prefixEnd_5621966 : Nat := 4983230072969 + 3 ^ 40 * 5621966 * 2
def baseEnd_5621966 : Nat := 962256927078285421956685

theorem tailTrace_5621966 : CollatzResearch.WordTrace tailWord_5621966 prefixEnd_5621966 962256927078285421956685 := by
  unfold tailWord_5621966
  simp only [CollatzResearch.WordTrace]
  refine ⟨25631243193823101524504719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136699963700389874797358501 25631243193823101524504719)
  ·
    refine ⟨38446864790734652286757079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25631243193823101524504719 38446864790734652286757079)
    ·
      refine ⟨57670297186101978430135619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38446864790734652286757079 57670297186101978430135619)
      ·
        refine ⟨86505445779152967645203429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57670297186101978430135619 86505445779152967645203429)
        ·
          refine ⟨16219771083591181433475643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86505445779152967645203429 16219771083591181433475643)
          ·
            refine ⟨24329656625386772150213465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16219771083591181433475643 24329656625386772150213465)
            ·
              refine ⟨18247242469040079112660099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24329656625386772150213465 18247242469040079112660099)
              ·
                refine ⟨27370863703560118668990149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18247242469040079112660099 27370863703560118668990149)
                ·
                  refine ⟨5132036944417522250435653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27370863703560118668990149 5132036944417522250435653)
                  ·
                    refine ⟨962256927078285421956685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5132036944417522250435653 962256927078285421956685)
                    ·
                      rfl

theorem cell23_5621966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_5621966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5621966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5621966 prefixEnd_5621966 := by exact prefixLift 5621966
  have htrace : WordTrace (prefixWord ++ tailWord_5621966) baseStart_5621966 baseEnd_5621966 := by
    simpa [prefixWord, tailWord_5621966, baseEnd_5621966] using wordTrace_append hprefix tailTrace_5621966
  have hstable : (prefixWord ++ tailWord_5621966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5621966).length < 2 ^ (prefixWord ++ tailWord_5621966).sum := by decide
  have hdescent : baseEnd_5621966 < baseStart_5621966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5621966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622006 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_5622006 : Nat := 118140960795 + 5622006 * 2 ^ 59
def prefixEnd_5622006 : Nat := 4983230072969 + 3 ^ 40 * 5622006 * 2
def baseEnd_5622006 : Nat := 2886791320461036109369871

theorem tailTrace_5622006 : CollatzResearch.WordTrace tailWord_5622006 prefixEnd_5622006 2886791320461036109369871 := by
  unfold tailWord_5622006
  simp only [CollatzResearch.WordTrace]
  refine ⟨12815712779402493689218367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136700936313626599351662581 12815712779402493689218367)
  ·
    refine ⟨19223569169103740533827551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12815712779402493689218367 19223569169103740533827551)
    ·
      refine ⟨28835353753655610800741327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19223569169103740533827551 28835353753655610800741327)
      ·
        refine ⟨43253030630483416201111991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28835353753655610800741327 43253030630483416201111991)
        ·
          refine ⟨64879545945725124301667987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43253030630483416201111991 64879545945725124301667987)
          ·
            refine ⟨97319318918587686452501981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64879545945725124301667987 97319318918587686452501981)
            ·
              refine ⟨36494744594470382419688243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97319318918587686452501981 36494744594470382419688243)
              ·
                refine ⟨54742116891705573629532365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36494744594470382419688243 54742116891705573629532365)
                ·
                  refine ⟨20528293834389590111074637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54742116891705573629532365 20528293834389590111074637)
                  ·
                    refine ⟨7698110187896096291652989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20528293834389590111074637 7698110187896096291652989)
                    ·
                      refine ⟨2886791320461036109369871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7698110187896096291652989 2886791320461036109369871)
                      ·
                        rfl

theorem cell23_5622006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_5622006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622006 prefixEnd_5622006 := by exact prefixLift 5622006
  have htrace : WordTrace (prefixWord ++ tailWord_5622006) baseStart_5622006 baseEnd_5622006 := by
    simpa [prefixWord, tailWord_5622006, baseEnd_5622006] using wordTrace_append hprefix tailTrace_5622006
  have hstable : (prefixWord ++ tailWord_5622006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622006).length < 2 ^ (prefixWord ++ tailWord_5622006).sum := by decide
  have hdescent : baseEnd_5622006 < baseStart_5622006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622024 : List Nat := [2, 1, 3, 2, 3, 3, 2, 2, 1, 2, 2]
def baseStart_5622024 : Nat := 118140960795 + 5622024 * 2 ^ 59
def prefixEnd_5622024 : Nat := 4983230072969 + 3 ^ 40 * 5622024 * 2
def baseEnd_5622024 : Nat := 2886800563112817038944789

theorem tailTrace_5622024 : CollatzResearch.WordTrace tailWord_5622024 prefixEnd_5622024 2886800563112817038944789 := by
  unfold tailWord_5622024
  simp only [CollatzResearch.WordTrace]
  refine ⟨102526030492187344050824563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136701373989583125401099417 102526030492187344050824563)
  ·
    refine ⟨153789045738281016076236845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102526030492187344050824563 153789045738281016076236845)
    ·
      refine ⟨57670892151855381028588817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153789045738281016076236845 57670892151855381028588817)
      ·
        refine ⟨43253169113891535771441613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57670892151855381028588817 43253169113891535771441613)
        ·
          refine ⟨16219938417709325914290605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43253169113891535771441613 16219938417709325914290605)
          ·
            refine ⟨6082476906640997217858977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16219938417709325914290605 6082476906640997217858977)
            ·
              refine ⟨4561857679980747913394233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6082476906640997217858977 4561857679980747913394233)
              ·
                refine ⟨3421393259985560935045675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4561857679980747913394233 3421393259985560935045675)
                ·
                  refine ⟨5132089889978341402568513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3421393259985560935045675 5132089889978341402568513)
                  ·
                    refine ⟨3849067417483756051926385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5132089889978341402568513 3849067417483756051926385)
                    ·
                      refine ⟨2886800563112817038944789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3849067417483756051926385 2886800563112817038944789)
                      ·
                        rfl

theorem cell23_5622024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_5622024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622024 prefixEnd_5622024 := by exact prefixLift 5622024
  have htrace : WordTrace (prefixWord ++ tailWord_5622024) baseStart_5622024 baseEnd_5622024 := by
    simpa [prefixWord, tailWord_5622024, baseEnd_5622024] using wordTrace_append hprefix tailTrace_5622024
  have hstable : (prefixWord ++ tailWord_5622024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622024).length < 2 ^ (prefixWord ++ tailWord_5622024).sum := by decide
  have hdescent : baseEnd_5622024 < baseStart_5622024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622039 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 1, 8]
def baseStart_5622039 : Nat := 118140960795 + 5622039 * 2 ^ 59
def prefixEnd_5622039 : Nat := 4983230072969 + 3 ^ 40 * 5622039 * 2
def baseEnd_5622039 : Nat := 962269421774211493419073

theorem tailTrace_5622039 : CollatzResearch.WordTrace tailWord_5622039 prefixEnd_5622039 962269421774211493419073 := by
  unfold tailWord_5622039
  simp only [CollatzResearch.WordTrace]
  refine ⟨205052608079320345663445171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136701738719546897108963447 205052608079320345663445171)
  ·
    refine ⟨307578912118980518495167757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205052608079320345663445171 307578912118980518495167757)
    ·
      refine ⟨115342092044617694435687909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307578912118980518495167757 115342092044617694435687909)
      ·
        refine ⟨21626642258365817706691483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115342092044617694435687909 21626642258365817706691483)
        ·
          refine ⟨32439963387548726560037225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21626642258365817706691483 32439963387548726560037225)
          ·
            refine ⟨24329972540661544920027919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32439963387548726560037225 24329972540661544920027919)
            ·
              refine ⟨36494958810992317380041879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24329972540661544920027919 36494958810992317380041879)
              ·
                refine ⟨54742438216488476070062819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36494958810992317380041879 54742438216488476070062819)
                ·
                  refine ⟨82113657324732714105094229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54742438216488476070062819 82113657324732714105094229)
                  ·
                    refine ⟨962269421774211493419073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82113657324732714105094229 962269421774211493419073)
                    ·
                      rfl

theorem cell23_5622039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_5622039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622039 prefixEnd_5622039 := by exact prefixLift 5622039
  have htrace : WordTrace (prefixWord ++ tailWord_5622039) baseStart_5622039 baseEnd_5622039 := by
    simpa [prefixWord, tailWord_5622039, baseEnd_5622039] using wordTrace_append hprefix tailTrace_5622039
  have hstable : (prefixWord ++ tailWord_5622039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622039).length < 2 ^ (prefixWord ++ tailWord_5622039).sum := by decide
  have hdescent : baseEnd_5622039 < baseStart_5622039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622049 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_5622049 : Nat := 118140960795 + 5622049 * 2 ^ 59
def prefixEnd_5622049 : Nat := 4983230072969 + 3 ^ 40 * 5622049 * 2
def baseEnd_5622049 : Nat := 2886813400129179441132173

theorem tailTrace_5622049 : CollatzResearch.WordTrace tailWord_5622049 prefixEnd_5622049 2886813400129179441132173 := by
  unfold tailWord_5622049
  simp only [CollatzResearch.WordTrace]
  refine ⟨205052972809284117371309201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136701981872856078247539467 205052972809284117371309201)
  ·
    refine ⟨153789729606963088028481901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205052972809284117371309201 153789729606963088028481901)
    ·
      refine ⟨57671148602611158010680713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153789729606963088028481901 57671148602611158010680713)
      ·
        refine ⟨43253361451958368508010535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57671148602611158010680713 43253361451958368508010535)
        ·
          refine ⟨64880042177937552762015803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43253361451958368508010535 64880042177937552762015803)
          ·
            refine ⟨97320063266906329143023705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64880042177937552762015803 97320063266906329143023705)
            ·
              refine ⟨72990047450179746857267779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97320063266906329143023705 72990047450179746857267779)
              ·
                refine ⟨109485071175269620285901669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72990047450179746857267779 109485071175269620285901669)
                ·
                  refine ⟨20528450845363053803606563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109485071175269620285901669 20528450845363053803606563)
                  ·
                    refine ⟨30792676268044580705409845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20528450845363053803606563 30792676268044580705409845)
                    ·
                      refine ⟨2886813400129179441132173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30792676268044580705409845 2886813400129179441132173)
                      ·
                        rfl

theorem cell23_5622049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_5622049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622049 prefixEnd_5622049 := by exact prefixLift 5622049
  have htrace : WordTrace (prefixWord ++ tailWord_5622049) baseStart_5622049 baseEnd_5622049 := by
    simpa [prefixWord, tailWord_5622049, baseEnd_5622049] using wordTrace_append hprefix tailTrace_5622049
  have hstable : (prefixWord ++ tailWord_5622049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622049).length < 2 ^ (prefixWord ++ tailWord_5622049).sum := by decide
  have hdescent : baseEnd_5622049 < baseStart_5622049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622069 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 9]
def baseStart_5622069 : Nat := 118140960795 + 5622069 * 2 ^ 59
def prefixEnd_5622069 : Nat := 4983230072969 + 3 ^ 40 * 5622069 * 2
def baseEnd_5622069 : Nat := 320758185526918818098009

theorem tailTrace_5622069 : CollatzResearch.WordTrace tailWord_5622069 prefixEnd_5622069 320758185526918818098009 := by
  unfold tailWord_5622069
  simp only [CollatzResearch.WordTrace]
  refine ⟨205053702269211660787037261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136702468179474440524691507 205053702269211660787037261)
  ·
    refine ⟨76895138350954372795138973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205053702269211660787037261 76895138350954372795138973)
    ·
      refine ⟨28835676881607889798177115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76895138350954372795138973 28835676881607889798177115)
      ·
        refine ⟨43253515322411834697265673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28835676881607889798177115 43253515322411834697265673)
        ·
          refine ⟨32440136491808876022949255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43253515322411834697265673 32440136491808876022949255)
          ·
            refine ⟨48660204737713314034423883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32440136491808876022949255 48660204737713314034423883)
            ·
              refine ⟨72990307106569971051635825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48660204737713314034423883 72990307106569971051635825)
              ·
                refine ⟨54742730329927478288726869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72990307106569971051635825 54742730329927478288726869)
                ·
                  refine ⟨320758185526918818098009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54742730329927478288726869 320758185526918818098009)
                  ·
                    rfl

theorem cell23_5622069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 9].length) (baseStart_5622069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622069 prefixEnd_5622069 := by exact prefixLift 5622069
  have htrace : WordTrace (prefixWord ++ tailWord_5622069) baseStart_5622069 baseEnd_5622069 := by
    simpa [prefixWord, tailWord_5622069, baseEnd_5622069] using wordTrace_append hprefix tailTrace_5622069
  have hstable : (prefixWord ++ tailWord_5622069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622069).length < 2 ^ (prefixWord ++ tailWord_5622069).sum := by decide
  have hdescent : baseEnd_5622069 < baseStart_5622069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622096 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 3]
def baseStart_5622096 : Nat := 118140960795 + 5622096 * 2 ^ 59
def prefixEnd_5622096 : Nat := 4983230072969 + 3 ^ 40 * 5622096 * 2
def baseEnd_5622096 : Nat := 2886837533719940757244457

theorem tailTrace_5622096 : CollatzResearch.WordTrace tailWord_5622096 prefixEnd_5622096 2886837533719940757244457 := by
  unfold tailWord_5622096
  simp only [CollatzResearch.WordTrace]
  refine ⟨102527343520056922199135071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136703124693409229598846761 102527343520056922199135071)
  ·
    refine ⟨153791015280085383298702607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102527343520056922199135071 153791015280085383298702607)
    ·
      refine ⟨230686522920128074948053911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153791015280085383298702607 230686522920128074948053911)
      ·
        refine ⟨346029784380192112422080867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230686522920128074948053911 346029784380192112422080867)
        ·
          refine ⟨519044676570288168633121301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346029784380192112422080867 519044676570288168633121301)
          ·
            refine ⟨24330219214232257904677561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 519044676570288168633121301 24330219214232257904677561)
            ·
              refine ⟨18247664410674193428508171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24330219214232257904677561 18247664410674193428508171)
              ·
                refine ⟨27371496616011290142762257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18247664410674193428508171 27371496616011290142762257)
                ·
                  refine ⟨20528622462008467607071693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27371496616011290142762257 20528622462008467607071693)
                  ·
                    refine ⟨7698233423253175352651885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20528622462008467607071693 7698233423253175352651885)
                    ·
                      refine ⟨2886837533719940757244457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7698233423253175352651885 2886837533719940757244457)
                      ·
                        rfl

theorem cell23_5622096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 3].length) (baseStart_5622096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622096 prefixEnd_5622096 := by exact prefixLift 5622096
  have htrace : WordTrace (prefixWord ++ tailWord_5622096) baseStart_5622096 baseEnd_5622096 := by
    simpa [prefixWord, tailWord_5622096, baseEnd_5622096] using wordTrace_append hprefix tailTrace_5622096
  have hstable : (prefixWord ++ tailWord_5622096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622096).length < 2 ^ (prefixWord ++ tailWord_5622096).sum := by decide
  have hdescent : baseEnd_5622096 < baseStart_5622096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622097 : List Nat := [1, 2, 2, 1, 4, 3, 3, 1, 2, 2, 2]
def baseStart_5622097 : Nat := 118140960795 + 5622097 * 2 ^ 59
def prefixEnd_5622097 : Nat := 4983230072969 + 3 ^ 40 * 5622097 * 2
def baseEnd_5622097 : Nat := 2886838047200595253331953

theorem tailTrace_5622097 : CollatzResearch.WordTrace tailWord_5622097 prefixEnd_5622097 2886838047200595253331953 := by
  unfold tailWord_5622097
  simp only [CollatzResearch.WordTrace]
  refine ⟨205054723513110221569056545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136703149008740147712704363 205054723513110221569056545)
  ·
    refine ⟨153791042634832666176792409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205054723513110221569056545 153791042634832666176792409)
    ·
      refine ⟨115343281976124499632594307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153791042634832666176792409 115343281976124499632594307)
      ·
        refine ⟨173014922964186749448891461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115343281976124499632594307 173014922964186749448891461)
        ·
          refine ⟨32440298055785015521667149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173014922964186749448891461 32440298055785015521667149)
          ·
            refine ⟨12165111770919380820625181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32440298055785015521667149 12165111770919380820625181)
            ·
              refine ⟨4561916914094767807734443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12165111770919380820625181 4561916914094767807734443)
              ·
                refine ⟨6842875371142151711601665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4561916914094767807734443 6842875371142151711601665)
                ·
                  refine ⟨5132156528356613783701249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6842875371142151711601665 5132156528356613783701249)
                  ·
                    refine ⟨3849117396267460337775937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5132156528356613783701249 3849117396267460337775937)
                    ·
                      refine ⟨2886838047200595253331953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3849117396267460337775937 2886838047200595253331953)
                      ·
                        rfl

theorem cell23_5622097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 2, 2, 2].length) (baseStart_5622097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622097 prefixEnd_5622097 := by exact prefixLift 5622097
  have htrace : WordTrace (prefixWord ++ tailWord_5622097) baseStart_5622097 baseEnd_5622097 := by
    simpa [prefixWord, tailWord_5622097, baseEnd_5622097] using wordTrace_append hprefix tailTrace_5622097
  have hstable : (prefixWord ++ tailWord_5622097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622097).length < 2 ^ (prefixWord ++ tailWord_5622097).sum := by decide
  have hdescent : baseEnd_5622097 < baseStart_5622097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622099 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 6, 5]
def baseStart_5622099 : Nat := 118140960795 + 5622099 * 2 ^ 59
def prefixEnd_5622099 : Nat := 4983230072969 + 3 ^ 40 * 5622099 * 2
def baseEnd_5622099 : Nat := 962279691387301415168981

theorem tailTrace_5622099 : CollatzResearch.WordTrace tailWord_5622099 prefixEnd_5622099 962279691387301415168981 := by
  unfold tailWord_5622099
  simp only [CollatzResearch.WordTrace]
  refine ⟨205054796459102975910629351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136703197639401983940419567 205054796459102975910629351)
  ·
    refine ⟨307582194688654463865944027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205054796459102975910629351 307582194688654463865944027)
    ·
      refine ⟨461373292032981695798916041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307582194688654463865944027 461373292032981695798916041)
      ·
        refine ⟨346029969024736271849187031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461373292032981695798916041 346029969024736271849187031)
        ·
          refine ⟨519044953537104407773780547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346029969024736271849187031 519044953537104407773780547)
          ·
            refine ⟨778567430305656611660670821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519044953537104407773780547 778567430305656611660670821)
            ·
              refine ⟨145981393182310614686375779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 778567430305656611660670821 145981393182310614686375779)
              ·
                refine ⟨218972089773465922029563669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145981393182310614686375779 218972089773465922029563669)
                ·
                  refine ⟨10264316708131215095135797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 218972089773465922029563669 10264316708131215095135797)
                  ·
                    refine ⟨962279691387301415168981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10264316708131215095135797 962279691387301415168981)
                    ·
                      rfl

theorem cell23_5622099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 5].length) (baseStart_5622099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622099 prefixEnd_5622099 := by exact prefixLift 5622099
  have htrace : WordTrace (prefixWord ++ tailWord_5622099) baseStart_5622099 baseEnd_5622099 := by
    simpa [prefixWord, tailWord_5622099, baseEnd_5622099] using wordTrace_append hprefix tailTrace_5622099
  have hstable : (prefixWord ++ tailWord_5622099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622099).length < 2 ^ (prefixWord ++ tailWord_5622099).sum := by decide
  have hdescent : baseEnd_5622099 < baseStart_5622099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622116 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 2, 5]
def baseStart_5622116 : Nat := 118140960795 + 5622116 * 2 ^ 59
def prefixEnd_5622116 : Nat := 4983230072969 + 3 ^ 40 * 5622116 * 2
def baseEnd_5622116 : Nat := 962282601111010226331455

theorem tailTrace_5622116 : CollatzResearch.WordTrace tailWord_5622116 prefixEnd_5622116 962282601111010226331455 := by
  unfold tailWord_5622116
  simp only [CollatzResearch.WordTrace]
  refine ⟨102527708250020693906999101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136703611000027591875998801 102527708250020693906999101)
  ·
    refine ⟨38447890593757760215124663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102527708250020693906999101 38447890593757760215124663)
    ·
      refine ⟨57671835890636640322686995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38447890593757760215124663 57671835890636640322686995)
      ·
        refine ⟨86507753835954960484030493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57671835890636640322686995 86507753835954960484030493)
        ·
          refine ⟨32440407688483110181511435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86507753835954960484030493 32440407688483110181511435)
          ·
            refine ⟨48660611532724665272267153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32440407688483110181511435 48660611532724665272267153)
            ·
              refine ⟨36495458649543498954200365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48660611532724665272267153 36495458649543498954200365)
              ·
                refine ⟨13685796993578812107825137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36495458649543498954200365 13685796993578812107825137)
                ·
                  refine ⟨10264347745184109080868853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13685796993578812107825137 10264347745184109080868853)
                  ·
                    refine ⟨962282601111010226331455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10264347745184109080868853 962282601111010226331455)
                    ·
                      rfl

theorem cell23_5622116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_5622116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622116 prefixEnd_5622116 := by exact prefixLift 5622116
  have htrace : WordTrace (prefixWord ++ tailWord_5622116) baseStart_5622116 baseEnd_5622116 := by
    simpa [prefixWord, tailWord_5622116, baseEnd_5622116] using wordTrace_append hprefix tailTrace_5622116
  have hstable : (prefixWord ++ tailWord_5622116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622116).length < 2 ^ (prefixWord ++ tailWord_5622116).sum := by decide
  have hdescent : baseEnd_5622116 < baseStart_5622116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622120 : List Nat := [2, 1, 4, 2, 2, 3, 1, 3, 5]
def baseStart_5622120 : Nat := 118140960795 + 5622120 * 2 ^ 59
def prefixEnd_5622120 : Nat := 4983230072969 + 3 ^ 40 * 5622120 * 2
def baseEnd_5622120 : Nat := 320761095250627629260483

theorem tailTrace_5622120 : CollatzResearch.WordTrace tailWord_5622120 prefixEnd_5622120 320761095250627629260483 := by
  unfold tailWord_5622120
  simp only [CollatzResearch.WordTrace]
  refine ⟨102527781196013448248571907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136703708261351264331429209 102527781196013448248571907)
  ·
    refine ⟨153791671794020172372857861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102527781196013448248571907 153791671794020172372857861)
    ·
      refine ⟨28835938461378782319910849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153791671794020172372857861 28835938461378782319910849)
      ·
        refine ⟨21626953846034086739933137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28835938461378782319910849 21626953846034086739933137)
        ·
          refine ⟨16220215384525565054949853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21626953846034086739933137 16220215384525565054949853)
          ·
            refine ⟨6082580769197086895606195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16220215384525565054949853 6082580769197086895606195)
            ·
              refine ⟨9123871153795630343409293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6082580769197086895606195 9123871153795630343409293)
              ·
                refine ⟨3421451682673361378778485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9123871153795630343409293 3421451682673361378778485)
                ·
                  refine ⟨320761095250627629260483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3421451682673361378778485 320761095250627629260483)
                  ·
                    rfl

theorem cell23_5622120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 5].length) (baseStart_5622120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622120 prefixEnd_5622120 := by exact prefixLift 5622120
  have htrace : WordTrace (prefixWord ++ tailWord_5622120) baseStart_5622120 baseEnd_5622120 := by
    simpa [prefixWord, tailWord_5622120, baseEnd_5622120] using wordTrace_append hprefix tailTrace_5622120
  have hstable : (prefixWord ++ tailWord_5622120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622120).length < 2 ^ (prefixWord ++ tailWord_5622120).sum := by decide
  have hdescent : baseEnd_5622120 < baseStart_5622120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622133 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 2, 5]
def baseStart_5622133 : Nat := 118140960795 + 5622133 * 2 ^ 59
def prefixEnd_5622133 : Nat := 4983230072969 + 3 ^ 40 * 5622133 * 2
def baseEnd_5622133 : Nat := 962285510834719037493929

theorem tailTrace_5622133 : CollatzResearch.WordTrace tailWord_5622133 prefixEnd_5622133 962285510834719037493929 := by
  unfold tailWord_5622133
  simp only [CollatzResearch.WordTrace]
  refine ⟨205056036540979799717367053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136704024360653199811578035 205056036540979799717367053)
  ·
    refine ⟨76896013702867424894012645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205056036540979799717367053 76896013702867424894012645)
    ·
      refine ⟨14418002569287642167627371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76896013702867424894012645 14418002569287642167627371)
      ·
        refine ⟨21627003853931463251441057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14418002569287642167627371 21627003853931463251441057)
        ·
          refine ⟨16220252890448597438580793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21627003853931463251441057 16220252890448597438580793)
          ·
            refine ⟨12165189667836448078935595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16220252890448597438580793 12165189667836448078935595)
            ·
              refine ⟨18247784501754672118403393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12165189667836448078935595 18247784501754672118403393)
              ·
                refine ⟨13685838376316004088802545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18247784501754672118403393 13685838376316004088802545)
                ·
                  refine ⟨10264378782237003066601909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13685838376316004088802545 10264378782237003066601909)
                  ·
                    refine ⟨962285510834719037493929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10264378782237003066601909 962285510834719037493929)
                    ·
                      rfl

theorem cell23_5622133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_5622133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622133 prefixEnd_5622133 := by exact prefixLift 5622133
  have htrace : WordTrace (prefixWord ++ tailWord_5622133) baseStart_5622133 baseEnd_5622133 := by
    simpa [prefixWord, tailWord_5622133, baseEnd_5622133] using wordTrace_append hprefix tailTrace_5622133
  have hstable : (prefixWord ++ tailWord_5622133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622133).length < 2 ^ (prefixWord ++ tailWord_5622133).sum := by decide
  have hdescent : baseEnd_5622133 < baseStart_5622133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622193 : List Nat := [1, 2, 2, 4, 1, 3, 2, 2, 6]
def baseStart_5622193 : Nat := 118140960795 + 5622193 * 2 ^ 59
def prefixEnd_5622193 : Nat := 4983230072969 + 3 ^ 40 * 5622193 * 2
def baseEnd_5622193 : Nat := 320765260149269653081279

theorem tailTrace_5622193 : CollatzResearch.WordTrace tailWord_5622193 prefixEnd_5622193 320765260149269653081279 := by
  unfold tailWord_5622193
  simp only [CollatzResearch.WordTrace]
  refine ⟨205058224920762429964551233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136705483280508286643034155 205058224920762429964551233)
  ·
    refine ⟨153793668690571822473413425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205058224920762429964551233 153793668690571822473413425)
    ·
      refine ⟨115345251517928866855060069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153793668690571822473413425 115345251517928866855060069)
      ·
        refine ⟨21627234659611662535323763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115345251517928866855060069 21627234659611662535323763)
        ·
          refine ⟨32440851989417493802985645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21627234659611662535323763 32440851989417493802985645)
          ·
            refine ⟨12165319496031560176119617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32440851989417493802985645 12165319496031560176119617)
            ·
              refine ⟨9123989622023670132089713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12165319496031560176119617 9123989622023670132089713)
              ·
                refine ⟨6842992216517752599067285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9123989622023670132089713 6842992216517752599067285)
                ·
                  refine ⟨320765260149269653081279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6842992216517752599067285 320765260149269653081279)
                  ·
                    rfl

theorem cell23_5622193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 6].length) (baseStart_5622193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622193 prefixEnd_5622193 := by exact prefixLift 5622193
  have htrace : WordTrace (prefixWord ++ tailWord_5622193) baseStart_5622193 baseEnd_5622193 := by
    simpa [prefixWord, tailWord_5622193, baseEnd_5622193] using wordTrace_append hprefix tailTrace_5622193
  have hstable : (prefixWord ++ tailWord_5622193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622193).length < 2 ^ (prefixWord ++ tailWord_5622193).sum := by decide
  have hdescent : baseEnd_5622193 < baseStart_5622193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622197 : List Nat := [1, 3, 3, 2, 3, 1, 1, 4, 1, 4]
def baseStart_5622197 : Nat := 118140960795 + 5622197 * 2 ^ 59
def prefixEnd_5622197 : Nat := 4983230072969 + 3 ^ 40 * 5622197 * 2
def baseEnd_5622197 : Nat := 962296465088681620693831

theorem tailTrace_5622197 : CollatzResearch.WordTrace tailWord_5622197 prefixEnd_5622197 962296465088681620693831 := by
  unfold tailWord_5622197
  simp only [CollatzResearch.WordTrace]
  refine ⟨205058370812747938647696845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136705580541831959098464563 205058370812747938647696845)
  ·
    refine ⟨76896889054780476992886317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205058370812747938647696845 76896889054780476992886317)
    ·
      refine ⟨28836333395542678872332369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76896889054780476992886317 28836333395542678872332369)
      ·
        refine ⟨21627250046657009154249277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28836333395542678872332369 21627250046657009154249277)
        ·
          refine ⟨8110218767496378432843479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21627250046657009154249277 8110218767496378432843479)
          ·
            refine ⟨12165328151244567649265219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8110218767496378432843479 12165328151244567649265219)
            ·
              refine ⟨18247992226866851473897829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12165328151244567649265219 18247992226866851473897829)
              ·
                refine ⟨3421498542537534651355843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18247992226866851473897829 3421498542537534651355843)
                ·
                  refine ⟨5132247813806301977033765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3421498542537534651355843 5132247813806301977033765)
                  ·
                    refine ⟨962296465088681620693831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5132247813806301977033765 962296465088681620693831)
                    ·
                      rfl

theorem cell23_5622197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_5622197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622197 prefixEnd_5622197 := by exact prefixLift 5622197
  have htrace : WordTrace (prefixWord ++ tailWord_5622197) baseStart_5622197 baseEnd_5622197 := by
    simpa [prefixWord, tailWord_5622197, baseEnd_5622197] using wordTrace_append hprefix tailTrace_5622197
  have hstable : (prefixWord ++ tailWord_5622197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622197).length < 2 ^ (prefixWord ++ tailWord_5622197).sum := by decide
  have hdescent : baseEnd_5622197 < baseStart_5622197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622256 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 6]
def baseStart_5622256 : Nat := 118140960795 + 5622256 * 2 ^ 59
def prefixEnd_5622256 : Nat := 4983230072969 + 3 ^ 40 * 5622256 * 2
def baseEnd_5622256 : Nat := 2886919690624660131243721

theorem tailTrace_5622256 : CollatzResearch.WordTrace tailWord_5622256 prefixEnd_5622256 2886919690624660131243721 := by
  unfold tailWord_5622256
  simp only [CollatzResearch.WordTrace]
  refine ⟨102530261359767095862047311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136707015146356127816063081 102530261359767095862047311)
  ·
    refine ⟨153795392039650643793070967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102530261359767095862047311 153795392039650643793070967)
    ·
      refine ⟨230693088059475965689606451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153795392039650643793070967 230693088059475965689606451)
      ·
        refine ⟨346039632089213948534409677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230693088059475965689606451 346039632089213948534409677)
        ·
          refine ⟨129764862033455230700403629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346039632089213948534409677 129764862033455230700403629)
          ·
            refine ⟨48661823262545711512651361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129764862033455230700403629 48661823262545711512651361)
            ·
              refine ⟨36496367446909283634488521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48661823262545711512651361 36496367446909283634488521)
              ·
                refine ⟨27372275585181962725866391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36496367446909283634488521 27372275585181962725866391)
                ·
                  refine ⟨41058413377772944088799587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27372275585181962725866391 41058413377772944088799587)
                  ·
                    refine ⟨61587620066659416133199381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41058413377772944088799587 61587620066659416133199381)
                    ·
                      refine ⟨2886919690624660131243721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61587620066659416133199381 2886919690624660131243721)
                      ·
                        rfl

theorem cell23_5622256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_5622256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622256 prefixEnd_5622256 := by exact prefixLift 5622256
  have htrace : WordTrace (prefixWord ++ tailWord_5622256) baseStart_5622256 baseEnd_5622256 := by
    simpa [prefixWord, tailWord_5622256, baseEnd_5622256] using wordTrace_append hprefix tailTrace_5622256
  have hstable : (prefixWord ++ tailWord_5622256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622256).length < 2 ^ (prefixWord ++ tailWord_5622256).sum := by decide
  have hdescent : baseEnd_5622256 < baseStart_5622256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622273 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_5622273 : Nat := 118140960795 + 5622273 * 2 ^ 59
def prefixEnd_5622273 : Nat := 4983230072969 + 3 ^ 40 * 5622273 * 2
def baseEnd_5622273 : Nat := 2886928419795786564731143

theorem tailTrace_5622273 : CollatzResearch.WordTrace tailWord_5622273 prefixEnd_5622273 2886928419795786564731143 := by
  unfold tailWord_5622273
  simp only [CollatzResearch.WordTrace]
  refine ⟨205061142760472603627463473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136707428506981735751642315 205061142760472603627463473)
  ·
    refine ⟨153795857070354452720597605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205061142760472603627463473 153795857070354452720597605)
    ·
      refine ⟨28836723200691459885112051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153795857070354452720597605 28836723200691459885112051)
      ·
        refine ⟨43255084801037189827668077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28836723200691459885112051 43255084801037189827668077)
        ·
          refine ⟨16220656800388946185375529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43255084801037189827668077 16220656800388946185375529)
          ·
            refine ⟨12165492600291709639031647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16220656800388946185375529 12165492600291709639031647)
            ·
              refine ⟨18248238900437564458547471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12165492600291709639031647 18248238900437564458547471)
              ·
                refine ⟨27372358350656346687821207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18248238900437564458547471 27372358350656346687821207)
                ·
                  refine ⟨41058537525984520031731811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27372358350656346687821207 41058537525984520031731811)
                  ·
                    refine ⟨61587806288976780047597717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41058537525984520031731811 61587806288976780047597717)
                    ·
                      refine ⟨2886928419795786564731143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61587806288976780047597717 2886928419795786564731143)
                      ·
                        rfl

theorem cell23_5622273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_5622273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622273 prefixEnd_5622273 := by exact prefixLift 5622273
  have htrace : WordTrace (prefixWord ++ tailWord_5622273) baseStart_5622273 baseEnd_5622273 := by
    simpa [prefixWord, tailWord_5622273, baseEnd_5622273] using wordTrace_append hprefix tailTrace_5622273
  have hstable : (prefixWord ++ tailWord_5622273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622273).length < 2 ^ (prefixWord ++ tailWord_5622273).sum := by decide
  have hdescent : baseEnd_5622273 < baseStart_5622273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622283 : List Nat := [1, 1, 1, 1, 7, 1, 4, 7]
def baseStart_5622283 : Nat := 118140960795 + 5622283 * 2 ^ 59
def prefixEnd_5622283 : Nat := 4983230072969 + 3 ^ 40 * 5622283 * 2
def baseEnd_5622283 : Nat := 106923464985271537985411

theorem tailTrace_5622283 : CollatzResearch.WordTrace tailWord_5622283 prefixEnd_5622283 106923464985271537985411 := by
  unfold tailWord_5622283
  simp only [CollatzResearch.WordTrace]
  refine ⟨205061507490436375335327503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136707671660290916890218335 205061507490436375335327503)
  ·
    refine ⟨307592261235654563002991255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205061507490436375335327503 307592261235654563002991255)
    ·
      refine ⟨461388391853481844504486883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307592261235654563002991255 461388391853481844504486883)
      ·
        refine ⟨692082587780222766756730325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461388391853481844504486883 692082587780222766756730325)
        ·
          refine ⟨16220685651098971095860867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 692082587780222766756730325 16220685651098971095860867)
          ·
            refine ⟨24331028476648456643791301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16220685651098971095860867 24331028476648456643791301)
            ·
              refine ⟨4562067839371585620710869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24331028476648456643791301 4562067839371585620710869)
              ·
                refine ⟨106923464985271537985411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4562067839371585620710869 106923464985271537985411)
                ·
                  rfl

theorem cell23_5622283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 7].length) (baseStart_5622283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622283 prefixEnd_5622283 := by exact prefixLift 5622283
  have htrace : WordTrace (prefixWord ++ tailWord_5622283) baseStart_5622283 baseEnd_5622283 := by
    simpa [prefixWord, tailWord_5622283, baseEnd_5622283] using wordTrace_append hprefix tailTrace_5622283
  have hstable : (prefixWord ++ tailWord_5622283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622283).length < 2 ^ (prefixWord ++ tailWord_5622283).sum := by decide
  have hdescent : baseEnd_5622283 < baseStart_5622283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622293 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 3, 3, 3]
def baseStart_5622293 : Nat := 118140960795 + 5622293 * 2 ^ 59
def prefixEnd_5622293 : Nat := 4983230072969 + 3 ^ 40 * 5622293 * 2
def baseEnd_5622293 : Nat := 2886938689408876486481051

theorem tailTrace_5622293 : CollatzResearch.WordTrace tailWord_5622293 prefixEnd_5622293 2886938689408876486481051 := by
  unfold tailWord_5622293
  simp only [CollatzResearch.WordTrace]
  refine ⟨205061872220400147043191533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136707914813600098028794355 205061872220400147043191533)
  ·
    refine ⟨76898202082650055141196825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205061872220400147043191533 76898202082650055141196825)
    ·
      refine ⟨57673651561987541355897619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76898202082650055141196825 57673651561987541355897619)
      ·
        refine ⟨86510477342981312033846429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57673651561987541355897619 86510477342981312033846429)
        ·
          refine ⟨32441429003617992012692411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86510477342981312033846429 32441429003617992012692411)
          ·
            refine ⟨48662143505426988019038617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32441429003617992012692411 48662143505426988019038617)
            ·
              refine ⟨36496607629070241014278963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48662143505426988019038617 36496607629070241014278963)
              ·
                refine ⟨54744911443605361521418445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36496607629070241014278963 54744911443605361521418445)
                ·
                  refine ⟨20529341791352010570531917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54744911443605361521418445 20529341791352010570531917)
                  ·
                    refine ⟨7698503171757003963949469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20529341791352010570531917 7698503171757003963949469)
                    ·
                      refine ⟨2886938689408876486481051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7698503171757003963949469 2886938689408876486481051)
                      ·
                        rfl

theorem cell23_5622293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_5622293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622293 prefixEnd_5622293 := by exact prefixLift 5622293
  have htrace : WordTrace (prefixWord ++ tailWord_5622293) baseStart_5622293 baseEnd_5622293 := by
    simpa [prefixWord, tailWord_5622293, baseEnd_5622293] using wordTrace_append hprefix tailTrace_5622293
  have hstable : (prefixWord ++ tailWord_5622293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622293).length < 2 ^ (prefixWord ++ tailWord_5622293).sum := by decide
  have hdescent : baseEnd_5622293 < baseStart_5622293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622337 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_5622337 : Nat := 118140960795 + 5622337 * 2 ^ 59
def prefixEnd_5622337 : Nat := 4983230072969 + 3 ^ 40 * 5622337 * 2
def baseEnd_5622337 : Nat := 2886961282557674314330849

theorem tailTrace_5622337 : CollatzResearch.WordTrace tailWord_5622337 prefixEnd_5622337 2886961282557674314330849 := by
  unfold tailWord_5622337
  simp only [CollatzResearch.WordTrace]
  refine ⟨205063477032240742557793265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136708984688160495038528843 205063477032240742557793265)
  ·
    refine ⟨153797607774180556918344949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205063477032240742557793265 153797607774180556918344949)
    ·
      refine ⟨14418525728829427211094839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153797607774180556918344949 14418525728829427211094839)
      ·
        refine ⟨21627788593244140816642259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14418525728829427211094839 21627788593244140816642259)
        ·
          refine ⟨32441682889866211224963389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21627788593244140816642259 32441682889866211224963389)
          ·
            refine ⟨12165631083699829209361271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32441682889866211224963389 12165631083699829209361271)
            ·
              refine ⟨18248446625549743814041907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12165631083699829209361271 18248446625549743814041907)
              ·
                refine ⟨27372669938324615721062861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18248446625549743814041907 27372669938324615721062861)
                ·
                  refine ⟨10264751226871730895398573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27372669938324615721062861 10264751226871730895398573)
                  ·
                    refine ⟨3849281710076899085774465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10264751226871730895398573 3849281710076899085774465)
                    ·
                      refine ⟨2886961282557674314330849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3849281710076899085774465 2886961282557674314330849)
                      ·
                        rfl

theorem cell23_5622337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_5622337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622337 prefixEnd_5622337 := by exact prefixLift 5622337
  have htrace : WordTrace (prefixWord ++ tailWord_5622337) baseStart_5622337 baseEnd_5622337 := by
    simpa [prefixWord, tailWord_5622337, baseEnd_5622337] using wordTrace_append hprefix tailTrace_5622337
  have hstable : (prefixWord ++ tailWord_5622337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622337).length < 2 ^ (prefixWord ++ tailWord_5622337).sum := by decide
  have hdescent : baseEnd_5622337 < baseStart_5622337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622350 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2]
def baseStart_5622350 : Nat := 118140960795 + 5622350 * 2 ^ 59
def prefixEnd_5622350 : Nat := 4983230072969 + 3 ^ 40 * 5622350 * 2
def baseEnd_5622350 : Nat := 2886967957806182763468289

theorem tailTrace_5622350 : CollatzResearch.WordTrace tailWord_5622350 prefixEnd_5622350 2886967957806182763468289 := by
  unfold tailWord_5622350
  simp only [CollatzResearch.WordTrace]
  refine ⟨25632993897649205722252063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136709300787462430518677669 25632993897649205722252063)
  ·
    refine ⟨38449490846473808583378095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25632993897649205722252063 38449490846473808583378095)
    ·
      refine ⟨57674236269710712875067143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38449490846473808583378095 57674236269710712875067143)
      ·
        refine ⟨86511354404566069312600715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57674236269710712875067143 86511354404566069312600715)
        ·
          refine ⟨129767031606849103968901073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86511354404566069312600715 129767031606849103968901073)
          ·
            refine ⟨97325273705136827976675805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129767031606849103968901073 97325273705136827976675805)
            ·
              refine ⟨36496977639426310491253427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97325273705136827976675805 36496977639426310491253427)
              ·
                refine ⟨54745466459139465736880141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36496977639426310491253427 54745466459139465736880141)
                ·
                  refine ⟨20529549922177299651330053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54745466459139465736880141 20529549922177299651330053)
                  ·
                    refine ⟨3849290610408243684624385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20529549922177299651330053 3849290610408243684624385)
                    ·
                      refine ⟨2886967957806182763468289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3849290610408243684624385 2886967957806182763468289)
                      ·
                        rfl

theorem cell23_5622350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_5622350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622350 prefixEnd_5622350 := by exact prefixLift 5622350
  have htrace : WordTrace (prefixWord ++ tailWord_5622350) baseStart_5622350 baseEnd_5622350 := by
    simpa [prefixWord, tailWord_5622350, baseEnd_5622350] using wordTrace_append hprefix tailTrace_5622350
  have hstable : (prefixWord ++ tailWord_5622350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622350).length < 2 ^ (prefixWord ++ tailWord_5622350).sum := by decide
  have hdescent : baseEnd_5622350 < baseStart_5622350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622353 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 2, 1, 5]
def baseStart_5622353 : Nat := 118140960795 + 5622353 * 2 ^ 59
def prefixEnd_5622353 : Nat := 4983230072969 + 3 ^ 40 * 5622353 * 2
def baseEnd_5622353 : Nat := 2886969498248146251730775

theorem tailTrace_5622353 : CollatzResearch.WordTrace tailWord_5622353 prefixEnd_5622353 2886969498248146251730775 := by
  unfold tailWord_5622353
  simp only [CollatzResearch.WordTrace]
  refine ⟨205064060600182777290375713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136709373733455184860250475 205064060600182777290375713)
  ·
    refine ⟨153798045450137082967781785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205064060600182777290375713 153798045450137082967781785)
    ·
      refine ⟨115348534087602812225836339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153798045450137082967781785 115348534087602812225836339)
      ·
        refine ⟨173022801131404218338754509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115348534087602812225836339 173022801131404218338754509)
        ·
          refine ⟨64883550424276581877032941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173022801131404218338754509 64883550424276581877032941)
          ·
            refine ⟨24331331409103718203887353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64883550424276581877032941 24331331409103718203887353)
            ·
              refine ⟨18248498556827788652915515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24331331409103718203887353 18248498556827788652915515)
              ·
                refine ⟨27372747835241682979373273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18248498556827788652915515 27372747835241682979373273)
                ·
                  refine ⟨20529560876431262234529955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27372747835241682979373273 20529560876431262234529955)
                  ·
                    refine ⟨30794341314646893351794933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20529560876431262234529955 30794341314646893351794933)
                    ·
                      refine ⟨2886969498248146251730775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30794341314646893351794933 2886969498248146251730775)
                      ·
                        rfl

theorem cell23_5622353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_5622353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622353 prefixEnd_5622353 := by exact prefixLift 5622353
  have htrace : WordTrace (prefixWord ++ tailWord_5622353) baseStart_5622353 baseEnd_5622353 := by
    simpa [prefixWord, tailWord_5622353, baseEnd_5622353] using wordTrace_append hprefix tailTrace_5622353
  have hstable : (prefixWord ++ tailWord_5622353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622353).length < 2 ^ (prefixWord ++ tailWord_5622353).sum := by decide
  have hdescent : baseEnd_5622353 < baseStart_5622353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622354 : List Nat := [3, 2, 2, 1, 2, 1, 5, 1, 1, 3, 2]
def baseStart_5622354 : Nat := 118140960795 + 5622354 * 2 ^ 59
def prefixEnd_5622354 : Nat := 4983230072969 + 3 ^ 40 * 5622354 * 2
def baseEnd_5622354 : Nat := 2886970011728800747818271

theorem tailTrace_5622354 : CollatzResearch.WordTrace tailWord_5622354 prefixEnd_5622354 2886970011728800747818271 := by
  unfold tailWord_5622354
  simp only [CollatzResearch.WordTrace]
  refine ⟨51266024268294788615290529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136709398048786102974108077 51266024268294788615290529)
  ·
    refine ⟨38449518201221091461467897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51266024268294788615290529 38449518201221091461467897)
    ·
      refine ⟨28837138650915818596100923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38449518201221091461467897 28837138650915818596100923)
      ·
        refine ⟨43255707976373727894151385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28837138650915818596100923 43255707976373727894151385)
        ·
          refine ⟨32441780982280295920613539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43255707976373727894151385 32441780982280295920613539)
          ·
            refine ⟨48662671473420443880920309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32441780982280295920613539 48662671473420443880920309)
            ·
              refine ⟨4562125450633166613836279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48662671473420443880920309 4562125450633166613836279)
              ·
                refine ⟨6843188175949749920754419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4562125450633166613836279 6843188175949749920754419)
                ·
                  refine ⟨10264782263924624881131629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6843188175949749920754419 10264782263924624881131629)
                  ·
                    refine ⟨3849293348971734330424361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10264782263924624881131629 3849293348971734330424361)
                    ·
                      refine ⟨2886970011728800747818271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3849293348971734330424361 2886970011728800747818271)
                      ·
                        rfl

theorem cell23_5622354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_5622354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622354 prefixEnd_5622354 := by exact prefixLift 5622354
  have htrace : WordTrace (prefixWord ++ tailWord_5622354) baseStart_5622354 baseEnd_5622354 := by
    simpa [prefixWord, tailWord_5622354, baseEnd_5622354] using wordTrace_append hprefix tailTrace_5622354
  have hstable : (prefixWord ++ tailWord_5622354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622354).length < 2 ^ (prefixWord ++ tailWord_5622354).sum := by decide
  have hdescent : baseEnd_5622354 < baseStart_5622354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622383 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 3]
def baseStart_5622383 : Nat := 118140960795 + 5622383 * 2 ^ 59
def prefixEnd_5622383 : Nat := 4983230072969 + 3 ^ 40 * 5622383 * 2
def baseEnd_5622383 : Nat := 2886984902667781134355637

theorem tailTrace_5622383 : CollatzResearch.WordTrace tailWord_5622383 prefixEnd_5622383 2886984902667781134355637 := by
  unfold tailWord_5622383
  simp only [CollatzResearch.WordTrace]
  refine ⟨205065154790074092413967803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136710103193382728275978535 205065154790074092413967803)
  ·
    refine ⟨307597732185111138620951705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205065154790074092413967803 307597732185111138620951705)
    ·
      refine ⟨230698299138833353965713779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307597732185111138620951705 230698299138833353965713779)
      ·
        refine ⟨346047448708250030948570669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230698299138833353965713779 346047448708250030948570669)
        ·
          refine ⟨129767793265593761605714001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346047448708250030948570669 129767793265593761605714001)
          ·
            refine ⟨97325844949195321204285501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129767793265593761605714001 97325844949195321204285501)
            ·
              refine ⟨36497191855948245451607063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97325844949195321204285501 36497191855948245451607063)
              ·
                refine ⟨54745787783922368177410595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36497191855948245451607063 54745787783922368177410595)
                ·
                  refine ⟨82118681675883552266115893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54745787783922368177410595 82118681675883552266115893)
                  ·
                    refine ⟨7698626407114083024948365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82118681675883552266115893 7698626407114083024948365)
                    ·
                      refine ⟨2886984902667781134355637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7698626407114083024948365 2886984902667781134355637)
                      ·
                        rfl

theorem cell23_5622383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 3].length) (baseStart_5622383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622383 prefixEnd_5622383 := by exact prefixLift 5622383
  have htrace : WordTrace (prefixWord ++ tailWord_5622383) baseStart_5622383 baseEnd_5622383 := by
    simpa [prefixWord, tailWord_5622383, baseEnd_5622383] using wordTrace_append hprefix tailTrace_5622383
  have hstable : (prefixWord ++ tailWord_5622383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622383).length < 2 ^ (prefixWord ++ tailWord_5622383).sum := by decide
  have hdescent : baseEnd_5622383 < baseStart_5622383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622430 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_5622430 : Nat := 118140960795 + 5622430 * 2 ^ 59
def prefixEnd_5622430 : Nat := 4983230072969 + 3 ^ 40 * 5622430 * 2
def baseEnd_5622430 : Nat := 2887009036258542450467921

theorem tailTrace_5622430 : CollatzResearch.WordTrace tailWord_5622430 prefixEnd_5622430 2887009036258542450467921 := by
  unfold tailWord_5622430
  simp only [CollatzResearch.WordTrace]
  refine ⟨25633358627612977430116093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136711246013935879627285829 25633358627612977430116093)
  ·
    refine ⟨9612509485354866536293535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25633358627612977430116093 9612509485354866536293535)
    ·
      refine ⟨14418764228032299804440303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9612509485354866536293535 14418764228032299804440303)
      ·
        refine ⟨21628146342048449706660455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14418764228032299804440303 21628146342048449706660455)
        ·
          refine ⟨32442219513072674559990683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21628146342048449706660455 32442219513072674559990683)
          ·
            refine ⟨48663329269609011839986025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32442219513072674559990683 48663329269609011839986025)
            ·
              refine ⟨36497496952206758879989519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48663329269609011839986025 36497496952206758879989519)
              ·
                refine ⟨54746245428310138319984279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36497496952206758879989519 54746245428310138319984279)
                ·
                  refine ⟨82119368142465207479976419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54746245428310138319984279 82119368142465207479976419)
                  ·
                    refine ⟨123179052213697811219964629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82119368142465207479976419 123179052213697811219964629)
                    ·
                      refine ⟨2887009036258542450467921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123179052213697811219964629 2887009036258542450467921)
                      ·
                        rfl

theorem cell23_5622430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_5622430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622430 prefixEnd_5622430 := by exact prefixLift 5622430
  have htrace : WordTrace (prefixWord ++ tailWord_5622430) baseStart_5622430 baseEnd_5622430 := by
    simpa [prefixWord, tailWord_5622430, baseEnd_5622430] using wordTrace_append hprefix tailTrace_5622430
  have hstable : (prefixWord ++ tailWord_5622430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622430).length < 2 ^ (prefixWord ++ tailWord_5622430).sum := by decide
  have hdescent : baseEnd_5622430 < baseStart_5622430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622460 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 1, 4, 3]
def baseStart_5622460 : Nat := 118140960795 + 5622460 * 2 ^ 59
def prefixEnd_5622460 : Nat := 4983230072969 + 3 ^ 40 * 5622460 * 2
def baseEnd_5622460 : Nat := 2887024440678177333092783

theorem tailTrace_5622460 : CollatzResearch.WordTrace tailWord_5622460 prefixEnd_5622460 2887024440678177333092783 := by
  unfold tailWord_5622460
  simp only [CollatzResearch.WordTrace]
  refine ⟨102533981605397567282260417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136711975473863423043013889 102533981605397567282260417)
  ·
    refine ⟨76900486204048175461695313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102533981605397567282260417 76900486204048175461695313)
    ·
      refine ⟨57675364653036131596271485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76900486204048175461695313 57675364653036131596271485)
      ·
        refine ⟨21628261744888549348601807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57675364653036131596271485 21628261744888549348601807)
        ·
          refine ⟨32442392617332824022902711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21628261744888549348601807 32442392617332824022902711)
          ·
            refine ⟨48663588925999236034354067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32442392617332824022902711 48663588925999236034354067)
            ·
              refine ⟨72995383388998854051531101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48663588925999236034354067 72995383388998854051531101)
              ·
                refine ⟨27373268770874570269324163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72995383388998854051531101 27373268770874570269324163)
                ·
                  refine ⟨41059903156311855403986245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27373268770874570269324163 41059903156311855403986245)
                  ·
                    refine ⟨7698731841808472888247421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41059903156311855403986245 7698731841808472888247421)
                    ·
                      refine ⟨2887024440678177333092783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7698731841808472888247421 2887024440678177333092783)
                      ·
                        rfl

theorem cell23_5622460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_5622460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622460 prefixEnd_5622460 := by exact prefixLift 5622460
  have htrace : WordTrace (prefixWord ++ tailWord_5622460) baseStart_5622460 baseEnd_5622460 := by
    simpa [prefixWord, tailWord_5622460, baseEnd_5622460] using wordTrace_append hprefix tailTrace_5622460
  have hstable : (prefixWord ++ tailWord_5622460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622460).length < 2 ^ (prefixWord ++ tailWord_5622460).sum := by decide
  have hdescent : baseEnd_5622460 < baseStart_5622460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622463 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 8]
def baseStart_5622463 : Nat := 118140960795 + 5622463 * 2 ^ 59
def prefixEnd_5622463 : Nat := 4983230072969 + 3 ^ 40 * 5622463 * 2
def baseEnd_5622463 : Nat := 320780664568904535706141

theorem tailTrace_5622463 : CollatzResearch.WordTrace tailWord_5622463 prefixEnd_5622463 320780664568904535706141 := by
  unfold tailWord_5622463
  simp only [CollatzResearch.WordTrace]
  refine ⟨205068072629784266076880043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136712048419856177384586695 205068072629784266076880043)
  ·
    refine ⟨307602108944676399115320065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205068072629784266076880043 307602108944676399115320065)
    ·
      refine ⟨230701581708507299336490049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307602108944676399115320065 230701581708507299336490049)
      ·
        refine ⟨173026186281380474502367537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230701581708507299336490049 173026186281380474502367537)
        ·
          refine ⟨129769639711035355876775653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173026186281380474502367537 129769639711035355876775653)
          ·
            refine ⟨24331807445819129226895435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129769639711035355876775653 24331807445819129226895435)
            ·
              refine ⟨36497711168728693840343153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24331807445819129226895435 36497711168728693840343153)
              ·
                refine ⟨27373283376546520380257365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36497711168728693840343153 27373283376546520380257365)
                ·
                  refine ⟨320780664568904535706141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27373283376546520380257365 320780664568904535706141)
                  ·
                    rfl

theorem cell23_5622463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 8].length) (baseStart_5622463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622463 prefixEnd_5622463 := by exact prefixLift 5622463
  have htrace : WordTrace (prefixWord ++ tailWord_5622463) baseStart_5622463 baseEnd_5622463 := by
    simpa [prefixWord, tailWord_5622463, baseEnd_5622463] using wordTrace_append hprefix tailTrace_5622463
  have hstable : (prefixWord ++ tailWord_5622463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622463).length < 2 ^ (prefixWord ++ tailWord_5622463).sum := by decide
  have hdescent : baseEnd_5622463 < baseStart_5622463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622497 : List Nat := [1, 2, 3, 1, 4, 1, 4, 1, 6]
def baseStart_5622497 : Nat := 118140960795 + 5622497 * 2 ^ 59
def prefixEnd_5622497 : Nat := 4983230072969 + 3 ^ 40 * 5622497 * 2
def baseEnd_5622497 : Nat := 320782604384710409814457

theorem tailTrace_5622497 : CollatzResearch.WordTrace tailWord_5622497 prefixEnd_5622497 320782604384710409814457 := by
  unfold tailWord_5622497
  simp only [CollatzResearch.WordTrace]
  refine ⟨205069312711661089883617745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136712875141107393255745163 205069312711661089883617745)
  ·
    refine ⟨153801984533745817412713309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205069312711661089883617745 153801984533745817412713309)
    ·
      refine ⟨57675744200154681529767491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153801984533745817412713309 57675744200154681529767491)
      ·
        refine ⟨86513616300232022294651237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57675744200154681529767491 86513616300232022294651237)
        ·
          refine ⟨16221303056293504180247107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86513616300232022294651237 16221303056293504180247107)
          ·
            refine ⟨24331954584440256270370661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16221303056293504180247107 24331954584440256270370661)
            ·
              refine ⟨4562241484582548050694499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24331954584440256270370661 4562241484582548050694499)
              ·
                refine ⟨6843362226873822076041749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4562241484582548050694499 6843362226873822076041749)
                ·
                  refine ⟨320782604384710409814457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6843362226873822076041749 320782604384710409814457)
                  ·
                    rfl

theorem cell23_5622497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 6].length) (baseStart_5622497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622497 prefixEnd_5622497 := by exact prefixLift 5622497
  have htrace : WordTrace (prefixWord ++ tailWord_5622497) baseStart_5622497 baseEnd_5622497 := by
    simpa [prefixWord, tailWord_5622497, baseEnd_5622497] using wordTrace_append hprefix tailTrace_5622497
  have hstable : (prefixWord ++ tailWord_5622497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622497).length < 2 ^ (prefixWord ++ tailWord_5622497).sum := by decide
  have hdescent : baseEnd_5622497 < baseStart_5622497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622553 : List Nat := [1, 2, 1, 2, 1, 1, 1, 14]
def baseStart_5622553 : Nat := 118140960795 + 5622553 * 2 ^ 59
def prefixEnd_5622553 : Nat := 4983230072969 + 3 ^ 40 * 5622553 * 2
def baseEnd_5622553 : Nat := 106928599791816498860365

theorem tailTrace_5622553 : CollatzResearch.WordTrace tailWord_5622553 prefixEnd_5622553 106928599791816498860365 := by
  unfold tailWord_5622553
  simp only [CollatzResearch.WordTrace]
  refine ⟨205071355199458211447656313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136714236799638807631770875 205071355199458211447656313)
  ·
    refine ⟨153803516399593658585742235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205071355199458211447656313 153803516399593658585742235)
    ·
      refine ⟨230705274599390487878613353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153803516399593658585742235 230705274599390487878613353)
      ·
        refine ⟨173028955949542865908960015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230705274599390487878613353 173028955949542865908960015)
        ·
          refine ⟨259543433924314298863440023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173028955949542865908960015 259543433924314298863440023)
          ·
            refine ⟨389315150886471448295160035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259543433924314298863440023 389315150886471448295160035)
            ·
              refine ⟨583972726329707172442740053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389315150886471448295160035 583972726329707172442740053)
              ·
                refine ⟨106928599791816498860365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 583972726329707172442740053 106928599791816498860365)
                ·
                  rfl

theorem cell23_5622553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 14].length) (baseStart_5622553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622553 prefixEnd_5622553 := by exact prefixLift 5622553
  have htrace : WordTrace (prefixWord ++ tailWord_5622553) baseStart_5622553 baseEnd_5622553 := by
    simpa [prefixWord, tailWord_5622553, baseEnd_5622553] using wordTrace_append hprefix tailTrace_5622553
  have hstable : (prefixWord ++ tailWord_5622553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622553).length < 2 ^ (prefixWord ++ tailWord_5622553).sum := by decide
  have hdescent : baseEnd_5622553 < baseStart_5622553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622581 : List Nat := [1, 3, 3, 1, 3, 3, 2, 1, 1, 1, 4]
def baseStart_5622581 : Nat := 118140960795 + 5622581 * 2 ^ 59
def prefixEnd_5622581 : Nat := 4983230072969 + 3 ^ 40 * 5622581 * 2
def baseEnd_5622581 : Nat := 2887086571837371359679727

theorem tailTrace_5622581 : CollatzResearch.WordTrace tailWord_5622581 prefixEnd_5622581 2887086571837371359679727 := by
  unfold tailWord_5622581
  simp only [CollatzResearch.WordTrace]
  refine ⟨205072376443356772229675597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136714917628904514819783731 205072376443356772229675597)
  ·
    refine ⟨76902141166258789586128349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205072376443356772229675597 76902141166258789586128349)
    ·
      refine ⟨28838302937347046094798131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76902141166258789586128349 28838302937347046094798131)
      ·
        refine ⟨43257454406020569142197197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28838302937347046094798131 43257454406020569142197197)
        ·
          refine ⟨16221545402257713428323949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43257454406020569142197197 16221545402257713428323949)
          ·
            refine ⟨6083079525846642535621481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16221545402257713428323949 6083079525846642535621481)
            ·
              refine ⟨4562309644384981901716111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6083079525846642535621481 4562309644384981901716111)
              ·
                refine ⟨6843464466577472852574167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4562309644384981901716111 6843464466577472852574167)
                ·
                  refine ⟨10265196699866209278861251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6843464466577472852574167 10265196699866209278861251)
                  ·
                    refine ⟨15397795049799313918291877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10265196699866209278861251 15397795049799313918291877)
                    ·
                      refine ⟨2887086571837371359679727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15397795049799313918291877 2887086571837371359679727)
                      ·
                        rfl

theorem cell23_5622581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_5622581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622581 prefixEnd_5622581 := by exact prefixLift 5622581
  have htrace : WordTrace (prefixWord ++ tailWord_5622581) baseStart_5622581 baseEnd_5622581 := by
    simpa [prefixWord, tailWord_5622581, baseEnd_5622581] using wordTrace_append hprefix tailTrace_5622581
  have hstable : (prefixWord ++ tailWord_5622581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622581).length < 2 ^ (prefixWord ++ tailWord_5622581).sum := by decide
  have hdescent : baseEnd_5622581 < baseStart_5622581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622640 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 5]
def baseStart_5622640 : Nat := 118140960795 + 5622640 * 2 ^ 59
def prefixEnd_5622640 : Nat := 4983230072969 + 3 ^ 40 * 5622640 * 2
def baseEnd_5622640 : Nat := 2887116867195986628841955

theorem tailTrace_5622640 : CollatzResearch.WordTrace tailWord_5622640 prefixEnd_5622640 2887116867195986628841955 := by
  unfold tailWord_5622640
  simp only [CollatzResearch.WordTrace]
  refine ⟨102537264175071512653036687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136716352233428683537382249 102537264175071512653036687)
  ·
    refine ⟨153805896262607268979555031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102537264175071512653036687 153805896262607268979555031)
    ·
      refine ⟨230708844393910903469332547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153805896262607268979555031 230708844393910903469332547)
      ·
        refine ⟨346063266590866355203998821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230708844393910903469332547 346063266590866355203998821)
        ·
          refine ⟨64886862485787441600749779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 346063266590866355203998821 64886862485787441600749779)
          ·
            refine ⟨97330293728681162401124669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64886862485787441600749779 97330293728681162401124669)
            ·
              refine ⟨36498860148255435900421751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97330293728681162401124669 36498860148255435900421751)
              ·
                refine ⟨54748290222383153850632627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36498860148255435900421751 54748290222383153850632627)
                ·
                  refine ⟨82122435333574730775948941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54748290222383153850632627 82122435333574730775948941)
                  ·
                    refine ⟨30795913250090524040980853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82122435333574730775948941 30795913250090524040980853)
                    ·
                      refine ⟨2887116867195986628841955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30795913250090524040980853 2887116867195986628841955)
                      ·
                        rfl

theorem cell23_5622640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_5622640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622640 prefixEnd_5622640 := by exact prefixLift 5622640
  have htrace : WordTrace (prefixWord ++ tailWord_5622640) baseStart_5622640 baseEnd_5622640 := by
    simpa [prefixWord, tailWord_5622640, baseEnd_5622640] using wordTrace_append hprefix tailTrace_5622640
  have hstable : (prefixWord ++ tailWord_5622640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622640).length < 2 ^ (prefixWord ++ tailWord_5622640).sum := by decide
  have hdescent : baseEnd_5622640 < baseStart_5622640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622700 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 7]
def baseStart_5622700 : Nat := 118140960795 + 5622700 * 2 ^ 59
def prefixEnd_5622700 : Nat := 4983230072969 + 3 ^ 40 * 5622700 * 2
def baseEnd_5622700 : Nat := 2887147676035256394091679

theorem tailTrace_5622700 : CollatzResearch.WordTrace tailWord_5622700 prefixEnd_5622700 2887147676035256394091679 := by
  unfold tailWord_5622700
  simp only [CollatzResearch.WordTrace]
  refine ⟨102538358364962827776628777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136717811153283770368838369 102538358364962827776628777)
  ·
    refine ⟨76903768773722120832471583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102538358364962827776628777 76903768773722120832471583)
    ·
      refine ⟨115355653160583181248707375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76903768773722120832471583 115355653160583181248707375)
      ·
        refine ⟨173033479740874771873061063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115355653160583181248707375 173033479740874771873061063)
        ·
          refine ⟨259550219611312157809591595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173033479740874771873061063 259550219611312157809591595)
          ·
            refine ⟨389325329416968236714387393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259550219611312157809591595 389325329416968236714387393)
            ·
              refine ⟨291993997062726177535790545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389325329416968236714387393 291993997062726177535790545)
              ·
                refine ⟨218995497797044633151842909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291993997062726177535790545 218995497797044633151842909)
                ·
                  refine ⟨82123311673891737431941091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218995497797044633151842909 82123311673891737431941091)
                  ·
                    refine ⟨123184967510837606147911637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82123311673891737431941091 123184967510837606147911637)
                    ·
                      refine ⟨2887147676035256394091679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123184967510837606147911637 2887147676035256394091679)
                      ·
                        rfl

theorem cell23_5622700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_5622700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622700 prefixEnd_5622700 := by exact prefixLift 5622700
  have htrace : WordTrace (prefixWord ++ tailWord_5622700) baseStart_5622700 baseEnd_5622700 := by
    simpa [prefixWord, tailWord_5622700, baseEnd_5622700] using wordTrace_append hprefix tailTrace_5622700
  have hstable : (prefixWord ++ tailWord_5622700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622700).length < 2 ^ (prefixWord ++ tailWord_5622700).sum := by decide
  have hdescent : baseEnd_5622700 < baseStart_5622700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622727 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_5622727 : Nat := 118140960795 + 5622727 * 2 ^ 59
def prefixEnd_5622727 : Nat := 4983230072969 + 3 ^ 40 * 5622727 * 2
def baseEnd_5622727 : Nat := 2887161540012927788454055

theorem tailTrace_5622727 : CollatzResearch.WordTrace tailWord_5622727 prefixEnd_5622727 2887161540012927788454055 := by
  unfold tailWord_5622727
  simp only [CollatzResearch.WordTrace]
  refine ⟨205077701500827839164490435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136718467667218559442993623 205077701500827839164490435)
  ·
    refine ⟨307616552251241758746735653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205077701500827839164490435 307616552251241758746735653)
    ·
      refine ⟨57678103547107829765012935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 307616552251241758746735653 57678103547107829765012935)
      ·
        refine ⟨86517155320661744647519403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57678103547107829765012935 86517155320661744647519403)
        ·
          refine ⟨129775732980992616971279105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86517155320661744647519403 129775732980992616971279105)
          ·
            refine ⟨97331799735744462728459329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129775732980992616971279105 97331799735744462728459329)
            ·
              refine ⟨72998849801808347046344497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97331799735744462728459329 72998849801808347046344497)
              ·
                refine ⟨54749137351356260284758373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72998849801808347046344497 54749137351356260284758373)
                ·
                  refine ⟨10265463253379298803392195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54749137351356260284758373 10265463253379298803392195)
                  ·
                    refine ⟨15398194880068948205088293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10265463253379298803392195 15398194880068948205088293)
                    ·
                      refine ⟨2887161540012927788454055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15398194880068948205088293 2887161540012927788454055)
                      ·
                        rfl

theorem cell23_5622727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_5622727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622727 prefixEnd_5622727 := by exact prefixLift 5622727
  have htrace : WordTrace (prefixWord ++ tailWord_5622727) baseStart_5622727 baseEnd_5622727 := by
    simpa [prefixWord, tailWord_5622727, baseEnd_5622727] using wordTrace_append hprefix tailTrace_5622727
  have hstable : (prefixWord ++ tailWord_5622727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622727).length < 2 ^ (prefixWord ++ tailWord_5622727).sum := by decide
  have hdescent : baseEnd_5622727 < baseStart_5622727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622741 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 2, 5]
def baseStart_5622741 : Nat := 118140960795 + 5622741 * 2 ^ 59
def prefixEnd_5622741 : Nat := 4983230072969 + 3 ^ 40 * 5622741 * 2
def baseEnd_5622741 : Nat := 962389576247363577892997

theorem tailTrace_5622741 : CollatzResearch.WordTrace tailWord_5622741 prefixEnd_5622741 962389576247363577892997 := by
  unfold tailWord_5622741
  simp only [CollatzResearch.WordTrace]
  refine ⟨205078212122777119555500077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136718808081851413037000051 205078212122777119555500077)
  ·
    refine ⟨76904329546041419833312529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205078212122777119555500077 76904329546041419833312529)
    ·
      refine ⟨57678247159531064874984397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76904329546041419833312529 57678247159531064874984397)
      ·
        refine ⟨21629342684824149328119149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57678247159531064874984397 21629342684824149328119149)
        ·
          refine ⟨8111003506809055998044681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21629342684824149328119149 8111003506809055998044681)
          ·
            refine ⟨6083252630106791998533511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8111003506809055998044681 6083252630106791998533511)
            ·
              refine ⟨9124878945160187997800267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6083252630106791998533511 9124878945160187997800267)
              ·
                refine ⟨13687318417740281996700401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9124878945160187997800267 13687318417740281996700401)
                ·
                  refine ⟨10265488813305211497525301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13687318417740281996700401 10265488813305211497525301)
                  ·
                    refine ⟨962389576247363577892997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10265488813305211497525301 962389576247363577892997)
                    ·
                      rfl

theorem cell23_5622741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_5622741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622741 prefixEnd_5622741 := by exact prefixLift 5622741
  have htrace : WordTrace (prefixWord ++ tailWord_5622741) baseStart_5622741 baseEnd_5622741 := by
    simpa [prefixWord, tailWord_5622741, baseEnd_5622741] using wordTrace_append hprefix tailTrace_5622741
  have hstable : (prefixWord ++ tailWord_5622741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622741).length < 2 ^ (prefixWord ++ tailWord_5622741).sum := by decide
  have hdescent : baseEnd_5622741 < baseStart_5622741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622744 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 2, 1, 4]
def baseStart_5622744 : Nat := 118140960795 + 5622744 * 2 ^ 59
def prefixEnd_5622744 : Nat := 4983230072969 + 3 ^ 40 * 5622744 * 2
def baseEnd_5622744 : Nat := 2887170269184054221941477

theorem tailTrace_5622744 : CollatzResearch.WordTrace tailWord_5622744 prefixEnd_5622744 2887170269184054221941477 := by
  unfold tailWord_5622744
  simp only [CollatzResearch.WordTrace]
  refine ⟨102539160770883125533929643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136718881027844167378572857 102539160770883125533929643)
  ·
    refine ⟨153808741156324688300894465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102539160770883125533929643 153808741156324688300894465)
    ·
      refine ⟨115356555867243516225670849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153808741156324688300894465 115356555867243516225670849)
      ·
        refine ⟨86517416900432637169253137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115356555867243516225670849 86517416900432637169253137)
        ·
          refine ⟨64888062675324477876939853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86517416900432637169253137 64888062675324477876939853)
          ·
            refine ⟨24333023503246679203852445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64888062675324477876939853 24333023503246679203852445)
            ·
              refine ⟨9124883813717504701444667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24333023503246679203852445 9124883813717504701444667)
              ·
                refine ⟨13687325720576257052167001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9124883813717504701444667 13687325720576257052167001)
                ·
                  refine ⟨10265494290432192789125251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13687325720576257052167001 10265494290432192789125251)
                  ·
                    refine ⟨15398241435648289183687877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10265494290432192789125251 15398241435648289183687877)
                    ·
                      refine ⟨2887170269184054221941477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15398241435648289183687877 2887170269184054221941477)
                      ·
                        rfl

theorem cell23_5622744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_5622744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622744 prefixEnd_5622744 := by exact prefixLift 5622744
  have htrace : WordTrace (prefixWord ++ tailWord_5622744) baseStart_5622744 baseEnd_5622744 := by
    simpa [prefixWord, tailWord_5622744, baseEnd_5622744] using wordTrace_append hprefix tailTrace_5622744
  have hstable : (prefixWord ++ tailWord_5622744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622744).length < 2 ^ (prefixWord ++ tailWord_5622744).sum := by decide
  have hdescent : baseEnd_5622744 < baseStart_5622744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622767 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 8]
def baseStart_5622767 : Nat := 118140960795 + 5622767 * 2 ^ 59
def prefixEnd_5622767 : Nat := 4983230072969 + 3 ^ 40 * 5622767 * 2
def baseEnd_5622767 : Nat := 320798008804345292439319

theorem tailTrace_5622767 : CollatzResearch.WordTrace tailWord_5622767 prefixEnd_5622767 320798008804345292439319 := by
  unfold tailWord_5622767
  simp only [CollatzResearch.WordTrace]
  refine ⟨205079160420682925995946555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136719440280455283997297703 205079160420682925995946555)
  ·
    refine ⟨307618740631024388993919833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205079160420682925995946555 307618740631024388993919833)
    ·
      refine ⟨230714055473268291745439875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307618740631024388993919833 230714055473268291745439875)
      ·
        refine ⟨346071083209902437618159813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230714055473268291745439875 346071083209902437618159813)
        ·
          refine ⟨64888328101856707053404965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 346071083209902437618159813 64888328101856707053404965)
          ·
            refine ⟨12166561519098132572513431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64888328101856707053404965 12166561519098132572513431)
            ·
              refine ⟨18249842278647198858770147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12166561519098132572513431 18249842278647198858770147)
              ·
                refine ⟨27374763417970798288155221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18249842278647198858770147 27374763417970798288155221)
                ·
                  refine ⟨320798008804345292439319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27374763417970798288155221 320798008804345292439319)
                  ·
                    rfl

theorem cell23_5622767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 8].length) (baseStart_5622767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622767 prefixEnd_5622767 := by exact prefixLift 5622767
  have htrace : WordTrace (prefixWord ++ tailWord_5622767) baseStart_5622767 baseEnd_5622767 := by
    simpa [prefixWord, tailWord_5622767, baseEnd_5622767] using wordTrace_append hprefix tailTrace_5622767
  have hstable : (prefixWord ++ tailWord_5622767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622767).length < 2 ^ (prefixWord ++ tailWord_5622767).sum := by decide
  have hdescent : baseEnd_5622767 < baseStart_5622767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622821 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 2, 3, 2]
def baseStart_5622821 : Nat := 118140960795 + 5622821 * 2 ^ 59
def prefixEnd_5622821 : Nat := 4983230072969 + 3 ^ 40 * 5622821 * 2
def baseEnd_5622821 : Nat := 2887209807194450420678623

theorem tailTrace_5622821 : CollatzResearch.WordTrace tailWord_5622821 prefixEnd_5622821 2887209807194450420678623 := by
  unfold tailWord_5622821
  simp only [CollatzResearch.WordTrace]
  refine ⟨205081129962487293218412317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136720753308324862145608211 205081129962487293218412317)
  ·
    refine ⟨76905423735932734956904619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205081129962487293218412317 76905423735932734956904619)
    ·
      refine ⟨115358135603899102435356929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76905423735932734956904619 115358135603899102435356929)
      ·
        refine ⟨86518601702924326826517697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115358135603899102435356929 86518601702924326826517697)
        ·
          refine ⟨64888951277193245119888273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86518601702924326826517697 64888951277193245119888273)
          ·
            refine ⟨48666713457894933839916205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64888951277193245119888273 48666713457894933839916205)
            ·
              refine ⟨18250017546710600189968577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48666713457894933839916205 18250017546710600189968577)
              ·
                refine ⟨13687513160032950142476433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18250017546710600189968577 13687513160032950142476433)
                ·
                  refine ⟨10265634870024712606857325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13687513160032950142476433 10265634870024712606857325)
                  ·
                    refine ⟨3849613076259267227571497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10265634870024712606857325 3849613076259267227571497)
                    ·
                      refine ⟨2887209807194450420678623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3849613076259267227571497 2887209807194450420678623)
                      ·
                        rfl

theorem cell23_5622821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_5622821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622821 prefixEnd_5622821 := by exact prefixLift 5622821
  have htrace : WordTrace (prefixWord ++ tailWord_5622821) baseStart_5622821 baseEnd_5622821 := by
    simpa [prefixWord, tailWord_5622821, baseEnd_5622821] using wordTrace_append hprefix tailTrace_5622821
  have hstable : (prefixWord ++ tailWord_5622821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622821).length < 2 ^ (prefixWord ++ tailWord_5622821).sum := by decide
  have hdescent : baseEnd_5622821 < baseStart_5622821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622834 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_5622834 : Nat := 118140960795 + 5622834 * 2 ^ 59
def prefixEnd_5622834 : Nat := 4983230072969 + 3 ^ 40 * 5622834 * 2
def baseEnd_5622834 : Nat := 2887216482442958869816063

theorem tailTrace_5622834 : CollatzResearch.WordTrace tailWord_5622834 prefixEnd_5622834 2887216482442958869816063 := by
  unfold tailWord_5622834
  simp only [CollatzResearch.WordTrace]
  refine ⟨51270401027860049109658889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136721069407626797625757037 51270401027860049109658889)
  ·
    refine ⟨38452800770895036832244167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51270401027860049109658889 38452800770895036832244167)
    ·
      refine ⟨57679201156342555248366251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38452800770895036832244167 57679201156342555248366251)
      ·
        refine ⟨86518801734513832872549377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57679201156342555248366251 86518801734513832872549377)
        ·
          refine ⟨64889101300885374654412033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86518801734513832872549377 64889101300885374654412033)
          ·
            refine ⟨48666825975664030990809025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64889101300885374654412033 48666825975664030990809025)
            ·
              refine ⟨36500119481748023243106769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48666825975664030990809025 36500119481748023243106769)
              ·
                refine ⟨27375089611311017432330077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36500119481748023243106769 27375089611311017432330077)
                ·
                  refine ⟨10265658604241631537123779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27375089611311017432330077 10265658604241631537123779)
                  ·
                    refine ⟨15398487906362447305685669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10265658604241631537123779 15398487906362447305685669)
                    ·
                      refine ⟨2887216482442958869816063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15398487906362447305685669 2887216482442958869816063)
                      ·
                        rfl

theorem cell23_5622834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_5622834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622834 prefixEnd_5622834 := by exact prefixLift 5622834
  have htrace : WordTrace (prefixWord ++ tailWord_5622834) baseStart_5622834 baseEnd_5622834 := by
    simpa [prefixWord, tailWord_5622834, baseEnd_5622834] using wordTrace_append hprefix tailTrace_5622834
  have hstable : (prefixWord ++ tailWord_5622834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622834).length < 2 ^ (prefixWord ++ tailWord_5622834).sum := by decide
  have hdescent : baseEnd_5622834 < baseStart_5622834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622851 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 5, 2, 2]
def baseStart_5622851 : Nat := 118140960795 + 5622851 * 2 ^ 59
def prefixEnd_5622851 : Nat := 4983230072969 + 3 ^ 40 * 5622851 * 2
def baseEnd_5622851 : Nat := 2887225211614085303303485

theorem tailTrace_5622851 : CollatzResearch.WordTrace tailWord_5622851 prefixEnd_5622851 2887225211614085303303485 := by
  unfold tailWord_5622851
  simp only [CollatzResearch.WordTrace]
  refine ⟨205082224152378608342004407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136721482768252405561336271 205082224152378608342004407)
  ·
    refine ⟨307623336228567912513006611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205082224152378608342004407 307623336228567912513006611)
    ·
      refine ⟨461435004342851868769509917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307623336228567912513006611 461435004342851868769509917)
      ·
        refine ⟨173038126628569450788566219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 461435004342851868769509917 173038126628569450788566219)
        ·
          refine ⟨259557189942854176182849329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173038126628569450788566219 259557189942854176182849329)
          ·
            refine ⟨194667892457140632137136997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259557189942854176182849329 194667892457140632137136997)
            ·
              refine ⟨36500229835713868525713187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194667892457140632137136997 36500229835713868525713187)
              ·
                refine ⟨54750344753570802788569781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36500229835713868525713187 54750344753570802788569781)
                ·
                  refine ⟨5132844820647262761428417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54750344753570802788569781 5132844820647262761428417)
                  ·
                    refine ⟨3849633615485447071071313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5132844820647262761428417 3849633615485447071071313)
                    ·
                      refine ⟨2887225211614085303303485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3849633615485447071071313 2887225211614085303303485)
                      ·
                        rfl

theorem cell23_5622851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 2, 2].length) (baseStart_5622851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622851 prefixEnd_5622851 := by exact prefixLift 5622851
  have htrace : WordTrace (prefixWord ++ tailWord_5622851) baseStart_5622851 baseEnd_5622851 := by
    simpa [prefixWord, tailWord_5622851, baseEnd_5622851] using wordTrace_append hprefix tailTrace_5622851
  have hstable : (prefixWord ++ tailWord_5622851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622851).length < 2 ^ (prefixWord ++ tailWord_5622851).sum := by decide
  have hdescent : baseEnd_5622851 < baseStart_5622851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622861 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_5622861 : Nat := 118140960795 + 5622861 * 2 ^ 59
def prefixEnd_5622861 : Nat := 4983230072969 + 3 ^ 40 * 5622861 * 2
def baseEnd_5622861 : Nat := 962410115473543421392813

theorem tailTrace_5622861 : CollatzResearch.WordTrace tailWord_5622861 prefixEnd_5622861 962410115473543421392813 := by
  unfold tailWord_5622861
  simp only [CollatzResearch.WordTrace]
  refine ⟨205082588882342380049868437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136721725921561586699912291 205082588882342380049868437)
  ·
    refine ⟨9613246353859799064837583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 205082588882342380049868437 9613246353859799064837583)
    ·
      refine ⟨14419869530789698597256375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9613246353859799064837583 14419869530789698597256375)
      ·
        refine ⟨21629804296184547895884563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14419869530789698597256375 21629804296184547895884563)
        ·
          refine ⟨32444706444276821843826845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21629804296184547895884563 32444706444276821843826845)
          ·
            refine ⟨12166764916603808191435067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32444706444276821843826845 12166764916603808191435067)
            ·
              refine ⟨18250147374905712287152601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12166764916603808191435067 18250147374905712287152601)
              ·
                refine ⟨13687610531179284215364451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18250147374905712287152601 13687610531179284215364451)
                ·
                  refine ⟨20531415796768926323046677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13687610531179284215364451 20531415796768926323046677)
                  ·
                    refine ⟨962410115473543421392813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20531415796768926323046677 962410115473543421392813)
                    ·
                      rfl

theorem cell23_5622861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_5622861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622861 prefixEnd_5622861 := by exact prefixLift 5622861
  have htrace : WordTrace (prefixWord ++ tailWord_5622861) baseStart_5622861 baseEnd_5622861 := by
    simpa [prefixWord, tailWord_5622861, baseEnd_5622861] using wordTrace_append hprefix tailTrace_5622861
  have hstable : (prefixWord ++ tailWord_5622861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622861).length < 2 ^ (prefixWord ++ tailWord_5622861).sum := by decide
  have hdescent : baseEnd_5622861 < baseStart_5622861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622884 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 5, 3, 3]
def baseStart_5622884 : Nat := 118140960795 + 5622884 * 2 ^ 59
def prefixEnd_5622884 : Nat := 4983230072969 + 3 ^ 40 * 5622884 * 2
def baseEnd_5622884 : Nat := 2887242156475683674190833

theorem tailTrace_5622884 : CollatzResearch.WordTrace tailWord_5622884 prefixEnd_5622884 2887242156475683674190833 := by
  unfold tailWord_5622884
  simp only [CollatzResearch.WordTrace]
  refine ⟨102541713880629527488977853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136722285174172703318637137 102541713880629527488977853)
  ·
    refine ⟨38453142705236072808366695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102541713880629527488977853 38453142705236072808366695)
    ·
      refine ⟨57679714057854109212550043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38453142705236072808366695 57679714057854109212550043)
      ·
        refine ⟨86519571086781163818825065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57679714057854109212550043 86519571086781163818825065)
        ·
          refine ⟨64889678315085872864118799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86519571086781163818825065 64889678315085872864118799)
          ·
            refine ⟨97334517472628809296178199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64889678315085872864118799 97334517472628809296178199)
            ·
              refine ⟨146001776208943213944267299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97334517472628809296178199 146001776208943213944267299)
              ·
                refine ⟨219002664313414820916400949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146001776208943213944267299 219002664313414820916400949)
                ·
                  refine ⟨20531499779382639460912589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 219002664313414820916400949 20531499779382639460912589)
                  ·
                    refine ⟨7699312417268489797842221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20531499779382639460912589 7699312417268489797842221)
                    ·
                      refine ⟨2887242156475683674190833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7699312417268489797842221 2887242156475683674190833)
                      ·
                        rfl

theorem cell23_5622884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_5622884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622884 prefixEnd_5622884 := by exact prefixLift 5622884
  have htrace : WordTrace (prefixWord ++ tailWord_5622884) baseStart_5622884 baseEnd_5622884 := by
    simpa [prefixWord, tailWord_5622884, baseEnd_5622884] using wordTrace_append hprefix tailTrace_5622884
  have hstable : (prefixWord ++ tailWord_5622884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622884).length < 2 ^ (prefixWord ++ tailWord_5622884).sum := by decide
  have hdescent : baseEnd_5622884 < baseStart_5622884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622885 : List Nat := [1, 3, 1, 3, 2, 1, 3, 4, 1, 2, 2]
def baseStart_5622885 : Nat := 118140960795 + 5622885 * 2 ^ 59
def prefixEnd_5622885 : Nat := 4983230072969 + 3 ^ 40 * 5622885 * 2
def baseEnd_5622885 : Nat := 2887242669956338170278329

theorem tailTrace_5622885 : CollatzResearch.WordTrace tailWord_5622885 prefixEnd_5622885 2887242669956338170278329 := by
  unfold tailWord_5622885
  simp only [CollatzResearch.WordTrace]
  refine ⟨205083464234255432148742109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136722309489503621432494739 205083464234255432148742109)
  ·
    refine ⟨76906299087845787055778291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205083464234255432148742109 76906299087845787055778291)
    ·
      refine ⟨115359448631768680583667437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76906299087845787055778291 115359448631768680583667437)
      ·
        refine ⟨43259793236913255218875289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115359448631768680583667437 43259793236913255218875289)
        ·
          refine ⟨32444844927684941414156467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43259793236913255218875289 32444844927684941414156467)
          ·
            refine ⟨48667267391527412121234701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32444844927684941414156467 48667267391527412121234701)
            ·
              refine ⟨18250225271822779545463013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48667267391527412121234701 18250225271822779545463013)
              ·
                refine ⟨3421917238466771164774315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18250225271822779545463013 3421917238466771164774315)
                ·
                  refine ⟨5132875857700156747161473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3421917238466771164774315 5132875857700156747161473)
                  ·
                    refine ⟨3849656893275117560371105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5132875857700156747161473 3849656893275117560371105)
                    ·
                      refine ⟨2887242669956338170278329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3849656893275117560371105 2887242669956338170278329)
                      ·
                        rfl

theorem cell23_5622885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_5622885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622885 prefixEnd_5622885 := by exact prefixLift 5622885
  have htrace : WordTrace (prefixWord ++ tailWord_5622885) baseStart_5622885 baseEnd_5622885 := by
    simpa [prefixWord, tailWord_5622885, baseEnd_5622885] using wordTrace_append hprefix tailTrace_5622885
  have hstable : (prefixWord ++ tailWord_5622885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622885).length < 2 ^ (prefixWord ++ tailWord_5622885).sum := by decide
  have hdescent : baseEnd_5622885 < baseStart_5622885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622927 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 9]
def baseStart_5622927 : Nat := 118140960795 + 5622927 * 2 ^ 59
def prefixEnd_5622927 : Nat := 4983230072969 + 3 ^ 40 * 5622927 * 2
def baseEnd_5622927 : Nat := 2887264236143827005953135

theorem tailTrace_5622927 : CollatzResearch.WordTrace tailWord_5622927 prefixEnd_5622927 2887264236143827005953135 := by
  unfold tailWord_5622927
  simp only [CollatzResearch.WordTrace]
  refine ⟨205084996100103273321771035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136723330733402182214514023 205084996100103273321771035)
  ·
    refine ⟨307627494150154909982656553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205084996100103273321771035 307627494150154909982656553)
    ·
      refine ⟨230720620612616182486992415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307627494150154909982656553 230720620612616182486992415)
      ·
        refine ⟨346080930918924273730488623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230720620612616182486992415 346080930918924273730488623)
        ·
          refine ⟨519121396378386410595732935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346080930918924273730488623 519121396378386410595732935)
          ·
            refine ⟨778682094567579615893599403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519121396378386410595732935 778682094567579615893599403)
            ·
              refine ⟨1168023141851369423840399105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778682094567579615893599403 1168023141851369423840399105)
              ·
                refine ⟨876017356388527067880299329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1168023141851369423840399105 876017356388527067880299329)
                ·
                  refine ⟨657013017291395300910224497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 876017356388527067880299329 657013017291395300910224497)
                  ·
                    refine ⟨492759762968546475682668373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 657013017291395300910224497 492759762968546475682668373)
                    ·
                      refine ⟨2887264236143827005953135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 492759762968546475682668373 2887264236143827005953135)
                      ·
                        rfl

theorem cell23_5622927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_5622927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622927 prefixEnd_5622927 := by exact prefixLift 5622927
  have htrace : WordTrace (prefixWord ++ tailWord_5622927) baseStart_5622927 baseEnd_5622927 := by
    simpa [prefixWord, tailWord_5622927, baseEnd_5622927] using wordTrace_append hprefix tailTrace_5622927
  have hstable : (prefixWord ++ tailWord_5622927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622927).length < 2 ^ (prefixWord ++ tailWord_5622927).sum := by decide
  have hdescent : baseEnd_5622927 < baseStart_5622927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622935 : List Nat := [1, 1, 3, 3, 3, 3, 1, 2, 2, 1, 3]
def baseStart_5622935 : Nat := 118140960795 + 5622935 * 2 ^ 59
def prefixEnd_5622935 : Nat := 4983230072969 + 3 ^ 40 * 5622935 * 2
def baseEnd_5622935 : Nat := 2887268343989062974653099

theorem tailTrace_5622935 : CollatzResearch.WordTrace tailWord_5622935 prefixEnd_5622935 2887268343989062974653099 := by
  unfold tailWord_5622935
  simp only [CollatzResearch.WordTrace]
  refine ⟨205085287884074290688062259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136723525256049527125374839 205085287884074290688062259)
  ·
    refine ⟨307627931826111436032093389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205085287884074290688062259 307627931826111436032093389)
    ·
      refine ⟨115360474434791788512035021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307627931826111436032093389 115360474434791788512035021)
      ·
        refine ⟨43260177913046920692013133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115360474434791788512035021 43260177913046920692013133)
        ·
          refine ⟨16222566717392595259504925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43260177913046920692013133 16222566717392595259504925)
          ·
            refine ⟨6083462519022223222314347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16222566717392595259504925 6083462519022223222314347)
            ·
              refine ⟨9125193778533334833471521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6083462519022223222314347 9125193778533334833471521)
              ·
                refine ⟨6843895333900001125103641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9125193778533334833471521 6843895333900001125103641)
                ·
                  refine ⟨5132921500425000843827731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6843895333900001125103641 5132921500425000843827731)
                  ·
                    refine ⟨7699382250637501265741597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5132921500425000843827731 7699382250637501265741597)
                    ·
                      refine ⟨2887268343989062974653099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7699382250637501265741597 2887268343989062974653099)
                      ·
                        rfl

theorem cell23_5622935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_5622935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622935 prefixEnd_5622935 := by exact prefixLift 5622935
  have htrace : WordTrace (prefixWord ++ tailWord_5622935) baseStart_5622935 baseEnd_5622935 := by
    simpa [prefixWord, tailWord_5622935, baseEnd_5622935] using wordTrace_append hprefix tailTrace_5622935
  have hstable : (prefixWord ++ tailWord_5622935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622935).length < 2 ^ (prefixWord ++ tailWord_5622935).sum := by decide
  have hdescent : baseEnd_5622935 < baseStart_5622935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5622951 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 2, 6]
def baseStart_5622951 : Nat := 118140960795 + 5622951 * 2 ^ 59
def prefixEnd_5622951 : Nat := 4983230072969 + 3 ^ 40 * 5622951 * 2
def baseEnd_5622951 : Nat := 962425519893178304017675

theorem tailTrace_5622951 : CollatzResearch.WordTrace tailWord_5622951 prefixEnd_5622951 962425519893178304017675 := by
  unfold tailWord_5622951
  simp only [CollatzResearch.WordTrace]
  refine ⟨205085871452016325420644707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136723914301344216947096471 205085871452016325420644707)
  ·
    refine ⟨307628807178024488130967061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205085871452016325420644707 307628807178024488130967061)
    ·
      refine ⟨14420100336469897881139081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 307628807178024488130967061 14420100336469897881139081)
      ·
        refine ⟨10815075252352423410854311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14420100336469897881139081 10815075252352423410854311)
        ·
          refine ⟨16222612878528635116281467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10815075252352423410854311 16222612878528635116281467)
          ·
            refine ⟨24333919317792952674422201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16222612878528635116281467 24333919317792952674422201)
            ·
              refine ⟨18250439488344714505816651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24333919317792952674422201 18250439488344714505816651)
              ·
                refine ⟨27375659232517071758724977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18250439488344714505816651 27375659232517071758724977)
                ·
                  refine ⟨20531744424387803819043733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27375659232517071758724977 20531744424387803819043733)
                  ·
                    refine ⟨962425519893178304017675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20531744424387803819043733 962425519893178304017675)
                    ·
                      rfl

theorem cell23_5622951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_5622951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5622951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5622951 prefixEnd_5622951 := by exact prefixLift 5622951
  have htrace : WordTrace (prefixWord ++ tailWord_5622951) baseStart_5622951 baseEnd_5622951 := by
    simpa [prefixWord, tailWord_5622951, baseEnd_5622951] using wordTrace_append hprefix tailTrace_5622951
  have hstable : (prefixWord ++ tailWord_5622951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5622951).length < 2 ^ (prefixWord ++ tailWord_5622951).sum := by decide
  have hdescent : baseEnd_5622951 < baseStart_5622951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5622951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623001 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 2, 5, 2]
def baseStart_5623001 : Nat := 118140960795 + 5623001 * 2 ^ 59
def prefixEnd_5623001 : Nat := 4983230072969 + 3 ^ 40 * 5623001 * 2
def baseEnd_5623001 : Nat := 2887302233712259716427795

theorem tailTrace_5623001 : CollatzResearch.WordTrace tailWord_5623001 prefixEnd_5623001 2887302233712259716427795 := by
  unfold tailWord_5623001
  simp only [CollatzResearch.WordTrace]
  refine ⟨205087695101835183959964857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136725130067890122639976571 205087695101835183959964857)
  ·
    refine ⟨153815771326376387969973643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205087695101835183959964857 153815771326376387969973643)
    ·
      refine ⟨230723656989564581954960465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153815771326376387969973643 230723656989564581954960465)
      ·
        refine ⟨173042742742173436466220349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230723656989564581954960465 173042742742173436466220349)
        ·
          refine ⟨64891028528315038674832631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173042742742173436466220349 64891028528315038674832631)
          ·
            refine ⟨97336542792472558012248947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64891028528315038674832631 97336542792472558012248947)
            ·
              refine ⟨146004814188708837018373421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97336542792472558012248947 146004814188708837018373421)
              ·
                refine ⟨54751805320765813881890033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146004814188708837018373421 54751805320765813881890033)
                ·
                  refine ⟨41063853990574360411417525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54751805320765813881890033 41063853990574360411417525)
                  ·
                    refine ⟨3849736311616346288570393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41063853990574360411417525 3849736311616346288570393)
                    ·
                      refine ⟨2887302233712259716427795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3849736311616346288570393 2887302233712259716427795)
                      ·
                        rfl

theorem cell23_5623001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 5, 2].length) (baseStart_5623001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623001 prefixEnd_5623001 := by exact prefixLift 5623001
  have htrace : WordTrace (prefixWord ++ tailWord_5623001) baseStart_5623001 baseEnd_5623001 := by
    simpa [prefixWord, tailWord_5623001, baseEnd_5623001] using wordTrace_append hprefix tailTrace_5623001
  have hstable : (prefixWord ++ tailWord_5623001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623001).length < 2 ^ (prefixWord ++ tailWord_5623001).sum := by decide
  have hdescent : baseEnd_5623001 < baseStart_5623001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623031 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 1, 6, 2]
def baseStart_5623031 : Nat := 118140960795 + 5623031 * 2 ^ 59
def prefixEnd_5623031 : Nat := 4983230072969 + 3 ^ 40 * 5623031 * 2
def baseEnd_5623031 : Nat := 2887317638131894599052657

theorem tailTrace_5623031 : CollatzResearch.WordTrace tailWord_5623031 prefixEnd_5623031 2887317638131894599052657 := by
  unfold tailWord_5623031
  simp only [CollatzResearch.WordTrace]
  refine ⟨205088789291726499083556947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136725859527817666055704631 205088789291726499083556947)
  ·
    refine ⟨307633183937589748625335421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205088789291726499083556947 307633183937589748625335421)
    ·
      refine ⟨115362443976596155734500783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307633183937589748625335421 115362443976596155734500783)
      ·
        refine ⟨173043665964894233601751175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115362443976596155734500783 173043665964894233601751175)
        ·
          refine ⟨259565498947341350402626763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173043665964894233601751175 259565498947341350402626763)
          ·
            refine ⟨389348248421012025603940145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259565498947341350402626763 389348248421012025603940145)
            ·
              refine ⟨292011186315759019202955109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389348248421012025603940145 292011186315759019202955109)
              ·
                refine ⟨54752097434204816100554083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292011186315759019202955109 54752097434204816100554083)
                ·
                  refine ⟨82128146151307224150831125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54752097434204816100554083 82128146151307224150831125)
                  ·
                    refine ⟨3849756850842526132070209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82128146151307224150831125 3849756850842526132070209)
                    ·
                      refine ⟨2887317638131894599052657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3849756850842526132070209 2887317638131894599052657)
                      ·
                        rfl

theorem cell23_5623031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 6, 2].length) (baseStart_5623031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623031 prefixEnd_5623031 := by exact prefixLift 5623031
  have htrace : WordTrace (prefixWord ++ tailWord_5623031) baseStart_5623031 baseEnd_5623031 := by
    simpa [prefixWord, tailWord_5623031, baseEnd_5623031] using wordTrace_append hprefix tailTrace_5623031
  have hstable : (prefixWord ++ tailWord_5623031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623031).length < 2 ^ (prefixWord ++ tailWord_5623031).sum := by decide
  have hdescent : baseEnd_5623031 < baseStart_5623031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623085 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_5623085 : Nat := 118140960795 + 5623085 * 2 ^ 59
def prefixEnd_5623085 : Nat := 4983230072969 + 3 ^ 40 * 5623085 * 2
def baseEnd_5623085 : Nat := 2887345366087237387777409

theorem tailTrace_5623085 : CollatzResearch.WordTrace tailWord_5623085 prefixEnd_5623085 2887345366087237387777409 := by
  unfold tailWord_5623085
  simp only [CollatzResearch.WordTrace]
  refine ⟨205090758833530866306022709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136727172555687244204015139 205090758833530866306022709)
  ·
    refine ⟨19227258640643518716189629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 205090758833530866306022709 19227258640643518716189629)
    ·
      refine ⟨7210221990241319518571111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19227258640643518716189629 7210221990241319518571111)
      ·
        refine ⟨10815332985361979277856667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7210221990241319518571111 10815332985361979277856667)
        ·
          refine ⟨16222999478042968916785001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10815332985361979277856667 16222999478042968916785001)
          ·
            refine ⟨12167249608532226687588751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16222999478042968916785001 12167249608532226687588751)
            ·
              refine ⟨18250874412798340031383127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12167249608532226687588751 18250874412798340031383127)
              ·
                refine ⟨27376311619197510047074691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18250874412798340031383127 27376311619197510047074691)
                ·
                  refine ⟨41064467428796265070612037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27376311619197510047074691 41064467428796265070612037)
                  ·
                    refine ⟨7699587642899299700739757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41064467428796265070612037 7699587642899299700739757)
                    ·
                      refine ⟨2887345366087237387777409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7699587642899299700739757 2887345366087237387777409)
                      ·
                        rfl

theorem cell23_5623085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_5623085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623085 prefixEnd_5623085 := by exact prefixLift 5623085
  have htrace : WordTrace (prefixWord ++ tailWord_5623085) baseStart_5623085 baseEnd_5623085 := by
    simpa [prefixWord, tailWord_5623085, baseEnd_5623085] using wordTrace_append hprefix tailTrace_5623085
  have hstable : (prefixWord ++ tailWord_5623085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623085).length < 2 ^ (prefixWord ++ tailWord_5623085).sum := by decide
  have hdescent : baseEnd_5623085 < baseStart_5623085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623092 : List Nat := [2, 5, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_5623092 : Nat := 118140960795 + 5623092 * 2 ^ 59
def prefixEnd_5623092 : Nat := 4983230072969 + 3 ^ 40 * 5623092 * 2
def baseEnd_5623092 : Nat := 962449653483939620129959

theorem tailTrace_5623092 : CollatzResearch.WordTrace tailWord_5623092 prefixEnd_5623092 962449653483939620129959 := by
  unfold tailWord_5623092
  simp only [CollatzResearch.WordTrace]
  refine ⟨102545507072252753250763765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136727342763003671001018353 102545507072252753250763765)
  ·
    refine ⟨9613641288023695617259103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102545507072252753250763765 9613641288023695617259103)
    ·
      refine ⟨14420461932035543425888655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9613641288023695617259103 14420461932035543425888655)
      ·
        refine ⟨21630692898053315138832983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14420461932035543425888655 21630692898053315138832983)
        ·
          refine ⟨32446039347079972708249475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21630692898053315138832983 32446039347079972708249475)
          ·
            refine ⟨48669059020619959062374213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32446039347079972708249475 48669059020619959062374213)
            ·
              refine ⟨9125448566366242324195165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48669059020619959062374213 9125448566366242324195165)
              ·
                refine ⟨3422043212387340871573187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9125448566366242324195165 3422043212387340871573187)
                ·
                  refine ⟨5133064818581011307359781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3422043212387340871573187 5133064818581011307359781)
                  ·
                    refine ⟨962449653483939620129959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5133064818581011307359781 962449653483939620129959)
                    ·
                      rfl

theorem cell23_5623092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_5623092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623092 prefixEnd_5623092 := by exact prefixLift 5623092
  have htrace : WordTrace (prefixWord ++ tailWord_5623092) baseStart_5623092 baseEnd_5623092 := by
    simpa [prefixWord, tailWord_5623092, baseEnd_5623092] using wordTrace_append hprefix tailTrace_5623092
  have hstable : (prefixWord ++ tailWord_5623092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623092).length < 2 ^ (prefixWord ++ tailWord_5623092).sum := by decide
  have hdescent : baseEnd_5623092 < baseStart_5623092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623098 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3]
def baseStart_5623098 : Nat := 118140960795 + 5623098 * 2 ^ 59
def prefixEnd_5623098 : Nat := 4983230072969 + 3 ^ 40 * 5623098 * 2
def baseEnd_5623098 : Nat := 2887352041335745836914849

theorem tailTrace_5623098 : CollatzResearch.WordTrace tailWord_5623098 prefixEnd_5623098 2887352041335745836914849 := by
  unfold tailWord_5623098
  simp only [CollatzResearch.WordTrace]
  refine ⟨51272808245620942381561487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136727488654989179684163965 51272808245620942381561487)
  ·
    refine ⟨76909212368431413572342231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51272808245620942381561487 76909212368431413572342231)
    ·
      refine ⟨115363818552647120358513347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76909212368431413572342231 115363818552647120358513347)
      ·
        refine ⟨173045727828970680537770021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115363818552647120358513347 173045727828970680537770021)
        ·
          refine ⟨32446073967932002600831879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173045727828970680537770021 32446073967932002600831879)
          ·
            refine ⟨48669110951898003901247819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32446073967932002600831879 48669110951898003901247819)
            ·
              refine ⟨73003666427847005851871729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48669110951898003901247819 73003666427847005851871729)
              ·
                refine ⟨54752749820885254388903797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73003666427847005851871729 54752749820885254388903797)
                ·
                  refine ⟨5133070295707992598959731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54752749820885254388903797 5133070295707992598959731)
                  ·
                    refine ⟨7699605443561988898439597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5133070295707992598959731 7699605443561988898439597)
                    ·
                      refine ⟨2887352041335745836914849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7699605443561988898439597 2887352041335745836914849)
                      ·
                        rfl

theorem cell23_5623098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_5623098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623098 prefixEnd_5623098 := by exact prefixLift 5623098
  have htrace : WordTrace (prefixWord ++ tailWord_5623098) baseStart_5623098 baseEnd_5623098 := by
    simpa [prefixWord, tailWord_5623098, baseEnd_5623098] using wordTrace_append hprefix tailTrace_5623098
  have hstable : (prefixWord ++ tailWord_5623098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623098).length < 2 ^ (prefixWord ++ tailWord_5623098).sum := by decide
  have hdescent : baseEnd_5623098 < baseStart_5623098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623105 : List Nat := [1, 2, 5, 2, 1, 3, 1, 2, 6]
def baseStart_5623105 : Nat := 118140960795 + 5623105 * 2 ^ 59
def prefixEnd_5623105 : Nat := 4983230072969 + 3 ^ 40 * 5623105 * 2
def baseEnd_5623105 : Nat := 320817292855591923280813

theorem tailTrace_5623105 : CollatzResearch.WordTrace tailWord_5623105 prefixEnd_5623105 320817292855591923280813 := by
  unfold tailWord_5623105
  simp only [CollatzResearch.WordTrace]
  refine ⟨205091488293458409721750769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136727658862305606481167179 205091488293458409721750769)
  ·
    refine ⟨153818616220093807291313077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205091488293458409721750769 153818616220093807291313077)
    ·
      refine ⟨14420495270633794433560601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153818616220093807291313077 14420495270633794433560601)
      ·
        refine ⟨10815371452975345825170451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14420495270633794433560601 10815371452975345825170451)
        ·
          refine ⟨16223057179463018737755677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10815371452975345825170451 16223057179463018737755677)
          ·
            refine ⟨6083646442298632026658379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16223057179463018737755677 6083646442298632026658379)
            ·
              refine ⟨9125469663447948039987569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6083646442298632026658379 9125469663447948039987569)
              ·
                refine ⟨6844102247585961029990677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9125469663447948039987569 6844102247585961029990677)
                ·
                  refine ⟨320817292855591923280813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6844102247585961029990677 320817292855591923280813)
                  ·
                    rfl

theorem cell23_5623105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 6].length) (baseStart_5623105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623105 prefixEnd_5623105 := by exact prefixLift 5623105
  have htrace : WordTrace (prefixWord ++ tailWord_5623105) baseStart_5623105 baseEnd_5623105 := by
    simpa [prefixWord, tailWord_5623105, baseEnd_5623105] using wordTrace_append hprefix tailTrace_5623105
  have hstable : (prefixWord ++ tailWord_5623105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623105).length < 2 ^ (prefixWord ++ tailWord_5623105).sum := by decide
  have hdescent : baseEnd_5623105 < baseStart_5623105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623108 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_5623108 : Nat := 118140960795 + 5623108 * 2 ^ 59
def prefixEnd_5623108 : Nat := 4983230072969 + 3 ^ 40 * 5623108 * 2
def baseEnd_5623108 : Nat := 2887357176142290797789803

theorem tailTrace_5623108 : CollatzResearch.WordTrace tailWord_5623108 prefixEnd_5623108 2887357176142290797789803 := by
  unfold tailWord_5623108
  simp only [CollatzResearch.WordTrace]
  refine ⟨102545798856223770617054989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136727731808298360822739985 102545798856223770617054989)
  ·
    refine ⟨38454674571083913981395621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102545798856223770617054989 38454674571083913981395621)
    ·
      refine ⟨7210251482078233871511679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38454674571083913981395621 7210251482078233871511679)
      ·
        refine ⟨10815377223117350807267519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7210251482078233871511679 10815377223117350807267519)
        ·
          refine ⟨16223065834676026210901279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10815377223117350807267519 16223065834676026210901279)
          ·
            refine ⟨24334598752014039316351919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16223065834676026210901279 24334598752014039316351919)
            ·
              refine ⟨36501898128021058974527879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24334598752014039316351919 36501898128021058974527879)
              ·
                refine ⟨54752847192031588461791819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36501898128021058974527879 54752847192031588461791819)
                ·
                  refine ⟨82129270788047382692687729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54752847192031588461791819 82129270788047382692687729)
                  ·
                    refine ⟨61596953091035537019515797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82129270788047382692687729 61596953091035537019515797)
                    ·
                      refine ⟨2887357176142290797789803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61596953091035537019515797 2887357176142290797789803)
                      ·
                        rfl

theorem cell23_5623108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_5623108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623108 prefixEnd_5623108 := by exact prefixLift 5623108
  have htrace : WordTrace (prefixWord ++ tailWord_5623108) baseStart_5623108 baseEnd_5623108 := by
    simpa [prefixWord, tailWord_5623108, baseEnd_5623108] using wordTrace_append hprefix tailTrace_5623108
  have hstable : (prefixWord ++ tailWord_5623108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623108).length < 2 ^ (prefixWord ++ tailWord_5623108).sum := by decide
  have hdescent : baseEnd_5623108 < baseStart_5623108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623141 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 3, 1, 5]
def baseStart_5623141 : Nat := 118140960795 + 5623141 * 2 ^ 59
def prefixEnd_5623141 : Nat := 4983230072969 + 3 ^ 40 * 5623141 * 2
def baseEnd_5623141 : Nat := 2887374121003889168677151

theorem tailTrace_5623141 : CollatzResearch.WordTrace tailWord_5623141 prefixEnd_5623141 2887374121003889168677151 := by
  unfold tailWord_5623141
  simp only [CollatzResearch.WordTrace]
  refine ⟨205092801321327987870061277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136728534214218658580040851 205092801321327987870061277)
  ·
    refine ⟨76909800495497995451272979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205092801321327987870061277 76909800495497995451272979)
    ·
      refine ⟨115364700743246993176909469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76909800495497995451272979 115364700743246993176909469)
      ·
        refine ⟨43261762778717622441341051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115364700743246993176909469 43261762778717622441341051)
        ·
          refine ⟨64892644168076433662011577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43261762778717622441341051 64892644168076433662011577)
          ·
            refine ⟨48669483126057325246508683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64892644168076433662011577 48669483126057325246508683)
            ·
              refine ⟨73004224689085987869763025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48669483126057325246508683 73004224689085987869763025)
              ·
                refine ⟨54753168516814490902322269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73004224689085987869763025 54753168516814490902322269)
                ·
                  refine ⟨20532438193805434088370851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54753168516814490902322269 20532438193805434088370851)
                  ·
                    refine ⟨30798657290708151132556277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20532438193805434088370851 30798657290708151132556277)
                    ·
                      refine ⟨2887374121003889168677151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30798657290708151132556277 2887374121003889168677151)
                      ·
                        rfl

theorem cell23_5623141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_5623141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623141 prefixEnd_5623141 := by exact prefixLift 5623141
  have htrace : WordTrace (prefixWord ++ tailWord_5623141) baseStart_5623141 baseEnd_5623141 := by
    simpa [prefixWord, tailWord_5623141, baseEnd_5623141] using wordTrace_append hprefix tailTrace_5623141
  have hstable : (prefixWord ++ tailWord_5623141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623141).length < 2 ^ (prefixWord ++ tailWord_5623141).sum := by decide
  have hdescent : baseEnd_5623141 < baseStart_5623141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623148 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 4, 4]
def baseStart_5623148 : Nat := 118140960795 + 5623148 * 2 ^ 59
def prefixEnd_5623148 : Nat := 4983230072969 + 3 ^ 40 * 5623148 * 2
def baseEnd_5623148 : Nat := 962459238456156880429873

theorem tailTrace_5623148 : CollatzResearch.WordTrace tailWord_5623148 prefixEnd_5623148 962459238456156880429873 := by
  unfold tailWord_5623148
  simp only [CollatzResearch.WordTrace]
  refine ⟨102546528316151314032783049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136728704421535085377044065 102546528316151314032783049)
  ·
    refine ⟨76909896237113485524587287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102546528316151314032783049 76909896237113485524587287)
    ·
      refine ⟨115364844355670228286880931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76909896237113485524587287 115364844355670228286880931)
      ·
        refine ⟨173047266533505342430321397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115364844355670228286880931 173047266533505342430321397)
        ·
          refine ⟨16223181237516125852842631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173047266533505342430321397 16223181237516125852842631)
          ·
            refine ⟨24334771856274188779263947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16223181237516125852842631 24334771856274188779263947)
            ·
              refine ⟨36502157784411283168895921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24334771856274188779263947 36502157784411283168895921)
              ·
                refine ⟨27376618338308462376671941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36502157784411283168895921 27376618338308462376671941)
                ·
                  refine ⟨5133115938432836695625989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27376618338308462376671941 5133115938432836695625989)
                  ·
                    refine ⟨962459238456156880429873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5133115938432836695625989 962459238456156880429873)
                    ·
                      rfl

theorem cell23_5623148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_5623148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623148 prefixEnd_5623148 := by exact prefixLift 5623148
  have htrace : WordTrace (prefixWord ++ tailWord_5623148) baseStart_5623148 baseEnd_5623148 := by
    simpa [prefixWord, tailWord_5623148, baseEnd_5623148] using wordTrace_append hprefix tailTrace_5623148
  have hstable : (prefixWord ++ tailWord_5623148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623148).length < 2 ^ (prefixWord ++ tailWord_5623148).sum := by decide
  have hdescent : baseEnd_5623148 < baseStart_5623148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623149 : List Nat := [1, 5, 1, 1, 1, 5, 1, 3, 1, 1, 3]
def baseStart_5623149 : Nat := 118140960795 + 5623149 * 2 ^ 59
def prefixEnd_5623149 : Nat := 4983230072969 + 3 ^ 40 * 5623149 * 2
def baseEnd_5623149 : Nat := 2887378228849125137377115

theorem tailTrace_5623149 : CollatzResearch.WordTrace tailWord_5623149 prefixEnd_5623149 2887378228849125137377115 := by
  unfold tailWord_5623149
  simp only [CollatzResearch.WordTrace]
  refine ⟨205093093105299005236352501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136728728736866003490901667 205093093105299005236352501)
  ·
    refine ⟨19227477478621781740908047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 205093093105299005236352501 19227477478621781740908047)
    ·
      refine ⟨28841216217932672611362071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19227477478621781740908047 28841216217932672611362071)
      ·
        refine ⟨43261824326899008917043107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28841216217932672611362071 43261824326899008917043107)
        ·
          refine ⟨64892736490348513375564661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43261824326899008917043107 64892736490348513375564661)
          ·
            refine ⟨6083694045970173128959187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64892736490348513375564661 6083694045970173128959187)
            ·
              refine ⟨9125541068955259693438781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6083694045970173128959187 9125541068955259693438781)
              ·
                refine ⟨3422077900858222385039543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9125541068955259693438781 3422077900858222385039543)
                ·
                  refine ⟨5133116851287333577559315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3422077900858222385039543 5133116851287333577559315)
                  ·
                    refine ⟨7699675276931000366338973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5133116851287333577559315 7699675276931000366338973)
                    ·
                      refine ⟨2887378228849125137377115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7699675276931000366338973 2887378228849125137377115)
                      ·
                        rfl

theorem cell23_5623149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_5623149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623149 prefixEnd_5623149 := by exact prefixLift 5623149
  have htrace : WordTrace (prefixWord ++ tailWord_5623149) baseStart_5623149 baseEnd_5623149 := by
    simpa [prefixWord, tailWord_5623149, baseEnd_5623149] using wordTrace_append hprefix tailTrace_5623149
  have hstable : (prefixWord ++ tailWord_5623149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623149).length < 2 ^ (prefixWord ++ tailWord_5623149).sum := by decide
  have hdescent : baseEnd_5623149 < baseStart_5623149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623151 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 4]
def baseStart_5623151 : Nat := 118140960795 + 5623151 * 2 ^ 59
def prefixEnd_5623151 : Nat := 4983230072969 + 3 ^ 40 * 5623151 * 2
def baseEnd_5623151 : Nat := 2887379255810434129552105

theorem tailTrace_5623151 : CollatzResearch.WordTrace tailWord_5623151 prefixEnd_5623151 2887379255810434129552105 := by
  unfold tailWord_5623151
  simp only [CollatzResearch.WordTrace]
  refine ⟨205093166051291759577925307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136728777367527839718616871 205093166051291759577925307)
  ·
    refine ⟨307639749076937639366887961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205093166051291759577925307 307639749076937639366887961)
    ·
      refine ⟨230729811807703229525165971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307639749076937639366887961 230729811807703229525165971)
      ·
        refine ⟨346094717711554844287748957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230729811807703229525165971 346094717711554844287748957)
        ·
          refine ⟨129785519141833066607905859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346094717711554844287748957 129785519141833066607905859)
          ·
            refine ⟨194678278712749599911858789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129785519141833066607905859 194678278712749599911858789)
            ·
              refine ⟨36502177258640549983473523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194678278712749599911858789 36502177258640549983473523)
              ·
                refine ⟨54753265887960824975210285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36502177258640549983473523 54753265887960824975210285)
                ·
                  refine ⟨20532474707985309365703857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54753265887960824975210285 20532474707985309365703857)
                  ·
                    refine ⟨15399356030988982024277893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20532474707985309365703857 15399356030988982024277893)
                    ·
                      refine ⟨2887379255810434129552105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15399356030988982024277893 2887379255810434129552105)
                      ·
                        rfl

theorem cell23_5623151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_5623151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623151 prefixEnd_5623151 := by exact prefixLift 5623151
  have htrace : WordTrace (prefixWord ++ tailWord_5623151) baseStart_5623151 baseEnd_5623151 := by
    simpa [prefixWord, tailWord_5623151, baseEnd_5623151] using wordTrace_append hprefix tailTrace_5623151
  have hstable : (prefixWord ++ tailWord_5623151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623151).length < 2 ^ (prefixWord ++ tailWord_5623151).sum := by decide
  have hdescent : baseEnd_5623151 < baseStart_5623151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623166 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_5623166 : Nat := 118140960795 + 5623166 * 2 ^ 59
def prefixEnd_5623166 : Nat := 4983230072969 + 3 ^ 40 * 5623166 * 2
def baseEnd_5623166 : Nat := 2887386958020251570864537

theorem tailTrace_5623166 : CollatzResearch.WordTrace tailWord_5623166 prefixEnd_5623166 2887386958020251570864537 := by
  unfold tailWord_5623166
  simp only [CollatzResearch.WordTrace]
  refine ⟨25636714143279677142465169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136729142097491611426480901 25636714143279677142465169)
  ·
    refine ⟨19227535607459757856848877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25636714143279677142465169 19227535607459757856848877)
    ·
      refine ⟨7210325852797409196318329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19227535607459757856848877 7210325852797409196318329)
      ·
        refine ⟨5407744389598056897238747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7210325852797409196318329 5407744389598056897238747)
        ·
          refine ⟨8111616584397085345858121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5407744389598056897238747 8111616584397085345858121)
          ·
            refine ⟨6083712438297814009393591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8111616584397085345858121 6083712438297814009393591)
            ·
              refine ⟨9125568657446721014090387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6083712438297814009393591 9125568657446721014090387)
              ·
                refine ⟨13688352986170081521135581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9125568657446721014090387 13688352986170081521135581)
                ·
                  refine ⟨5133132369813780570425843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13688352986170081521135581 5133132369813780570425843)
                  ·
                    refine ⟨7699698554720670855638765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5133132369813780570425843 7699698554720670855638765)
                    ·
                      refine ⟨2887386958020251570864537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7699698554720670855638765 2887386958020251570864537)
                      ·
                        rfl

theorem cell23_5623166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_5623166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623166 prefixEnd_5623166 := by exact prefixLift 5623166
  have htrace : WordTrace (prefixWord ++ tailWord_5623166) baseStart_5623166 baseEnd_5623166 := by
    simpa [prefixWord, tailWord_5623166, baseEnd_5623166] using wordTrace_append hprefix tailTrace_5623166
  have hstable : (prefixWord ++ tailWord_5623166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623166).length < 2 ^ (prefixWord ++ tailWord_5623166).sum := by decide
  have hdescent : baseEnd_5623166 < baseStart_5623166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623172 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 3, 2, 2]
def baseStart_5623172 : Nat := 118140960795 + 5623172 * 2 ^ 59
def prefixEnd_5623172 : Nat := 4983230072969 + 3 ^ 40 * 5623172 * 2
def baseEnd_5623172 : Nat := 2887390038904178547389509

theorem tailTrace_5623172 : CollatzResearch.WordTrace tailWord_5623172 prefixEnd_5623172 2887390038904178547389509 := by
  unfold tailWord_5623172
  simp only [CollatzResearch.WordTrace]
  refine ⟨102546965992107840082219885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136729287989477120109626513 102546965992107840082219885)
  ·
    refine ⟨38455112247040440030832457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102546965992107840082219885 38455112247040440030832457)
    ·
      refine ⟨28841334185280330023124343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38455112247040440030832457 28841334185280330023124343)
      ·
        refine ⟨43262001277920495034686515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28841334185280330023124343 43262001277920495034686515)
        ·
          refine ⟨64893001916880742552029773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43262001277920495034686515 64893001916880742552029773)
          ·
            refine ⟨24334875718830278457011165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64893001916880742552029773 24334875718830278457011165)
            ·
              refine ⟨9125578394561354421379187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24334875718830278457011165 9125578394561354421379187)
              ·
                refine ⟨13688367591842031632068781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9125578394561354421379187 13688367591842031632068781)
                ·
                  refine ⟨5133137846940761862025793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13688367591842031632068781 5133137846940761862025793)
                  ·
                    refine ⟨3849853385205571396519345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5133137846940761862025793 3849853385205571396519345)
                    ·
                      refine ⟨2887390038904178547389509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3849853385205571396519345 2887390038904178547389509)
                      ·
                        rfl

theorem cell23_5623172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_5623172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623172 prefixEnd_5623172 := by exact prefixLift 5623172
  have htrace : WordTrace (prefixWord ++ tailWord_5623172) baseStart_5623172 baseEnd_5623172 := by
    simpa [prefixWord, tailWord_5623172, baseEnd_5623172] using wordTrace_append hprefix tailTrace_5623172
  have hstable : (prefixWord ++ tailWord_5623172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623172).length < 2 ^ (prefixWord ++ tailWord_5623172).sum := by decide
  have hdescent : baseEnd_5623172 < baseStart_5623172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623182 : List Nat := [4, 1, 1, 4, 2, 1, 1, 3, 2, 4]
def baseStart_5623182 : Nat := 118140960795 + 5623182 * 2 ^ 59
def prefixEnd_5623182 : Nat := 4983230072969 + 3 ^ 40 * 5623182 * 2
def baseEnd_5623182 : Nat := 962465057903574502754821

theorem tailTrace_5623182 : CollatzResearch.WordTrace tailWord_5623182 prefixEnd_5623182 962465057903574502754821 := by
  unfold tailWord_5623182
  simp only [CollatzResearch.WordTrace]
  refine ⟨25636787089272431484037975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136729531142786301248202533 25636787089272431484037975)
  ·
    refine ⟨38455180633908647226056963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25636787089272431484037975 38455180633908647226056963)
    ·
      refine ⟨57682770950862970839085445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38455180633908647226056963 57682770950862970839085445)
      ·
        refine ⟨10815519553286807032328521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57682770950862970839085445 10815519553286807032328521)
        ·
          refine ⟨8111639664965105274246391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10815519553286807032328521 8111639664965105274246391)
          ·
            refine ⟨12167459497447657911369587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8111639664965105274246391 12167459497447657911369587)
            ·
              refine ⟨18251189246171486867054381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12167459497447657911369587 18251189246171486867054381)
              ·
                refine ⟨6844195967314307575145393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18251189246171486867054381 6844195967314307575145393)
                ·
                  refine ⟨5133146975485730681359045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6844195967314307575145393 5133146975485730681359045)
                  ·
                    refine ⟨962465057903574502754821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5133146975485730681359045 962465057903574502754821)
                    ·
                      rfl

theorem cell23_5623182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_5623182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623182 prefixEnd_5623182 := by exact prefixLift 5623182
  have htrace : WordTrace (prefixWord ++ tailWord_5623182) baseStart_5623182 baseEnd_5623182 := by
    simpa [prefixWord, tailWord_5623182, baseEnd_5623182] using wordTrace_append hprefix tailTrace_5623182
  have hstable : (prefixWord ++ tailWord_5623182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623182).length < 2 ^ (prefixWord ++ tailWord_5623182).sum := by decide
  have hdescent : baseEnd_5623182 < baseStart_5623182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623215 : List Nat := [1, 1, 2, 1, 2, 2, 1, 7, 1, 3, 2]
def baseStart_5623215 : Nat := 118140960795 + 5623215 * 2 ^ 59
def prefixEnd_5623215 : Nat := 4983230072969 + 3 ^ 40 * 5623215 * 2
def baseEnd_5623215 : Nat := 2887412118572321879151811

theorem tailTrace_5623215 : CollatzResearch.WordTrace tailWord_5623215 prefixEnd_5623215 2887412118572321879151811 := by
  unfold tailWord_5623215
  simp only [CollatzResearch.WordTrace]
  refine ⟨205095500323059898508255099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136730333548706599005503399 205095500323059898508255099)
  ·
    refine ⟨307643250484589847762382649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205095500323059898508255099 307643250484589847762382649)
    ·
      refine ⟨230732437863442385821786987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307643250484589847762382649 230732437863442385821786987)
      ·
        refine ⟨346098656795163578732680481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230732437863442385821786987 346098656795163578732680481)
        ·
          refine ⟨259573992596372684049510361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346098656795163578732680481 259573992596372684049510361)
          ·
            refine ⟨194680494447279513037132771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259573992596372684049510361 194680494447279513037132771)
            ·
              refine ⟨292020741670919269555699157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194680494447279513037132771 292020741670919269555699157)
              ·
                refine ⟨6844236132912170380211699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 292020741670919269555699157 6844236132912170380211699)
                ·
                  refine ⟨10266354199368255570317549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6844236132912170380211699 10266354199368255570317549)
                  ·
                    refine ⟨3849882824763095838869081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10266354199368255570317549 3849882824763095838869081)
                    ·
                      refine ⟨2887412118572321879151811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3849882824763095838869081 2887412118572321879151811)
                      ·
                        rfl

theorem cell23_5623215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 3, 2].length) (baseStart_5623215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623215 prefixEnd_5623215 := by exact prefixLift 5623215
  have htrace : WordTrace (prefixWord ++ tailWord_5623215) baseStart_5623215 baseEnd_5623215 := by
    simpa [prefixWord, tailWord_5623215, baseEnd_5623215] using wordTrace_append hprefix tailTrace_5623215
  have hstable : (prefixWord ++ tailWord_5623215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623215).length < 2 ^ (prefixWord ++ tailWord_5623215).sum := by decide
  have hdescent : baseEnd_5623215 < baseStart_5623215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623231 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 5]
def baseStart_5623231 : Nat := 118140960795 + 5623231 * 2 ^ 59
def prefixEnd_5623231 : Nat := 4983230072969 + 3 ^ 40 * 5623231 * 2
def baseEnd_5623231 : Nat := 2887420334262793816551737

theorem tailTrace_5623231 : CollatzResearch.WordTrace tailWord_5623231 prefixEnd_5623231 2887420334262793816551737 := by
  unfold tailWord_5623231
  simp only [CollatzResearch.WordTrace]
  refine ⟨205096083891001933240837547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136730722594001288827225031 205096083891001933240837547)
  ·
    refine ⟨307644125836502899861256321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205096083891001933240837547 307644125836502899861256321)
    ·
      refine ⟨230733094377377174895942241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307644125836502899861256321 230733094377377174895942241)
      ·
        refine ⟨173049820783032881171956681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230733094377377174895942241 173049820783032881171956681)
        ·
          refine ⟨129787365587274660878967511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173049820783032881171956681 129787365587274660878967511)
          ·
            refine ⟨194681048380911991318451267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129787365587274660878967511 194681048380911991318451267)
            ·
              refine ⟨292021572571367986977676901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194681048380911991318451267 292021572571367986977676901)
              ·
                refine ⟨54754044857131497558314419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292021572571367986977676901 54754044857131497558314419)
                ·
                  refine ⟨82131067285697246337471629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54754044857131497558314419 82131067285697246337471629)
                  ·
                    refine ⟨30799150232136467376551861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82131067285697246337471629 30799150232136467376551861)
                    ·
                      refine ⟨2887420334262793816551737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30799150232136467376551861 2887420334262793816551737)
                      ·
                        rfl

theorem cell23_5623231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_5623231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623231 prefixEnd_5623231 := by exact prefixLift 5623231
  have htrace : WordTrace (prefixWord ++ tailWord_5623231) baseStart_5623231 baseEnd_5623231 := by
    simpa [prefixWord, tailWord_5623231, baseEnd_5623231] using wordTrace_append hprefix tailTrace_5623231
  have hstable : (prefixWord ++ tailWord_5623231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623231).length < 2 ^ (prefixWord ++ tailWord_5623231).sum := by decide
  have hdescent : baseEnd_5623231 < baseStart_5623231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623285 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 7]
def baseStart_5623285 : Nat := 118140960795 + 5623285 * 2 ^ 59
def prefixEnd_5623285 : Nat := 4983230072969 + 3 ^ 40 * 5623285 * 2
def baseEnd_5623285 : Nat := 320827562468681845030721

theorem tailTrace_5623285 : CollatzResearch.WordTrace tailWord_5623285 prefixEnd_5623285 320827562468681845030721 := by
  unfold tailWord_5623285
  simp only [CollatzResearch.WordTrace]
  refine ⟨205098053432806300463303309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136732035621870866975535539 205098053432806300463303309)
  ·
    refine ⟨76911770037302362673738741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205098053432806300463303309 76911770037302362673738741)
    ·
      refine ⟨7210478440997096500663007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76911770037302362673738741 7210478440997096500663007)
      ·
        refine ⟨10815717661495644750994511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7210478440997096500663007 10815717661495644750994511)
        ·
          refine ⟨16223576492243467126491767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10815717661495644750994511 16223576492243467126491767)
          ·
            refine ⟨24335364738365200689737651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16223576492243467126491767 24335364738365200689737651)
            ·
              refine ⟨36503047107547801034606477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24335364738365200689737651 36503047107547801034606477)
              ·
                refine ⟨13688642665330425387977429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36503047107547801034606477 13688642665330425387977429)
                ·
                  refine ⟨320827562468681845030721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13688642665330425387977429 320827562468681845030721)
                  ·
                    rfl

theorem cell23_5623285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 7].length) (baseStart_5623285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623285 prefixEnd_5623285 := by exact prefixLift 5623285
  have htrace : WordTrace (prefixWord ++ tailWord_5623285) baseStart_5623285 baseEnd_5623285 := by
    simpa [prefixWord, tailWord_5623285, baseEnd_5623285] using wordTrace_append hprefix tailTrace_5623285
  have hstable : (prefixWord ++ tailWord_5623285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623285).length < 2 ^ (prefixWord ++ tailWord_5623285).sum := by decide
  have hdescent : baseEnd_5623285 < baseStart_5623285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623372 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 2, 2, 3]
def baseStart_5623372 : Nat := 118140960795 + 5623372 * 2 ^ 59
def prefixEnd_5623372 : Nat := 4983230072969 + 3 ^ 40 * 5623372 * 2
def baseEnd_5623372 : Nat := 2887492735035077764888589

theorem tailTrace_5623372 : CollatzResearch.WordTrace tailWord_5623372 prefixEnd_5623372 2887492735035077764888589 := by
  unfold tailWord_5623372
  simp only [CollatzResearch.WordTrace]
  refine ⟨102550613291745557160860185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136734151055660742881146913 102550613291745557160860185)
  ·
    refine ⟨76912959968809167870645139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102550613291745557160860185 76912959968809167870645139)
    ·
      refine ⟨115369439953213751805967709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76912959968809167870645139 115369439953213751805967709)
      ·
        refine ⟨43263539982455156927237891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115369439953213751805967709 43263539982455156927237891)
        ·
          refine ⟨64895309973682735390856837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43263539982455156927237891 64895309973682735390856837)
          ·
            refine ⟨12167870620065512885785657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64895309973682735390856837 12167870620065512885785657)
            ·
              refine ⟨9125902965049134664339243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12167870620065512885785657 9125902965049134664339243)
              ·
                refine ⟨13688854447573701996508865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9125902965049134664339243 13688854447573701996508865)
                ·
                  refine ⟨10266640835680276497381649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13688854447573701996508865 10266640835680276497381649)
                  ·
                    refine ⟨7699980626760207373036237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10266640835680276497381649 7699980626760207373036237)
                    ·
                      refine ⟨2887492735035077764888589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7699980626760207373036237 2887492735035077764888589)
                      ·
                        rfl

theorem cell23_5623372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_5623372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623372 prefixEnd_5623372 := by exact prefixLift 5623372
  have htrace : WordTrace (prefixWord ++ tailWord_5623372) baseStart_5623372 baseEnd_5623372 := by
    simpa [prefixWord, tailWord_5623372, baseEnd_5623372] using wordTrace_append hprefix tailTrace_5623372
  have hstable : (prefixWord ++ tailWord_5623372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623372).length < 2 ^ (prefixWord ++ tailWord_5623372).sum := by decide
  have hdescent : baseEnd_5623372 < baseStart_5623372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623396 : List Nat := [2, 3, 1, 1, 2, 5, 2, 2, 1, 4]
def baseStart_5623396 : Nat := 118140960795 + 5623396 * 2 ^ 59
def prefixEnd_5623396 : Nat := 4983230072969 + 3 ^ 40 * 5623396 * 2
def baseEnd_5623396 : Nat := 962501686190261890329493

theorem tailTrace_5623396 : CollatzResearch.WordTrace tailWord_5623396 prefixEnd_5623396 962501686190261890329493 := by
  unfold tailWord_5623396
  simp only [CollatzResearch.WordTrace]
  refine ⟨102551050967702083210297021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136734734623602777613729361 102551050967702083210297021)
  ·
    refine ⟨38456644112888281203861383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102551050967702083210297021 38456644112888281203861383)
    ·
      refine ⟨57684966169332421805792075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38456644112888281203861383 57684966169332421805792075)
      ·
        refine ⟨86527449253998632708688113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57684966169332421805792075 86527449253998632708688113)
        ·
          refine ⟨64895586940498974531516085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86527449253998632708688113 64895586940498974531516085)
          ·
            refine ⟨6083961275671778862329633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64895586940498974531516085 6083961275671778862329633)
            ·
              refine ⟨4562970956753834146747225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6083961275671778862329633 4562970956753834146747225)
              ·
                refine ⟨3422228217565375610060419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4562970956753834146747225 3422228217565375610060419)
                ·
                  refine ⟨5133342326348063415090629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3422228217565375610060419 5133342326348063415090629)
                  ·
                    refine ⟨962501686190261890329493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5133342326348063415090629 962501686190261890329493)
                    ·
                      rfl

theorem cell23_5623396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_5623396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623396 prefixEnd_5623396 := by exact prefixLift 5623396
  have htrace : WordTrace (prefixWord ++ tailWord_5623396) baseStart_5623396 baseEnd_5623396 := by
    simpa [prefixWord, tailWord_5623396, baseEnd_5623396] using wordTrace_append hprefix tailTrace_5623396
  have hstable : (prefixWord ++ tailWord_5623396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623396).length < 2 ^ (prefixWord ++ tailWord_5623396).sum := by decide
  have hdescent : baseEnd_5623396 < baseStart_5623396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623435 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 4, 4]
def baseStart_5623435 : Nat := 118140960795 + 5623435 * 2 ^ 59
def prefixEnd_5623435 : Nat := 4983230072969 + 3 ^ 40 * 5623435 * 2
def baseEnd_5623435 : Nat := 962508361438770339466933

theorem tailTrace_5623435 : CollatzResearch.WordTrace tailWord_5623435 prefixEnd_5623435 962508361438770339466933 := by
  unfold tailWord_5623435
  simp only [CollatzResearch.WordTrace]
  refine ⟨205103524382262876081263759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136735682921508584054175839 205103524382262876081263759)
  ·
    refine ⟨307655286573394314121895639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205103524382262876081263759 307655286573394314121895639)
    ·
      refine ⟨461482929860091471182843459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307655286573394314121895639 461482929860091471182843459)
      ·
        refine ⟨692224394790137206774265189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461482929860091471182843459 692224394790137206774265189)
        ·
          refine ⟨129792074023150726270174723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 692224394790137206774265189 129792074023150726270174723)
          ·
            refine ⟨194688111034726089405262085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129792074023150726270174723 194688111034726089405262085)
            ·
              refine ⟨36504020819011141763486641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194688111034726089405262085 36504020819011141763486641)
              ·
                refine ⟨27378015614258356322614981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36504020819011141763486641 27378015614258356322614981)
                ·
                  refine ⟨5133377927673441810490309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27378015614258356322614981 5133377927673441810490309)
                  ·
                    refine ⟨962508361438770339466933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5133377927673441810490309 962508361438770339466933)
                    ·
                      rfl

theorem cell23_5623435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 4].length) (baseStart_5623435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623435 prefixEnd_5623435 := by exact prefixLift 5623435
  have htrace : WordTrace (prefixWord ++ tailWord_5623435) baseStart_5623435 baseEnd_5623435 := by
    simpa [prefixWord, tailWord_5623435, baseEnd_5623435] using wordTrace_append hprefix tailTrace_5623435
  have hstable : (prefixWord ++ tailWord_5623435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623435).length < 2 ^ (prefixWord ++ tailWord_5623435).sum := by decide
  have hdescent : baseEnd_5623435 < baseStart_5623435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623459 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 3, 2, 2]
def baseStart_5623459 : Nat := 118140960795 + 5623459 * 2 ^ 59
def prefixEnd_5623459 : Nat := 4983230072969 + 3 ^ 40 * 5623459 * 2
def baseEnd_5623459 : Nat := 2887537407852018924500689

theorem tailTrace_5623459 : CollatzResearch.WordTrace tailWord_5623459 prefixEnd_5623459 2887537407852018924500689 := by
  unfold tailWord_5623459
  simp only [CollatzResearch.WordTrace]
  refine ⟨205104399734175928180137431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136736266489450618786758287 205104399734175928180137431)
  ·
    refine ⟨307656599601263892270206147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205104399734175928180137431 307656599601263892270206147)
    ·
      refine ⟨461484899401895838405309221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307656599601263892270206147 461484899401895838405309221)
      ·
        refine ⟨86528418637855469700995479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 461484899401895838405309221 86528418637855469700995479)
        ·
          refine ⟨129792627956783204551493219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86528418637855469700995479 129792627956783204551493219)
          ·
            refine ⟨194688941935174806827239829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129792627956783204551493219 194688941935174806827239829)
            ·
              refine ⟨9126044153211319070026867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 194688941935174806827239829 9126044153211319070026867)
              ·
                refine ⟨13689066229816978605040301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9126044153211319070026867 13689066229816978605040301)
                ·
                  refine ⟨5133399836181366976890113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13689066229816978605040301 5133399836181366976890113)
                  ·
                    refine ⟨3850049877136025232667585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5133399836181366976890113 3850049877136025232667585)
                    ·
                      refine ⟨2887537407852018924500689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3850049877136025232667585 2887537407852018924500689)
                      ·
                        rfl

theorem cell23_5623459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_5623459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623459 prefixEnd_5623459 := by exact prefixLift 5623459
  have htrace : WordTrace (prefixWord ++ tailWord_5623459) baseStart_5623459 baseEnd_5623459 := by
    simpa [prefixWord, tailWord_5623459, baseEnd_5623459] using wordTrace_append hprefix tailTrace_5623459
  have hstable : (prefixWord ++ tailWord_5623459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623459).length < 2 ^ (prefixWord ++ tailWord_5623459).sum := by decide
  have hdescent : baseEnd_5623459 < baseStart_5623459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623479 : List Nat := [1, 1, 3, 1, 5, 2, 2, 2, 1, 2, 3]
def baseStart_5623479 : Nat := 118140960795 + 5623479 * 2 ^ 59
def prefixEnd_5623479 : Nat := 4983230072969 + 3 ^ 40 * 5623479 * 2
def baseEnd_5623479 : Nat := 2887547677465108846250597

theorem tailTrace_5623479 : CollatzResearch.WordTrace tailWord_5623479 prefixEnd_5623479 2887547677465108846250597 := by
  unfold tailWord_5623479
  simp only [CollatzResearch.WordTrace]
  refine ⟨205105129194103471595865491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136736752796068981063910327 205105129194103471595865491)
  ·
    refine ⟨307657693791155207393798237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205105129194103471595865491 307657693791155207393798237)
    ·
      refine ⟨115371635171683202772674339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307657693791155207393798237 115371635171683202772674339)
      ·
        refine ⟨173057452757524804159011509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115371635171683202772674339 173057452757524804159011509)
        ·
          refine ⟨16224136196017950389907329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173057452757524804159011509 16224136196017950389907329)
          ·
            refine ⟨12168102147013462792430497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16224136196017950389907329 12168102147013462792430497)
            ·
              refine ⟨9126076610260097094322873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12168102147013462792430497 9126076610260097094322873)
              ·
                refine ⟨6844557457695072820742155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9126076610260097094322873 6844557457695072820742155)
                ·
                  refine ⟨10266836186542609231113233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6844557457695072820742155 10266836186542609231113233)
                  ·
                    refine ⟨7700127139906956923334925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10266836186542609231113233 7700127139906956923334925)
                    ·
                      refine ⟨2887547677465108846250597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7700127139906956923334925 2887547677465108846250597)
                      ·
                        rfl

theorem cell23_5623479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_5623479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623479 prefixEnd_5623479 := by exact prefixLift 5623479
  have htrace : WordTrace (prefixWord ++ tailWord_5623479) baseStart_5623479 baseEnd_5623479 := by
    simpa [prefixWord, tailWord_5623479, baseEnd_5623479] using wordTrace_append hprefix tailTrace_5623479
  have hstable : (prefixWord ++ tailWord_5623479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623479).length < 2 ^ (prefixWord ++ tailWord_5623479).sum := by decide
  have hdescent : baseEnd_5623479 < baseStart_5623479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623482 : List Nat := [3, 1, 1, 1, 2, 6, 2, 7]
def baseStart_5623482 : Nat := 118140960795 + 5623482 * 2 ^ 59
def prefixEnd_5623482 : Nat := 4983230072969 + 3 ^ 40 * 5623482 * 2
def baseEnd_5623482 : Nat := 106946267329891567944929

theorem tailTrace_5623482 : CollatzResearch.WordTrace tailWord_5623482 prefixEnd_5623482 106946267329891567944929 := by
  unfold tailWord_5623482
  simp only [CollatzResearch.WordTrace]
  refine ⟨51276309653273150777056175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136736825742061735405483133 51276309653273150777056175)
  ·
    refine ⟨76914464479909726165584263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51276309653273150777056175 76914464479909726165584263)
    ·
      refine ⟨115371696719864589248376395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76914464479909726165584263 115371696719864589248376395)
      ·
        refine ⟨173057545079796883872564593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115371696719864589248376395 173057545079796883872564593)
        ·
          refine ⟨129793158809847662904423445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173057545079796883872564593 129793158809847662904423445)
          ·
            refine ⟨6084054319211609198644849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129793158809847662904423445 6084054319211609198644849)
            ·
              refine ⟨4563040739408706898983637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6084054319211609198644849 4563040739408706898983637)
              ·
                refine ⟨106946267329891567944929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4563040739408706898983637 106946267329891567944929)
                ·
                  rfl

theorem cell23_5623482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 7].length) (baseStart_5623482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623482 prefixEnd_5623482 := by exact prefixLift 5623482
  have htrace : WordTrace (prefixWord ++ tailWord_5623482) baseStart_5623482 baseEnd_5623482 := by
    simpa [prefixWord, tailWord_5623482, baseEnd_5623482] using wordTrace_append hprefix tailTrace_5623482
  have hstable : (prefixWord ++ tailWord_5623482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623482).length < 2 ^ (prefixWord ++ tailWord_5623482).sum := by decide
  have hdescent : baseEnd_5623482 < baseStart_5623482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623492 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_5623492 : Nat := 118140960795 + 5623492 * 2 ^ 59
def prefixEnd_5623492 : Nat := 4983230072969 + 3 ^ 40 * 5623492 * 2
def baseEnd_5623492 : Nat := 2887554352713617295388037

theorem tailTrace_5623492 : CollatzResearch.WordTrace tailWord_5623492 prefixEnd_5623492 2887554352713617295388037 := by
  unfold tailWord_5623492
  simp only [CollatzResearch.WordTrace]
  refine ⟨102552801671528187408044365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136737068895370916544059153 102552801671528187408044365)
  ·
    refine ⟨38457300626823070278016637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102552801671528187408044365 38457300626823070278016637)
    ·
      refine ⟨14421487735058651354256239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38457300626823070278016637 14421487735058651354256239)
      ·
        refine ⟨21632231602587977031384359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14421487735058651354256239 21632231602587977031384359)
        ·
          refine ⟨32448347403881965547076539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21632231602587977031384359 32448347403881965547076539)
          ·
            refine ⟨48672521105822948320614809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32448347403881965547076539 48672521105822948320614809)
            ·
              refine ⟨36504390829367211240461107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48672521105822948320614809 36504390829367211240461107)
              ·
                refine ⟨54756586244050816860691661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36504390829367211240461107 54756586244050816860691661)
                ·
                  refine ⟨20533719841519056322759373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54756586244050816860691661 20533719841519056322759373)
                  ·
                    refine ⟨7700144940569646121034765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20533719841519056322759373 7700144940569646121034765)
                    ·
                      refine ⟨2887554352713617295388037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7700144940569646121034765 2887554352713617295388037)
                      ·
                        rfl

theorem cell23_5623492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_5623492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623492 prefixEnd_5623492 := by exact prefixLift 5623492
  have htrace : WordTrace (prefixWord ++ tailWord_5623492) baseStart_5623492 baseEnd_5623492 := by
    simpa [prefixWord, tailWord_5623492, baseEnd_5623492] using wordTrace_append hprefix tailTrace_5623492
  have hstable : (prefixWord ++ tailWord_5623492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623492).length < 2 ^ (prefixWord ++ tailWord_5623492).sum := by decide
  have hdescent : baseEnd_5623492 < baseStart_5623492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623525 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 1, 8]
def baseStart_5623525 : Nat := 118140960795 + 5623525 * 2 ^ 59
def prefixEnd_5623525 : Nat := 4983230072969 + 3 ^ 40 * 5623525 * 2
def baseEnd_5623525 : Nat := 962523765858405222091795

theorem tailTrace_5623525 : CollatzResearch.WordTrace tailWord_5623525 prefixEnd_5623525 962523765858405222091795 := by
  unfold tailWord_5623525
  simp only [CollatzResearch.WordTrace]
  refine ⟨205106806951936821452040029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136737871301291214301360019 205106806951936821452040029)
  ·
    refine ⟨76915052606976308044515011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205106806951936821452040029 76915052606976308044515011)
    ·
      refine ⟨115372578910464462066772517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76915052606976308044515011 115372578910464462066772517)
      ·
        refine ⟨21632358545712086637519847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115372578910464462066772517 21632358545712086637519847)
        ·
          refine ⟨32448537818568129956279771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21632358545712086637519847 32448537818568129956279771)
          ·
            refine ⟨48672806727852194934419657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32448537818568129956279771 48672806727852194934419657)
            ·
              refine ⟨36504605045889146200814743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48672806727852194934419657 36504605045889146200814743)
              ·
                refine ⟨54756907568833719301222115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36504605045889146200814743 54756907568833719301222115)
                ·
                  refine ⟨82135361353250578951833173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54756907568833719301222115 82135361353250578951833173)
                  ·
                    refine ⟨962523765858405222091795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82135361353250578951833173 962523765858405222091795)
                    ·
                      rfl

theorem cell23_5623525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_5623525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623525 prefixEnd_5623525 := by exact prefixLift 5623525
  have htrace : WordTrace (prefixWord ++ tailWord_5623525) baseStart_5623525 baseEnd_5623525 := by
    simpa [prefixWord, tailWord_5623525, baseEnd_5623525] using wordTrace_append hprefix tailTrace_5623525
  have hstable : (prefixWord ++ tailWord_5623525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623525).length < 2 ^ (prefixWord ++ tailWord_5623525).sum := by decide
  have hdescent : baseEnd_5623525 < baseStart_5623525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623535 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 5]
def baseStart_5623535 : Nat := 118140960795 + 5623535 * 2 ^ 59
def prefixEnd_5623535 : Nat := 4983230072969 + 3 ^ 40 * 5623535 * 2
def baseEnd_5623535 : Nat := 2887576432381760627150339

theorem tailTrace_5623535 : CollatzResearch.WordTrace tailWord_5623535 prefixEnd_5623535 2887576432381760627150339 := by
  unfold tailWord_5623535
  simp only [CollatzResearch.WordTrace]
  refine ⟨205107171681900593159904059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136738114454600395439936039 205107171681900593159904059)
  ·
    refine ⟨307660757522850889739856089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205107171681900593159904059 307660757522850889739856089)
    ·
      refine ⟨230745568142138167304892067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307660757522850889739856089 230745568142138167304892067)
      ·
        refine ⟨346118352213207250957338101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230745568142138167304892067 346118352213207250957338101)
        ·
          refine ⟨32448595519988179777250447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 346118352213207250957338101 32448595519988179777250447)
          ·
            refine ⟨48672893279982269665875671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32448595519988179777250447 48672893279982269665875671)
            ·
              refine ⟨73009339919973404498813507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48672893279982269665875671 73009339919973404498813507)
              ·
                refine ⟨109514009879960106748220261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73009339919973404498813507 109514009879960106748220261)
                ·
                  refine ⟨20533876852492520015291299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109514009879960106748220261 20533876852492520015291299)
                  ·
                    refine ⟨30800815278738780022936949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20533876852492520015291299 30800815278738780022936949)
                    ·
                      refine ⟨2887576432381760627150339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30800815278738780022936949 2887576432381760627150339)
                      ·
                        rfl

theorem cell23_5623535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_5623535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623535 prefixEnd_5623535 := by exact prefixLift 5623535
  have htrace : WordTrace (prefixWord ++ tailWord_5623535) baseStart_5623535 baseEnd_5623535 := by
    simpa [prefixWord, tailWord_5623535, baseEnd_5623535] using wordTrace_append hprefix tailTrace_5623535
  have hstable : (prefixWord ++ tailWord_5623535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623535).length < 2 ^ (prefixWord ++ tailWord_5623535).sum := by decide
  have hdescent : baseEnd_5623535 < baseStart_5623535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623545 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 6, 2, 4]
def baseStart_5623545 : Nat := 118140960795 + 5623545 * 2 ^ 59
def prefixEnd_5623545 : Nat := 4983230072969 + 3 ^ 40 * 5623545 * 2
def baseEnd_5623545 : Nat := 2887581567188305588025293

theorem tailTrace_5623545 : CollatzResearch.WordTrace tailWord_5623545 prefixEnd_5623545 2887581567188305588025293 := by
  unfold tailWord_5623545
  simp only [CollatzResearch.WordTrace]
  refine ⟨205107536411864364867768089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136738357607909576578512059 205107536411864364867768089)
  ·
    refine ⟨153830652308898273650826067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205107536411864364867768089 153830652308898273650826067)
    ·
      refine ⟨230745978463347410476239101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153830652308898273650826067 230745978463347410476239101)
      ·
        refine ⟨86529741923755278928589663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230745978463347410476239101 86529741923755278928589663)
        ·
          refine ⟨129794612885632918392884495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86529741923755278928589663 129794612885632918392884495)
          ·
            refine ⟨194691919328449377589326743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129794612885632918392884495 194691919328449377589326743)
            ·
              refine ⟨292037878992674066383990115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194691919328449377589326743 292037878992674066383990115)
              ·
                refine ⟨438056818489011099575985173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292037878992674066383990115 438056818489011099575985173)
                ·
                  refine ⟨20533913366672395292624305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 438056818489011099575985173 20533913366672395292624305)
                  ·
                    refine ⟨15400435025004296469468229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20533913366672395292624305 15400435025004296469468229)
                    ·
                      refine ⟨2887581567188305588025293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15400435025004296469468229 2887581567188305588025293)
                      ·
                        rfl

theorem cell23_5623545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_5623545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623545 prefixEnd_5623545 := by exact prefixLift 5623545
  have htrace : WordTrace (prefixWord ++ tailWord_5623545) baseStart_5623545 baseEnd_5623545 := by
    simpa [prefixWord, tailWord_5623545, baseEnd_5623545] using wordTrace_append hprefix tailTrace_5623545
  have hstable : (prefixWord ++ tailWord_5623545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623545).length < 2 ^ (prefixWord ++ tailWord_5623545).sum := by decide
  have hdescent : baseEnd_5623545 < baseStart_5623545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623549 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 4, 2, 2]
def baseStart_5623549 : Nat := 118140960795 + 5623549 * 2 ^ 59
def prefixEnd_5623549 : Nat := 4983230072969 + 3 ^ 40 * 5623549 * 2
def baseEnd_5623549 : Nat := 2887583621110923572375275

theorem tailTrace_5623549 : CollatzResearch.WordTrace tailWord_5623549 prefixEnd_5623549 2887583621110923572375275 := by
  unfold tailWord_5623549
  simp only [CollatzResearch.WordTrace]
  refine ⟨205107682303849873550913701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136738454869233249033942467 205107682303849873550913701)
  ·
    refine ⟨38457690431971851290796319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205107682303849873550913701 38457690431971851290796319)
    ·
      refine ⟨57686535647957776936194479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38457690431971851290796319 57686535647957776936194479)
      ·
        refine ⟨86529803471936665404291719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57686535647957776936194479 86529803471936665404291719)
        ·
          refine ⟨129794705207904998106437579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86529803471936665404291719 129794705207904998106437579)
          ·
            refine ⟨194692057811857497159656369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129794705207904998106437579 194692057811857497159656369)
            ·
              refine ⟨146019043358893122869742277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194692057811857497159656369 146019043358893122869742277)
              ·
                refine ⟨27378570629792460538076677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146019043358893122869742277 27378570629792460538076677)
                ·
                  refine ⟨5133481993086086350889377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27378570629792460538076677 5133481993086086350889377)
                  ·
                    refine ⟨3850111494814564763167033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5133481993086086350889377 3850111494814564763167033)
                    ·
                      refine ⟨2887583621110923572375275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3850111494814564763167033 2887583621110923572375275)
                      ·
                        rfl

theorem cell23_5623549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_5623549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623549 prefixEnd_5623549 := by exact prefixLift 5623549
  have htrace : WordTrace (prefixWord ++ tailWord_5623549) baseStart_5623549 baseEnd_5623549 := by
    simpa [prefixWord, tailWord_5623549, baseEnd_5623549] using wordTrace_append hprefix tailTrace_5623549
  have hstable : (prefixWord ++ tailWord_5623549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623549).length < 2 ^ (prefixWord ++ tailWord_5623549).sum := by decide
  have hdescent : baseEnd_5623549 < baseStart_5623549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623566 : List Nat := [4, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2]
def baseStart_5623566 : Nat := 118140960795 + 5623566 * 2 ^ 59
def prefixEnd_5623566 : Nat := 4983230072969 + 3 ^ 40 * 5623566 * 2
def baseEnd_5623566 : Nat := 2887592350282050005862697

theorem tailTrace_5623566 : CollatzResearch.WordTrace tailWord_5623566 prefixEnd_5623566 2887592350282050005862697 := by
  unfold tailWord_5623566
  simp only [CollatzResearch.WordTrace]
  refine ⟨25638537793098535681785319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136738868229858856969521701 25638537793098535681785319)
  ·
    refine ⟨38457806689647803522677979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25638537793098535681785319 38457806689647803522677979)
    ·
      refine ⟨57686710034471705284016969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38457806689647803522677979 57686710034471705284016969)
      ·
        refine ⟨43265032525853778963012727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57686710034471705284016969 43265032525853778963012727)
        ·
          refine ⟨64897548788780668444519091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43265032525853778963012727 64897548788780668444519091)
          ·
            refine ⟨97346323183171002666778637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64897548788780668444519091 97346323183171002666778637)
            ·
              refine ⟨36504871193689126000041989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97346323183171002666778637 36504871193689126000041989)
              ·
                refine ⟨6844663348816711125007873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36504871193689126000041989 6844663348816711125007873)
                ·
                  refine ⟨5133497511612533343755905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6844663348816711125007873 5133497511612533343755905)
                  ·
                    refine ⟨3850123133709400007816929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5133497511612533343755905 3850123133709400007816929)
                    ·
                      refine ⟨2887592350282050005862697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3850123133709400007816929 2887592350282050005862697)
                      ·
                        rfl

theorem cell23_5623566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_5623566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623566 prefixEnd_5623566 := by exact prefixLift 5623566
  have htrace : WordTrace (prefixWord ++ tailWord_5623566) baseStart_5623566 baseEnd_5623566 := by
    simpa [prefixWord, tailWord_5623566, baseEnd_5623566] using wordTrace_append hprefix tailTrace_5623566
  have hstable : (prefixWord ++ tailWord_5623566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623566).length < 2 ^ (prefixWord ++ tailWord_5623566).sum := by decide
  have hdescent : baseEnd_5623566 < baseStart_5623566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623602 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 1, 7]
def baseStart_5623602 : Nat := 118140960795 + 5623602 * 2 ^ 59
def prefixEnd_5623602 : Nat := 4983230072969 + 3 ^ 40 * 5623602 * 2
def baseEnd_5623602 : Nat := 962536945195203955004177

theorem tailTrace_5623602 : CollatzResearch.WordTrace tailWord_5623602 prefixEnd_5623602 962536945195203955004177 := by
  unfold tailWord_5623602
  simp only [CollatzResearch.WordTrace]
  refine ⟨51277403843164465900648265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136739743581771909068395373 51277403843164465900648265)
  ·
    refine ⟨38458052882373349425486199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51277403843164465900648265 38458052882373349425486199)
    ·
      refine ⟨57687079323560024138229299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38458052882373349425486199 57687079323560024138229299)
      ·
        refine ⟨86530618985340036207343949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57687079323560024138229299 86530618985340036207343949)
        ·
          refine ⟨32448982119502513577753981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86530618985340036207343949 32448982119502513577753981)
          ·
            refine ⟨12168368294813442591657743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32448982119502513577753981 12168368294813442591657743)
            ·
              refine ⟨18252552442220163887486615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12168368294813442591657743 18252552442220163887486615)
              ·
                refine ⟨27378828663330245831229923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18252552442220163887486615 27378828663330245831229923)
                ·
                  refine ⟨41068242994995368746844885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27378828663330245831229923 41068242994995368746844885)
                  ·
                    refine ⟨962536945195203955004177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41068242994995368746844885 962536945195203955004177)
                    ·
                      rfl

theorem cell23_5623602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_5623602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623602 prefixEnd_5623602 := by exact prefixLift 5623602
  have htrace : WordTrace (prefixWord ++ tailWord_5623602) baseStart_5623602 baseEnd_5623602 := by
    simpa [prefixWord, tailWord_5623602, baseEnd_5623602] using wordTrace_append hprefix tailTrace_5623602
  have hstable : (prefixWord ++ tailWord_5623602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623602).length < 2 ^ (prefixWord ++ tailWord_5623602).sum := by decide
  have hdescent : baseEnd_5623602 < baseStart_5623602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623606 : List Nat := [5, 1, 2, 2, 1, 1, 1, 5, 5]
def baseStart_5623606 : Nat := 118140960795 + 5623606 * 2 ^ 59
def prefixEnd_5623606 : Nat := 4983230072969 + 3 ^ 40 * 5623606 * 2
def baseEnd_5623606 : Nat := 320845876612025538818057

theorem tailTrace_5623606 : CollatzResearch.WordTrace tailWord_5623606 prefixEnd_5623606 320845876612025538818057 := by
  unfold tailWord_5623606
  simp only [CollatzResearch.WordTrace]
  refine ⟨12819360079040210767858667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136739840843095581523825781 12819360079040210767858667)
  ·
    refine ⟨19229040118560316151788001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12819360079040210767858667 19229040118560316151788001)
    ·
      refine ⟨14421780088920237113841001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19229040118560316151788001 14421780088920237113841001)
      ·
        refine ⟨10816335066690177835380751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14421780088920237113841001 10816335066690177835380751)
        ·
          refine ⟨16224502600035266753071127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10816335066690177835380751 16224502600035266753071127)
          ·
            refine ⟨24336753900052900129606691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16224502600035266753071127 24336753900052900129606691)
            ·
              refine ⟨36505130850079350194410037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24336753900052900129606691 36505130850079350194410037)
              ·
                refine ⟨3422356017194939080725941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36505130850079350194410037 3422356017194939080725941)
                ·
                  refine ⟨320845876612025538818057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3422356017194939080725941 320845876612025538818057)
                  ·
                    rfl

theorem cell23_5623606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_5623606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623606 prefixEnd_5623606 := by exact prefixLift 5623606
  have htrace : WordTrace (prefixWord ++ tailWord_5623606) baseStart_5623606 baseEnd_5623606 := by
    simpa [prefixWord, tailWord_5623606, baseEnd_5623606] using wordTrace_append hprefix tailTrace_5623606
  have hstable : (prefixWord ++ tailWord_5623606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623606).length < 2 ^ (prefixWord ++ tailWord_5623606).sum := by decide
  have hdescent : baseEnd_5623606 < baseStart_5623606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623642 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3]
def baseStart_5623642 : Nat := 118140960795 + 5623642 * 2 ^ 59
def prefixEnd_5623642 : Nat := 4983230072969 + 3 ^ 40 * 5623642 * 2
def baseEnd_5623642 : Nat := 2887631374811791708512347

theorem tailTrace_5623642 : CollatzResearch.WordTrace tailWord_5623642 prefixEnd_5623642 2887631374811791708512347 := by
  unfold tailWord_5623642
  simp only [CollatzResearch.WordTrace]
  refine ⟨51277768573128237608512295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136740716195008633622699453 51277768573128237608512295)
  ·
    refine ⟨76916652859692356412768443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51277768573128237608512295 76916652859692356412768443)
    ·
      refine ⟨115374979289538534619152665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76916652859692356412768443 115374979289538534619152665)
      ·
        refine ⟨86531234467153900964364499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115374979289538534619152665 86531234467153900964364499)
        ·
          refine ⟨129796851700730851446546749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86531234467153900964364499 129796851700730851446546749)
          ·
            refine ⟨48673819387774069292455031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129796851700730851446546749 48673819387774069292455031)
            ·
              refine ⟨73010729081661103938682547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48673819387774069292455031 73010729081661103938682547)
              ·
                refine ⟨109516093622491655908023821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73010729081661103938682547 109516093622491655908023821)
                ·
                  refine ⟨41068535108434370965508933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109516093622491655908023821 41068535108434370965508933)
                  ·
                    refine ⟨7700350332831444556032925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41068535108434370965508933 7700350332831444556032925)
                    ·
                      refine ⟨2887631374811791708512347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7700350332831444556032925 2887631374811791708512347)
                      ·
                        rfl

theorem cell23_5623642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_5623642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623642 prefixEnd_5623642 := by exact prefixLift 5623642
  have htrace : WordTrace (prefixWord ++ tailWord_5623642) baseStart_5623642 baseEnd_5623642 := by
    simpa [prefixWord, tailWord_5623642, baseEnd_5623642] using wordTrace_append hprefix tailTrace_5623642
  have hstable : (prefixWord ++ tailWord_5623642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623642).length < 2 ^ (prefixWord ++ tailWord_5623642).sum := by decide
  have hdescent : baseEnd_5623642 < baseStart_5623642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623683 : List Nat := [1, 1, 1, 3, 4, 3, 3, 2, 1, 4]
def baseStart_5623683 : Nat := 118140960795 + 5623683 * 2 ^ 59
def prefixEnd_5623683 : Nat := 4983230072969 + 3 ^ 40 * 5623683 * 2
def baseEnd_5623683 : Nat := 962550809172875349366553

theorem tailTrace_5623683 : CollatzResearch.WordTrace tailWord_5623683 prefixEnd_5623683 962550809172875349366553 := by
  unfold tailWord_5623683
  simp only [CollatzResearch.WordTrace]
  refine ⟨205112569685364414436291703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136741713123576276290861135 205112569685364414436291703)
  ·
    refine ⟨307668854528046621654437555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205112569685364414436291703 307668854528046621654437555)
    ·
      refine ⟨461503281792069932481656333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307668854528046621654437555 461503281792069932481656333)
      ·
        refine ⟨173063730672026224680621125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 461503281792069932481656333 173063730672026224680621125)
        ·
          refine ⟨32449449501004917127616461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173063730672026224680621125 32449449501004917127616461)
          ·
            refine ⟨12168543562876843922856173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32449449501004917127616461 12168543562876843922856173)
            ·
              refine ⟨4563203836078816471071065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12168543562876843922856173 4563203836078816471071065)
              ·
                refine ⟨3422402877059112353303299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4563203836078816471071065 3422402877059112353303299)
                ·
                  refine ⟨5133604315588668529954949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3422402877059112353303299 5133604315588668529954949)
                  ·
                    refine ⟨962550809172875349366553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5133604315588668529954949 962550809172875349366553)
                    ·
                      rfl

theorem cell23_5623683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 1, 4].length) (baseStart_5623683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623683 prefixEnd_5623683 := by exact prefixLift 5623683
  have htrace : WordTrace (prefixWord ++ tailWord_5623683) baseStart_5623683 baseEnd_5623683 := by
    simpa [prefixWord, tailWord_5623683, baseEnd_5623683] using wordTrace_append hprefix tailTrace_5623683
  have hstable : (prefixWord ++ tailWord_5623683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623683).length < 2 ^ (prefixWord ++ tailWord_5623683).sum := by decide
  have hdescent : baseEnd_5623683 < baseStart_5623683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623692 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 3, 5]
def baseStart_5623692 : Nat := 118140960795 + 5623692 * 2 ^ 59
def prefixEnd_5623692 : Nat := 4983230072969 + 3 ^ 40 * 5623692 * 2
def baseEnd_5623692 : Nat := 962552349614838837629039

theorem tailTrace_5623692 : CollatzResearch.WordTrace tailWord_5623692 prefixEnd_5623692 962552349614838837629039 := by
  unfold tailWord_5623692
  simp only [CollatzResearch.WordTrace]
  refine ⟨102556448971165904486684665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136741931961554539315579553 102556448971165904486684665)
  ·
    refine ⟨76917336728374428365013499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102556448971165904486684665 76917336728374428365013499)
    ·
      refine ⟨115376005092561642547520249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76917336728374428365013499 115376005092561642547520249)
      ·
        refine ⟨86532003819421231910640187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115376005092561642547520249 86532003819421231910640187)
        ·
          refine ⟨129798005729131847865960281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86532003819421231910640187 129798005729131847865960281)
          ·
            refine ⟨97348504296848885899470211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129798005729131847865960281 97348504296848885899470211)
            ·
              refine ⟨146022756445273328849205317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97348504296848885899470211 146022756445273328849205317)
              ·
                refine ⟨27379266833488749159225997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146022756445273328849205317 27379266833488749159225997)
                ·
                  refine ⟨10267225062558280934709749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27379266833488749159225997 10267225062558280934709749)
                  ·
                    refine ⟨962552349614838837629039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10267225062558280934709749 962552349614838837629039)
                    ·
                      rfl

theorem cell23_5623692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_5623692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623692 prefixEnd_5623692 := by exact prefixLift 5623692
  have htrace : WordTrace (prefixWord ++ tailWord_5623692) baseStart_5623692 baseEnd_5623692 := by
    simpa [prefixWord, tailWord_5623692, baseEnd_5623692] using wordTrace_append hprefix tailTrace_5623692
  have hstable : (prefixWord ++ tailWord_5623692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623692).length < 2 ^ (prefixWord ++ tailWord_5623692).sum := by decide
  have hdescent : baseEnd_5623692 < baseStart_5623692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623709 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 3, 5]
def baseStart_5623709 : Nat := 118140960795 + 5623709 * 2 ^ 59
def prefixEnd_5623709 : Nat := 4983230072969 + 3 ^ 40 * 5623709 * 2
def baseEnd_5623709 : Nat := 962555259338547648791513

theorem tailTrace_5623709 : CollatzResearch.WordTrace tailWord_5623709 prefixEnd_5623709 962555259338547648791513 := by
  unfold tailWord_5623709
  simp only [CollatzResearch.WordTrace]
  refine ⟨205113517983270220876738181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136742345322180147251158787 205113517983270220876738181)
  ·
    refine ⟨38458784621863166414388409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205113517983270220876738181 38458784621863166414388409)
    ·
      refine ⟨28844088466397374810791307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38458784621863166414388409 28844088466397374810791307)
      ·
        refine ⟨43266132699596062216186961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28844088466397374810791307 43266132699596062216186961)
        ·
          refine ⟨32449599524697046662140221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43266132699596062216186961 32449599524697046662140221)
          ·
            refine ⟨12168599821761392498302583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32449599524697046662140221 12168599821761392498302583)
            ·
              refine ⟨18252899732642088747453875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12168599821761392498302583 18252899732642088747453875)
              ·
                refine ⟨27379349598963133121180813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18252899732642088747453875 27379349598963133121180813)
                ·
                  refine ⟨10267256099611174920442805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27379349598963133121180813 10267256099611174920442805)
                  ·
                    refine ⟨962555259338547648791513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10267256099611174920442805 962555259338547648791513)
                    ·
                      rfl

theorem cell23_5623709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_5623709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623709 prefixEnd_5623709 := by exact prefixLift 5623709
  have htrace : WordTrace (prefixWord ++ tailWord_5623709) baseStart_5623709 baseEnd_5623709 := by
    simpa [prefixWord, tailWord_5623709, baseEnd_5623709] using wordTrace_append hprefix tailTrace_5623709
  have hstable : (prefixWord ++ tailWord_5623709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623709).length < 2 ^ (prefixWord ++ tailWord_5623709).sum := by decide
  have hdescent : baseEnd_5623709 < baseStart_5623709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
