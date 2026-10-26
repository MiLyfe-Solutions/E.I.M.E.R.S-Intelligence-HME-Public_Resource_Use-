import V185TrunkScan23Chunk0465

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2756615 : List Nat := [1, 1, 4, 3, 1, 2, 4, 2, 1, 2, 2]
def baseStart_2756615 : Nat := 118140960795 + 2756615 * 2 ^ 59
def prefixEnd_2756615 : Nat := 4983230072969 + 3 ^ 40 * 2756615 * 2
def baseEnd_2756615 : Nat := 1415468474393837464835065

theorem tailTrace_2756615 : CollatzResearch.WordTrace tailWord_2756615 prefixEnd_2756615 1415468474393837464835065 := by
  unfold tailWord_2756615
  simp only [CollatzResearch.WordTrace]
  refine ⟨100542008908262122205415299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67028005938841414803610199 100542008908262122205415299)
  ·
    refine ⟨150813013362393183308122949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100542008908262122205415299 150813013362393183308122949)
    ·
      refine ⟨28277440005448721870273053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150813013362393183308122949 28277440005448721870273053)
      ·
        refine ⟨10604040002043270701352395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28277440005448721870273053 10604040002043270701352395)
        ·
          refine ⟨15906060003064906052028593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10604040002043270701352395 15906060003064906052028593)
          ·
            refine ⟨11929545002298679539021445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15906060003064906052028593 11929545002298679539021445)
            ·
              refine ⟨2236789687931002413566521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11929545002298679539021445 2236789687931002413566521)
              ·
                refine ⟨1677592265948251810174891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2236789687931002413566521 1677592265948251810174891)
                ·
                  refine ⟨2516388398922377715262337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677592265948251810174891 2516388398922377715262337)
                  ·
                    refine ⟨1887291299191783286446753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2516388398922377715262337 1887291299191783286446753)
                    ·
                      refine ⟨1415468474393837464835065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1887291299191783286446753 1415468474393837464835065)
                      ·
                        rfl

theorem cell23_2756615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_2756615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756615 prefixEnd_2756615 := by exact prefixLift 2756615
  have htrace : WordTrace (prefixWord ++ tailWord_2756615) baseStart_2756615 baseEnd_2756615 := by
    simpa [prefixWord, tailWord_2756615, baseEnd_2756615] using wordTrace_append hprefix tailTrace_2756615
  have hstable : (prefixWord ++ tailWord_2756615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756615).length < 2 ^ (prefixWord ++ tailWord_2756615).sum := by decide
  have hdescent : baseEnd_2756615 < baseStart_2756615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756628 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_2756628 : Nat := 118140960795 + 2756628 * 2 ^ 59
def prefixEnd_2756628 : Nat := 4983230072969 + 3 ^ 40 * 2756628 * 2
def baseEnd_2756628 : Nat := 1415475149642345913972505

theorem tailTrace_2756628 : CollatzResearch.WordTrace tailWord_2756628 prefixEnd_2756628 1415475149642345913972505 := by
  unfold tailWord_2756628
  simp only [CollatzResearch.WordTrace]
  refine ⟨50271241528607512712819269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67028322038143350283759025 50271241528607512712819269)
  ·
    refine ⟨9425857786613908633653613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50271241528607512712819269 9425857786613908633653613)
    ·
      refine ⟨3534696669980215737620105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9425857786613908633653613 3534696669980215737620105)
      ·
        refine ⟨2651022502485161803215079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3534696669980215737620105 2651022502485161803215079)
        ·
          refine ⟨3976533753727742704822619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2651022502485161803215079 3976533753727742704822619)
          ·
            refine ⟨5964800630591614057233929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3976533753727742704822619 5964800630591614057233929)
            ·
              refine ⟨4473600472943710542925447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5964800630591614057233929 4473600472943710542925447)
              ·
                refine ⟨6710400709415565814388171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4473600472943710542925447 6710400709415565814388171)
                ·
                  refine ⟨10065601064123348721582257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6710400709415565814388171 10065601064123348721582257)
                  ·
                    refine ⟨7549200798092511541186693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10065601064123348721582257 7549200798092511541186693)
                    ·
                      refine ⟨1415475149642345913972505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7549200798092511541186693 1415475149642345913972505)
                      ·
                        rfl

theorem cell23_2756628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_2756628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756628 prefixEnd_2756628 := by exact prefixLift 2756628
  have htrace : WordTrace (prefixWord ++ tailWord_2756628) baseStart_2756628 baseEnd_2756628 := by
    simpa [prefixWord, tailWord_2756628, baseEnd_2756628] using wordTrace_append hprefix tailTrace_2756628
  have hstable : (prefixWord ++ tailWord_2756628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756628).length < 2 ^ (prefixWord ++ tailWord_2756628).sum := by decide
  have hdescent : baseEnd_2756628 < baseStart_2756628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756631 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 3]
def baseStart_2756631 : Nat := 118140960795 + 2756631 * 2 ^ 59
def prefixEnd_2756631 : Nat := 4983230072969 + 3 ^ 40 * 2756631 * 2
def baseEnd_2756631 : Nat := 1415476690084309402234991

theorem tailTrace_2756631 : CollatzResearch.WordTrace tailWord_2756631 prefixEnd_2756631 1415476690084309402234991 := by
  unfold tailWord_2756631
  simp only [CollatzResearch.WordTrace]
  refine ⟨100542592476204156937997747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67028394984136104625331831 100542592476204156937997747)
  ·
    refine ⟨150813888714306235406996621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100542592476204156937997747 150813888714306235406996621)
    ·
      refine ⟨56555208267864838277623733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150813888714306235406996621 56555208267864838277623733)
      ·
        refine ⟨5302050775112328588527225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56555208267864838277623733 5302050775112328588527225)
        ·
          refine ⟨3976538081334246441395419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5302050775112328588527225 3976538081334246441395419)
          ·
            refine ⟨5964807122001369662093129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3976538081334246441395419 5964807122001369662093129)
            ·
              refine ⟨4473605341501027246569847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5964807122001369662093129 4473605341501027246569847)
              ·
                refine ⟨6710408012251540869854771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4473605341501027246569847 6710408012251540869854771)
                ·
                  refine ⟨10065612018377311304782157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6710408012251540869854771 10065612018377311304782157)
                  ·
                    refine ⟨3774604506891491739293309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10065612018377311304782157 3774604506891491739293309)
                    ·
                      refine ⟨1415476690084309402234991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3774604506891491739293309 1415476690084309402234991)
                      ·
                        rfl

theorem cell23_2756631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_2756631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756631 prefixEnd_2756631 := by exact prefixLift 2756631
  have htrace : WordTrace (prefixWord ++ tailWord_2756631) baseStart_2756631 baseEnd_2756631 := by
    simpa [prefixWord, tailWord_2756631, baseEnd_2756631] using wordTrace_append hprefix tailTrace_2756631
  have hstable : (prefixWord ++ tailWord_2756631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756631).length < 2 ^ (prefixWord ++ tailWord_2756631).sum := by decide
  have hdescent : baseEnd_2756631 < baseStart_2756631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756658 : List Nat := [3, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2]
def baseStart_2756658 : Nat := 118140960795 + 2756658 * 2 ^ 59
def prefixEnd_2756658 : Nat := 4983230072969 + 3 ^ 40 * 2756658 * 2
def baseEnd_2756658 : Nat := 1415490554061980796597367

theorem tailTrace_2756658 : CollatzResearch.WordTrace tailWord_2756658 prefixEnd_2756658 1415490554061980796597367 := by
  unfold tailWord_2756658
  simp only [CollatzResearch.WordTrace]
  refine ⟨25135894311776585137307657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67029051498070893699487085 25135894311776585137307657)
  ·
    refine ⟨18851920733832438852980743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25135894311776585137307657 18851920733832438852980743)
    ·
      refine ⟨28277881100748658279471115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18851920733832438852980743 28277881100748658279471115)
      ·
        refine ⟨42416821651122987419206673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28277881100748658279471115 42416821651122987419206673)
        ·
          refine ⟨31812616238342240564405005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42416821651122987419206673 31812616238342240564405005)
          ·
            refine ⟨11929731089378340211651877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31812616238342240564405005 11929731089378340211651877)
            ·
              refine ⟨2236824579258438789684727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11929731089378340211651877 2236824579258438789684727)
              ·
                refine ⟨3355236868887658184527091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236824579258438789684727 3355236868887658184527091)
                ·
                  refine ⟨5032855303331487276790637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355236868887658184527091 5032855303331487276790637)
                  ·
                    refine ⟨1887320738749307728796489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5032855303331487276790637 1887320738749307728796489)
                    ·
                      refine ⟨1415490554061980796597367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1887320738749307728796489 1415490554061980796597367)
                      ·
                        rfl

theorem cell23_2756658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_2756658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756658 prefixEnd_2756658 := by exact prefixLift 2756658
  have htrace : WordTrace (prefixWord ++ tailWord_2756658) baseStart_2756658 baseEnd_2756658 := by
    simpa [prefixWord, tailWord_2756658, baseEnd_2756658] using wordTrace_append hprefix tailTrace_2756658
  have hstable : (prefixWord ++ tailWord_2756658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756658).length < 2 ^ (prefixWord ++ tailWord_2756658).sum := by decide
  have hdescent : baseEnd_2756658 < baseStart_2756658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756665 : List Nat := [1, 2, 1, 5, 4, 1, 1, 2, 2, 1, 3]
def baseStart_2756665 : Nat := 118140960795 + 2756665 * 2 ^ 59
def prefixEnd_2756665 : Nat := 4983230072969 + 3 ^ 40 * 2756665 * 2
def baseEnd_2756665 : Nat := 1415494148426562269209835

theorem tailTrace_2756665 : CollatzResearch.WordTrace tailWord_2756665 prefixEnd_2756665 1415494148426562269209835 := by
  unfold tailWord_2756665
  simp only [CollatzResearch.WordTrace]
  refine ⟨100543832558080980744735449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67029221705387320496490299 100543832558080980744735449)
  ·
    refine ⟨75407874418560735558551587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100543832558080980744735449 75407874418560735558551587)
    ·
      refine ⟨113111811627841103337827381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75407874418560735558551587 113111811627841103337827381)
      ·
        refine ⟨10604232340110103437921317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113111811627841103337827381 10604232340110103437921317)
        ·
          refine ⟨1988293563770644394610247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10604232340110103437921317 1988293563770644394610247)
          ·
            refine ⟨2982440345655966591915371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988293563770644394610247 2982440345655966591915371)
            ·
              refine ⟨4473660518483949887873057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2982440345655966591915371 4473660518483949887873057)
              ·
                refine ⟨3355245388862962415904793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4473660518483949887873057 3355245388862962415904793)
                ·
                  refine ⟨2516434041647221811928595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3355245388862962415904793 2516434041647221811928595)
                  ·
                    refine ⟨3774651062470832717892893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2516434041647221811928595 3774651062470832717892893)
                    ·
                      refine ⟨1415494148426562269209835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3774651062470832717892893 1415494148426562269209835)
                      ·
                        rfl

theorem cell23_2756665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_2756665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756665 prefixEnd_2756665 := by exact prefixLift 2756665
  have htrace : WordTrace (prefixWord ++ tailWord_2756665) baseStart_2756665 baseEnd_2756665 := by
    simpa [prefixWord, tailWord_2756665, baseEnd_2756665] using wordTrace_append hprefix tailTrace_2756665
  have hstable : (prefixWord ++ tailWord_2756665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756665).length < 2 ^ (prefixWord ++ tailWord_2756665).sum := by decide
  have hdescent : baseEnd_2756665 < baseStart_2756665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756707 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 1, 7]
def baseStart_2756707 : Nat := 118140960795 + 2756707 * 2 ^ 59
def prefixEnd_2756707 : Nat := 4983230072969 + 3 ^ 40 * 2756707 * 2
def baseEnd_2756707 : Nat := 471838571538017034961547

theorem tailTrace_2756707 : CollatzResearch.WordTrace tailWord_2756707 prefixEnd_2756707 471838571538017034961547 := by
  unfold tailWord_2756707
  simp only [CollatzResearch.WordTrace]
  refine ⟨100545364423928821917764375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67030242949285881278509583 100545364423928821917764375)
  ·
    refine ⟨150818046635893232876646563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100545364423928821917764375 150818046635893232876646563)
    ·
      refine ⟨226227069953839849314969845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150818046635893232876646563 226227069953839849314969845)
      ·
        refine ⟨21208787808172485873278423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226227069953839849314969845 21208787808172485873278423)
        ·
          refine ⟨31813181712258728809917635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21208787808172485873278423 31813181712258728809917635)
          ·
            refine ⟨47719772568388093214876453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31813181712258728809917635 47719772568388093214876453)
            ·
              refine ⟨8947457356572767477789335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47719772568388093214876453 8947457356572767477789335)
              ·
                refine ⟨13421186034859151216684003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8947457356572767477789335 13421186034859151216684003)
                ·
                  refine ⟨20131779052288726825026005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13421186034859151216684003 20131779052288726825026005)
                  ·
                    refine ⟨471838571538017034961547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20131779052288726825026005 471838571538017034961547)
                    ·
                      rfl

theorem cell23_2756707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 7].length) (baseStart_2756707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756707 prefixEnd_2756707 := by exact prefixLift 2756707
  have htrace : WordTrace (prefixWord ++ tailWord_2756707) baseStart_2756707 baseEnd_2756707 := by
    simpa [prefixWord, tailWord_2756707, baseEnd_2756707] using wordTrace_append hprefix tailTrace_2756707
  have hstable : (prefixWord ++ tailWord_2756707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756707).length < 2 ^ (prefixWord ++ tailWord_2756707).sum := by decide
  have hdescent : baseEnd_2756707 < baseStart_2756707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756787 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 6]
def baseStart_2756787 : Nat := 118140960795 + 2756787 * 2 ^ 59
def prefixEnd_2756787 : Nat := 4983230072969 + 3 ^ 40 * 2756787 * 2
def baseEnd_2756787 : Nat := 1415556793066410791884273

theorem tailTrace_2756787 : CollatzResearch.WordTrace tailWord_2756787 prefixEnd_2756787 1415556793066410791884273 := by
  unfold tailWord_2756787
  simp only [CollatzResearch.WordTrace]
  refine ⟨100548282263638995580676615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67032188175759330387117743 100548282263638995580676615)
  ·
    refine ⟨150822423395458493371014923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100548282263638995580676615 150822423395458493371014923)
    ·
      refine ⟨226233635093187740056522385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150822423395458493371014923 226233635093187740056522385)
      ·
        refine ⟨169675226319890805042391789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226233635093187740056522385 169675226319890805042391789)
        ·
          refine ⟨63628209869959051890896921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169675226319890805042391789 63628209869959051890896921)
          ·
            refine ⟨47721157402469288918172691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63628209869959051890896921 47721157402469288918172691)
            ·
              refine ⟨71581736103703933377259037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47721157402469288918172691 71581736103703933377259037)
              ·
                refine ⟨26843151038888975016472139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71581736103703933377259037 26843151038888975016472139)
                ·
                  refine ⟨40264726558333462524708209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26843151038888975016472139 40264726558333462524708209)
                  ·
                    refine ⟨30198544918750096893531157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40264726558333462524708209 30198544918750096893531157)
                    ·
                      refine ⟨1415556793066410791884273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30198544918750096893531157 1415556793066410791884273)
                      ·
                        rfl

theorem cell23_2756787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_2756787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756787 prefixEnd_2756787 := by exact prefixLift 2756787
  have htrace : WordTrace (prefixWord ++ tailWord_2756787) baseStart_2756787 baseEnd_2756787 := by
    simpa [prefixWord, tailWord_2756787, baseEnd_2756787] using wordTrace_append hprefix tailTrace_2756787
  have hstable : (prefixWord ++ tailWord_2756787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756787).length < 2 ^ (prefixWord ++ tailWord_2756787).sum := by decide
  have hdescent : baseEnd_2756787 < baseStart_2756787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756811 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 3, 1, 3]
def baseStart_2756811 : Nat := 118140960795 + 2756811 * 2 ^ 59
def prefixEnd_2756811 : Nat := 4983230072969 + 3 ^ 40 * 2756811 * 2
def baseEnd_2756811 : Nat := 1415569116602118697984163

theorem tailTrace_2756811 : CollatzResearch.WordTrace tailWord_2756811 prefixEnd_2756811 1415569116602118697984163 := by
  unfold tailWord_2756811
  simp only [CollatzResearch.WordTrace]
  refine ⟨100549157615552047679550287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67032771743701365119700191 100549157615552047679550287)
  ·
    refine ⟨150823736423328071519325431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100549157615552047679550287 150823736423328071519325431)
    ·
      refine ⟨226235604634992107278988147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150823736423328071519325431 226235604634992107278988147)
      ·
        refine ⟨339353406952488160918482221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226235604634992107278988147 339353406952488160918482221)
        ·
          refine ⟨127257527607183060344430833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339353406952488160918482221 127257527607183060344430833)
          ·
            refine ⟨95443145705387295258323125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127257527607183060344430833 95443145705387295258323125)
            ·
              refine ⟨8947794909880058930467793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95443145705387295258323125 8947794909880058930467793)
              ·
                refine ⟨6710846182410044197850845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8947794909880058930467793 6710846182410044197850845)
                ·
                  refine ⟨2516567318403766574194067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6710846182410044197850845 2516567318403766574194067)
                  ·
                    refine ⟨3774850977605649861291101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2516567318403766574194067 3774850977605649861291101)
                    ·
                      refine ⟨1415569116602118697984163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3774850977605649861291101 1415569116602118697984163)
                      ·
                        rfl

theorem cell23_2756811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 1, 3].length) (baseStart_2756811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756811 prefixEnd_2756811 := by exact prefixLift 2756811
  have htrace : WordTrace (prefixWord ++ tailWord_2756811) baseStart_2756811 baseEnd_2756811 := by
    simpa [prefixWord, tailWord_2756811, baseEnd_2756811] using wordTrace_append hprefix tailTrace_2756811
  have hstable : (prefixWord ++ tailWord_2756811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756811).length < 2 ^ (prefixWord ++ tailWord_2756811).sum := by decide
  have hdescent : baseEnd_2756811 < baseStart_2756811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756822 : List Nat := [5, 2, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_2756822 : Nat := 118140960795 + 2756822 * 2 ^ 59
def prefixEnd_2756822 : Nat := 4983230072969 + 3 ^ 40 * 2756822 * 2
def baseEnd_2756822 : Nat := 471858254963106051648871

theorem tailTrace_2756822 : CollatzResearch.WordTrace tailWord_2756822 prefixEnd_2756822 471858254963106051648871 := by
  unfold tailWord_2756822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6284347426157012284887545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67033039212341464372133813 6284347426157012284887545)
  ·
    refine ⟨4713260569617759213665659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6284347426157012284887545 4713260569617759213665659)
    ·
      refine ⟨7069890854426638820498489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4713260569617759213665659 7069890854426638820498489)
      ·
        refine ⟨5302418140819979115373867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7069890854426638820498489 5302418140819979115373867)
        ·
          refine ⟨7953627211229968673060801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5302418140819979115373867 7953627211229968673060801)
          ·
            refine ⟨5965220408422476504795601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7953627211229968673060801 5965220408422476504795601)
            ·
              refine ⟨4473915306316857378596701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5965220408422476504795601 4473915306316857378596701)
              ·
                refine ⟨1677718239868821516973763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4473915306316857378596701 1677718239868821516973763)
                ·
                  refine ⟨2516577359803232275460645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677718239868821516973763 2516577359803232275460645)
                  ·
                    refine ⟨471858254963106051648871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2516577359803232275460645 471858254963106051648871)
                    ·
                      rfl

theorem cell23_2756822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_2756822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756822 prefixEnd_2756822 := by exact prefixLift 2756822
  have htrace : WordTrace (prefixWord ++ tailWord_2756822) baseStart_2756822 baseEnd_2756822 := by
    simpa [prefixWord, tailWord_2756822, baseEnd_2756822] using wordTrace_append hprefix tailTrace_2756822
  have hstable : (prefixWord ++ tailWord_2756822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756822).length < 2 ^ (prefixWord ++ tailWord_2756822).sum := by decide
  have hdescent : baseEnd_2756822 < baseStart_2756822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756835 : List Nat := [1, 1, 1, 8, 2, 1, 1, 2, 6]
def baseStart_2756835 : Nat := 118140960795 + 2756835 * 2 ^ 59
def prefixEnd_2756835 : Nat := 4983230072969 + 3 ^ 40 * 2756835 * 2
def baseEnd_2756835 : Nat := 157286826681980733787117

theorem tailTrace_2756835 : CollatzResearch.WordTrace tailWord_2756835 prefixEnd_2756835 157286826681980733787117 := by
  unfold tailWord_2756835
  simp only [CollatzResearch.WordTrace]
  refine ⟨100550032967465099778423959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67033355311643399852282639 100550032967465099778423959)
  ·
    refine ⟨150825049451197649667635939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100550032967465099778423959 150825049451197649667635939)
    ·
      refine ⟨226237574176796474501453909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150825049451197649667635939 226237574176796474501453909)
      ·
        refine ⟨2651221572384333685563913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 226237574176796474501453909 2651221572384333685563913)
        ·
          refine ⟨1988416179288250264172935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2651221572384333685563913 1988416179288250264172935)
          ·
            refine ⟨2982624268932375396259403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988416179288250264172935 2982624268932375396259403)
            ·
              refine ⟨4473936403398563094389105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2982624268932375396259403 4473936403398563094389105)
              ·
                refine ⟨3355452302548922320791829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4473936403398563094389105 3355452302548922320791829)
                ·
                  refine ⟨157286826681980733787117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3355452302548922320791829 157286826681980733787117)
                  ·
                    rfl

theorem cell23_2756835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 6].length) (baseStart_2756835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756835 prefixEnd_2756835 := by exact prefixLift 2756835
  have htrace : WordTrace (prefixWord ++ tailWord_2756835) baseStart_2756835 baseEnd_2756835 := by
    simpa [prefixWord, tailWord_2756835, baseEnd_2756835] using wordTrace_append hprefix tailTrace_2756835
  have hstable : (prefixWord ++ tailWord_2756835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756835).length < 2 ^ (prefixWord ++ tailWord_2756835).sum := by decide
  have hdescent : baseEnd_2756835 < baseStart_2756835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756845 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_2756845 : Nat := 118140960795 + 2756845 * 2 ^ 59
def prefixEnd_2756845 : Nat := 4983230072969 + 3 ^ 40 * 2756845 * 2
def baseEnd_2756845 : Nat := 1415586574944371564959007

theorem tailTrace_2756845 : CollatzResearch.WordTrace tailWord_2756845 prefixEnd_2756845 1415586574944371564959007 := by
  unfold tailWord_2756845
  simp only [CollatzResearch.WordTrace]
  refine ⟨100550397697428871486287989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67033598464952580990858659 100550397697428871486287989)
  ·
    refine ⟨9426599784133956701839499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100550397697428871486287989 9426599784133956701839499)
    ·
      refine ⟨14139899676200935052759249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9426599784133956701839499 14139899676200935052759249)
      ·
        refine ⟨10604924757150701289569437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14139899676200935052759249 10604924757150701289569437)
        ·
          refine ⟨3976846783931512983588539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10604924757150701289569437 3976846783931512983588539)
          ·
            refine ⟨5965270175897269475382809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3976846783931512983588539 5965270175897269475382809)
            ·
              refine ⟨4473952631922952106537107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5965270175897269475382809 4473952631922952106537107)
              ·
                refine ⟨6710928947884428159805661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4473952631922952106537107 6710928947884428159805661)
                ·
                  refine ⟨2516598355456660559927123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6710928947884428159805661 2516598355456660559927123)
                  ·
                    refine ⟨3774897533184990839890685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2516598355456660559927123 3774897533184990839890685)
                    ·
                      refine ⟨1415586574944371564959007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3774897533184990839890685 1415586574944371564959007)
                      ·
                        rfl

theorem cell23_2756845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_2756845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756845 prefixEnd_2756845 := by exact prefixLift 2756845
  have htrace : WordTrace (prefixWord ++ tailWord_2756845) baseStart_2756845 baseEnd_2756845 := by
    simpa [prefixWord, tailWord_2756845, baseEnd_2756845] using wordTrace_append hprefix tailTrace_2756845
  have hstable : (prefixWord ++ tailWord_2756845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756845).length < 2 ^ (prefixWord ++ tailWord_2756845).sum := by decide
  have hdescent : baseEnd_2756845 < baseStart_2756845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756861 : List Nat := [1, 4, 1, 1, 1, 1, 1, 7, 2, 4]
def baseStart_2756861 : Nat := 118140960795 + 2756861 * 2 ^ 59
def prefixEnd_2756861 : Nat := 4983230072969 + 3 ^ 40 * 2756861 * 2
def baseEnd_2756861 : Nat := 471864930211614500786311

theorem tailTrace_2756861 : CollatzResearch.WordTrace tailWord_2756861 prefixEnd_2756861 471864930211614500786311 := by
  unfold tailWord_2756861
  simp only [CollatzResearch.WordTrace]
  refine ⟨100550981265370906218870437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67033987510247270812580291 100550981265370906218870437)
  ·
    refine ⟨18853308987257044916038207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100550981265370906218870437 18853308987257044916038207)
    ·
      refine ⟨28279963480885567374057311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18853308987257044916038207 28279963480885567374057311)
      ·
        refine ⟨42419945221328351061085967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28279963480885567374057311 42419945221328351061085967)
        ·
          refine ⟨63629917831992526591628951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42419945221328351061085967 63629917831992526591628951)
          ·
            refine ⟨95444876747988789887443427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63629917831992526591628951 95444876747988789887443427)
            ·
              refine ⟨143167315121983184831165141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95444876747988789887443427 143167315121983184831165141)
              ·
                refine ⟨3355483948171480894480433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 143167315121983184831165141 3355483948171480894480433)
                ·
                  refine ⟨2516612961128610670860325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3355483948171480894480433 2516612961128610670860325)
                  ·
                    refine ⟨471864930211614500786311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2516612961128610670860325 471864930211614500786311)
                    ·
                      rfl

theorem cell23_2756861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_2756861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756861 prefixEnd_2756861 := by exact prefixLift 2756861
  have htrace : WordTrace (prefixWord ++ tailWord_2756861) baseStart_2756861 baseEnd_2756861 := by
    simpa [prefixWord, tailWord_2756861, baseEnd_2756861] using wordTrace_append hprefix tailTrace_2756861
  have hstable : (prefixWord ++ tailWord_2756861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756861).length < 2 ^ (prefixWord ++ tailWord_2756861).sum := by decide
  have hdescent : baseEnd_2756861 < baseStart_2756861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756928 : List Nat := [2, 1, 1, 2, 2, 1, 2, 6, 1, 3, 2]
def baseStart_2756928 : Nat := 118140960795 + 2756928 * 2 ^ 59
def prefixEnd_2756928 : Nat := 4983230072969 + 3 ^ 40 * 2756928 * 2
def baseEnd_2756928 : Nat := 1415629193838694740221125

theorem tailTrace_2756928 : CollatzResearch.WordTrace tailWord_2756928 prefixEnd_2756928 1415629193838694740221125 := by
  unfold tailWord_2756928
  simp only [CollatzResearch.WordTrace]
  refine ⟨50276712478064088330779719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67035616637418784441039625 50276712478064088330779719)
  ·
    refine ⟨75415068717096132496169579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50276712478064088330779719 75415068717096132496169579)
    ·
      refine ⟨113122603075644198744254369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75415068717096132496169579 113122603075644198744254369)
      ·
        refine ⟨84841952306733149058190777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113122603075644198744254369 84841952306733149058190777)
        ·
          refine ⟨63631464230049861793643083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84841952306733149058190777 63631464230049861793643083)
          ·
            refine ⟨95447196345074792690464625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63631464230049861793643083 95447196345074792690464625)
            ·
              refine ⟨71585397258806094517848469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95447196345074792690464625 71585397258806094517848469)
              ·
                refine ⟨3355565496506535680524147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71585397258806094517848469 3355565496506535680524147)
                ·
                  refine ⟨5033348244759803520786221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355565496506535680524147 5033348244759803520786221)
                  ·
                    refine ⟨1887505591784926320294833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5033348244759803520786221 1887505591784926320294833)
                    ·
                      refine ⟨1415629193838694740221125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1887505591784926320294833 1415629193838694740221125)
                      ·
                        rfl

theorem cell23_2756928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 1, 3, 2].length) (baseStart_2756928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756928 prefixEnd_2756928 := by exact prefixLift 2756928
  have htrace : WordTrace (prefixWord ++ tailWord_2756928) baseStart_2756928 baseEnd_2756928 := by
    simpa [prefixWord, tailWord_2756928, baseEnd_2756928] using wordTrace_append hprefix tailTrace_2756928
  have hstable : (prefixWord ++ tailWord_2756928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756928).length < 2 ^ (prefixWord ++ tailWord_2756928).sum := by decide
  have hdescent : baseEnd_2756928 < baseStart_2756928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756954 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6]
def baseStart_2756954 : Nat := 118140960795 + 2756954 * 2 ^ 59
def prefixEnd_2756954 : Nat := 4983230072969 + 3 ^ 40 * 2756954 * 2
def baseEnd_2756954 : Nat := 1415642544335711638496005

theorem tailTrace_2756954 : CollatzResearch.WordTrace tailWord_2756954 prefixEnd_2756954 1415642544335711638496005 := by
  unfold tailWord_2756954
  simp only [CollatzResearch.WordTrace]
  refine ⟨25138593313508495775501479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67036248836022655401337277 25138593313508495775501479)
  ·
    refine ⟨37707889970262743663252219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25138593313508495775501479 37707889970262743663252219)
    ·
      refine ⟨56561834955394115494878329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37707889970262743663252219 56561834955394115494878329)
      ·
        refine ⟨42421376216545586621158747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56561834955394115494878329 42421376216545586621158747)
        ·
          refine ⟨63632064324818379931738121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42421376216545586621158747 63632064324818379931738121)
          ·
            refine ⟨47724048243613784948803591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63632064324818379931738121 47724048243613784948803591)
            ·
              refine ⟨71586072365420677423205387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47724048243613784948803591 71586072365420677423205387)
              ·
                refine ⟨107379108548131016134808081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71586072365420677423205387 107379108548131016134808081)
                ·
                  refine ⟨80534331411098262101106061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107379108548131016134808081 80534331411098262101106061)
                  ·
                    refine ⟨30200374279161848287914773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80534331411098262101106061 30200374279161848287914773)
                    ·
                      refine ⟨1415642544335711638496005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30200374279161848287914773 1415642544335711638496005)
                      ·
                        rfl

theorem cell23_2756954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_2756954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756954 prefixEnd_2756954 := by exact prefixLift 2756954
  have htrace : WordTrace (prefixWord ++ tailWord_2756954) baseStart_2756954 baseEnd_2756954 := by
    simpa [prefixWord, tailWord_2756954, baseEnd_2756954] using wordTrace_append hprefix tailTrace_2756954
  have hstable : (prefixWord ++ tailWord_2756954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756954).length < 2 ^ (prefixWord ++ tailWord_2756954).sum := by decide
  have hdescent : baseEnd_2756954 < baseStart_2756954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2756981 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 9]
def baseStart_2756981 : Nat := 118140960795 + 2756981 * 2 ^ 59
def prefixEnd_2756981 : Nat := 4983230072969 + 3 ^ 40 * 2756981 * 2
def baseEnd_2756981 : Nat := 157295156479264781428709

theorem tailTrace_2756981 : CollatzResearch.WordTrace tailWord_2756981 prefixEnd_2756981 157295156479264781428709 := by
  unfold tailWord_2756981
  simp only [CollatzResearch.WordTrace]
  refine ⟨100555358024936166713238797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67036905349957444475492531 100555358024936166713238797)
  ·
    refine ⟨37708259259351062517464549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100555358024936166713238797 37708259259351062517464549)
    ·
      refine ⟨7070298611128324222024603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37708259259351062517464549 7070298611128324222024603)
      ·
        refine ⟨10605447916692486333036905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7070298611128324222024603 10605447916692486333036905)
        ·
          refine ⟨7954085937519364749777679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10605447916692486333036905 7954085937519364749777679)
          ·
            refine ⟨11931128906279047124666519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7954085937519364749777679 11931128906279047124666519)
            ·
              refine ⟨17896693359418570686999779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11931128906279047124666519 17896693359418570686999779)
              ·
                refine ⟨26845040039127856030499669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17896693359418570686999779 26845040039127856030499669)
                ·
                  refine ⟨157295156479264781428709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26845040039127856030499669 157295156479264781428709)
                  ·
                    rfl

theorem cell23_2756981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 9].length) (baseStart_2756981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2756981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2756981 prefixEnd_2756981 := by exact prefixLift 2756981
  have htrace : WordTrace (prefixWord ++ tailWord_2756981) baseStart_2756981 baseEnd_2756981 := by
    simpa [prefixWord, tailWord_2756981, baseEnd_2756981] using wordTrace_append hprefix tailTrace_2756981
  have hstable : (prefixWord ++ tailWord_2756981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2756981).length < 2 ^ (prefixWord ++ tailWord_2756981).sum := by decide
  have hdescent : baseEnd_2756981 < baseStart_2756981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2756981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757071 : List Nat := [1, 1, 2, 1, 1, 4, 1, 6, 6]
def baseStart_2757071 : Nat := 118140960795 + 2757071 * 2 ^ 59
def prefixEnd_2757071 : Nat := 4983230072969 + 3 ^ 40 * 2757071 * 2
def baseEnd_2757071 : Nat := 157300291285809742303663

theorem tailTrace_2757071 : CollatzResearch.WordTrace tailWord_2757071 prefixEnd_2757071 157300291285809742303663 := by
  unfold tailWord_2757071
  simp only [CollatzResearch.WordTrace]
  refine ⟨100558640594610112084015067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67039093729740074722676711 100558640594610112084015067)
  ·
    refine ⟨150837960891915168126022601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100558640594610112084015067 150837960891915168126022601)
    ·
      refine ⟨113128470668936376094516951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150837960891915168126022601 113128470668936376094516951)
      ·
        refine ⟨169692706003404564141775427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113128470668936376094516951 169692706003404564141775427)
        ·
          refine ⟨254539059005106846212663141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169692706003404564141775427 254539059005106846212663141)
          ·
            refine ⟨47726073563457533664874339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 254539059005106846212663141 47726073563457533664874339)
            ·
              refine ⟨71589110345186300497311509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47726073563457533664874339 71589110345186300497311509)
              ·
                refine ⟨3355739547430607835811477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71589110345186300497311509 3355739547430607835811477)
                ·
                  refine ⟨157300291285809742303663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3355739547430607835811477 157300291285809742303663)
                  ·
                    rfl

theorem cell23_2757071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 6].length) (baseStart_2757071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757071 prefixEnd_2757071 := by exact prefixLift 2757071
  have htrace : WordTrace (prefixWord ++ tailWord_2757071) baseStart_2757071 baseEnd_2757071 := by
    simpa [prefixWord, tailWord_2757071, baseEnd_2757071] using wordTrace_append hprefix tailTrace_2757071
  have hstable : (prefixWord ++ tailWord_2757071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757071).length < 2 ^ (prefixWord ++ tailWord_2757071).sum := by decide
  have hdescent : baseEnd_2757071 < baseStart_2757071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757122 : List Nat := [3, 4, 1, 2, 2, 1, 2, 2, 6]
def baseStart_2757122 : Nat := 118140960795 + 2757122 * 2 ^ 59
def prefixEnd_2757122 : Nat := 4983230072969 + 3 ^ 40 * 2757122 * 2
def baseEnd_2757122 : Nat := 157303201009518553466137

theorem tailTrace_2757122 : CollatzResearch.WordTrace tailWord_2757122 prefixEnd_2757122 157303201009518553466137 := by
  unfold tailWord_2757122
  simp only [CollatzResearch.WordTrace]
  refine ⟨25140125179356336948530405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67040333811616898529414413 25140125179356336948530405)
  ·
    refine ⟨4713773471129313177849451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25140125179356336948530405 4713773471129313177849451)
    ·
      refine ⟨7070660206693969766774177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4713773471129313177849451 7070660206693969766774177)
      ·
        refine ⟨5302995155020477325080633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7070660206693969766774177 5302995155020477325080633)
        ·
          refine ⟨3977246366265357993810475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5302995155020477325080633 3977246366265357993810475)
          ·
            refine ⟨5965869549398036990715713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3977246366265357993810475 5965869549398036990715713)
            ·
              refine ⟨4474402162048527743036785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5965869549398036990715713 4474402162048527743036785)
              ·
                refine ⟨3355801621536395807277589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4474402162048527743036785 3355801621536395807277589)
                ·
                  refine ⟨157303201009518553466137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3355801621536395807277589 157303201009518553466137)
                  ·
                    rfl

theorem cell23_2757122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_2757122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757122 prefixEnd_2757122 := by exact prefixLift 2757122
  have htrace : WordTrace (prefixWord ++ tailWord_2757122) baseStart_2757122 baseEnd_2757122 := by
    simpa [prefixWord, tailWord_2757122, baseEnd_2757122] using wordTrace_append hprefix tailTrace_2757122
  have hstable : (prefixWord ++ tailWord_2757122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757122).length < 2 ^ (prefixWord ++ tailWord_2757122).sum := by decide
  have hdescent : baseEnd_2757122 < baseStart_2757122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757125 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 2, 3, 2]
def baseStart_2757125 : Nat := 118140960795 + 2757125 * 2 ^ 59
def prefixEnd_2757125 : Nat := 4983230072969 + 3 ^ 40 * 2757125 * 2
def baseEnd_2757125 : Nat := 1415730349527630469457719

theorem tailTrace_2757125 : CollatzResearch.WordTrace tailWord_2757125 prefixEnd_2757125 1415730349527630469457719 := by
  unfold tailWord_2757125
  simp only [CollatzResearch.WordTrace]
  refine ⟨100560610136414479306480829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67040406757609652870987219 100560610136414479306480829)
  ·
    refine ⟨37710228801155429739930311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100560610136414479306480829 37710228801155429739930311)
    ·
      refine ⟨56565343201733144609895467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37710228801155429739930311 56565343201733144609895467)
      ·
        refine ⟨84848014802599716914843201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56565343201733144609895467 84848014802599716914843201)
        ·
          refine ⟨63636011101949787686132401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84848014802599716914843201 63636011101949787686132401)
          ·
            refine ⟨47727008326462340764599301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63636011101949787686132401 47727008326462340764599301)
            ·
              refine ⟨8948814061211688893362369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47727008326462340764599301 8948814061211688893362369)
              ·
                refine ⟨6711610545908766670021777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8948814061211688893362369 6711610545908766670021777)
                ·
                  refine ⟨5033707909431575002516333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6711610545908766670021777 5033707909431575002516333)
                  ·
                    refine ⟨1887640466036840625943625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5033707909431575002516333 1887640466036840625943625)
                    ·
                      refine ⟨1415730349527630469457719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1887640466036840625943625 1415730349527630469457719)
                      ·
                        rfl

theorem cell23_2757125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 3, 2].length) (baseStart_2757125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757125 prefixEnd_2757125 := by exact prefixLift 2757125
  have htrace : WordTrace (prefixWord ++ tailWord_2757125) baseStart_2757125 baseEnd_2757125 := by
    simpa [prefixWord, tailWord_2757125, baseEnd_2757125] using wordTrace_append hprefix tailTrace_2757125
  have hstable : (prefixWord ++ tailWord_2757125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757125).length < 2 ^ (prefixWord ++ tailWord_2757125).sum := by decide
  have hdescent : baseEnd_2757125 < baseStart_2757125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757148 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 1, 6]
def baseStart_2757148 : Nat := 118140960795 + 2757148 * 2 ^ 59
def prefixEnd_2757148 : Nat := 4983230072969 + 3 ^ 40 * 2757148 * 2
def baseEnd_2757148 : Nat := 471914053194227959823371

theorem tailTrace_2757148 : CollatzResearch.WordTrace tailWord_2757148 prefixEnd_2757148 471914053194227959823371 := by
  unfold tailWord_2757148
  simp only [CollatzResearch.WordTrace]
  refine ⟨50280724507665577117284049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67040966010220769489712065 50280724507665577117284049)
  ·
    refine ⟨37710543380749182837963037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50280724507665577117284049 37710543380749182837963037)
    ·
      refine ⟨14141453767780943564236139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37710543380749182837963037 14141453767780943564236139)
      ·
        refine ⟨21212180651671415346354209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14141453767780943564236139 21212180651671415346354209)
        ·
          refine ⟨15909135488753561509765657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21212180651671415346354209 15909135488753561509765657)
          ·
            refine ⟨11931851616565171132324243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15909135488753561509765657 11931851616565171132324243)
            ·
              refine ⟨17897777424847756698486365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11931851616565171132324243 17897777424847756698486365)
              ·
                refine ⟨6711666534317908761932387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17897777424847756698486365 6711666534317908761932387)
                ·
                  refine ⟨10067499801476863142898581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6711666534317908761932387 10067499801476863142898581)
                  ·
                    refine ⟨471914053194227959823371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10067499801476863142898581 471914053194227959823371)
                    ·
                      rfl

theorem cell23_2757148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_2757148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757148 prefixEnd_2757148 := by exact prefixLift 2757148
  have htrace : WordTrace (prefixWord ++ tailWord_2757148) baseStart_2757148 baseEnd_2757148 := by
    simpa [prefixWord, tailWord_2757148, baseEnd_2757148] using wordTrace_append hprefix tailTrace_2757148
  have hstable : (prefixWord ++ tailWord_2757148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757148).length < 2 ^ (prefixWord ++ tailWord_2757148).sum := by decide
  have hdescent : baseEnd_2757148 < baseStart_2757148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757159 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_2757159 : Nat := 118140960795 + 2757159 * 2 ^ 59
def prefixEnd_2757159 : Nat := 4983230072969 + 3 ^ 40 * 2757159 * 2
def baseEnd_2757159 : Nat := 1415747807869883336432563

theorem tailTrace_2757159 : CollatzResearch.WordTrace tailWord_2757159 prefixEnd_2757159 1415747807869883336432563 := by
  unfold tailWord_2757159
  simp only [CollatzResearch.WordTrace]
  refine ⟨100561850218291303113218531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67041233478860868742145687 100561850218291303113218531)
  ·
    refine ⟨150842775327436954669827797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100561850218291303113218531 150842775327436954669827797)
    ·
      refine ⟨3535377546736803625074089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 150842775327436954669827797 3535377546736803625074089)
      ·
        refine ⟨2651533160052602718805567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3535377546736803625074089 2651533160052602718805567)
        ·
          refine ⟨3977299740078904078208351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2651533160052602718805567 3977299740078904078208351)
          ·
            refine ⟨5965949610118356117312527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3977299740078904078208351 5965949610118356117312527)
            ·
              refine ⟨8948924415177534175968791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5965949610118356117312527 8948924415177534175968791)
              ·
                refine ⟨13423386622766301263953187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8948924415177534175968791 13423386622766301263953187)
                ·
                  refine ⟨20135079934149451895929781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13423386622766301263953187 20135079934149451895929781)
                  ·
                    refine ⟨1887663743826511115243417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20135079934149451895929781 1887663743826511115243417)
                    ·
                      refine ⟨1415747807869883336432563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1887663743826511115243417 1415747807869883336432563)
                      ·
                        rfl

theorem cell23_2757159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_2757159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757159 prefixEnd_2757159 := by exact prefixLift 2757159
  have htrace : WordTrace (prefixWord ++ tailWord_2757159) baseStart_2757159 baseEnd_2757159 := by
    simpa [prefixWord, tailWord_2757159, baseEnd_2757159] using wordTrace_append hprefix tailTrace_2757159
  have hstable : (prefixWord ++ tailWord_2757159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757159).length < 2 ^ (prefixWord ++ tailWord_2757159).sum := by decide
  have hdescent : baseEnd_2757159 < baseStart_2757159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757166 : List Nat := [4, 1, 3, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_2757166 : Nat := 118140960795 + 2757166 * 2 ^ 59
def prefixEnd_2757166 : Nat := 4983230072969 + 3 ^ 40 * 2757166 * 2
def baseEnd_2757166 : Nat := 1415751402234464809045031

theorem tailTrace_2757166 : CollatzResearch.WordTrace tailWord_2757166 prefixEnd_2757166 1415751402234464809045031 := by
  unfold tailWord_2757166
  simp only [CollatzResearch.WordTrace]
  refine ⟨12570263191158242913590419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67041403686177295539148901 12570263191158242913590419)
  ·
    refine ⟨18855394786737364370385629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12570263191158242913590419 18855394786737364370385629)
    ·
      refine ⟨7070773045026511638894611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18855394786737364370385629 7070773045026511638894611)
      ·
        refine ⟨10606159567539767458341917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7070773045026511638894611 10606159567539767458341917)
        ·
          refine ⟨3977309837827412796878219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10606159567539767458341917 3977309837827412796878219)
          ·
            refine ⟨5965964756741119195317329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3977309837827412796878219 5965964756741119195317329)
            ·
              refine ⟨4474473567555839396487997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5965964756741119195317329 4474473567555839396487997)
              ·
                refine ⟨1677927587833439773682999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4474473567555839396487997 1677927587833439773682999)
                ·
                  refine ⟨2516891381750159660524499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677927587833439773682999 2516891381750159660524499)
                  ·
                    refine ⟨3775337072625239490786749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2516891381750159660524499 3775337072625239490786749)
                    ·
                      refine ⟨1415751402234464809045031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3775337072625239490786749 1415751402234464809045031)
                      ·
                        rfl

theorem cell23_2757166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_2757166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757166 prefixEnd_2757166 := by exact prefixLift 2757166
  have htrace : WordTrace (prefixWord ++ tailWord_2757166) baseStart_2757166 baseEnd_2757166 := by
    simpa [prefixWord, tailWord_2757166, baseEnd_2757166] using wordTrace_append hprefix tailTrace_2757166
  have hstable : (prefixWord ++ tailWord_2757166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757166).length < 2 ^ (prefixWord ++ tailWord_2757166).sum := by decide
  have hdescent : baseEnd_2757166 < baseStart_2757166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757168 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 4]
def baseStart_2757168 : Nat := 118140960795 + 2757168 * 2 ^ 59
def prefixEnd_2757168 : Nat := 4983230072969 + 3 ^ 40 * 2757168 * 2
def baseEnd_2757168 : Nat := 1415752429195773801220021

theorem tailTrace_2757168 : CollatzResearch.WordTrace tailWord_2757168 prefixEnd_2757168 1415752429195773801220021 := by
  unfold tailWord_2757168
  simp only [CollatzResearch.WordTrace]
  refine ⟨50281089237629348825148079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67041452316839131766864105 50281089237629348825148079)
  ·
    refine ⟨75421633856444023237722119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50281089237629348825148079 75421633856444023237722119)
    ·
      refine ⟨113132450784666034856583179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75421633856444023237722119 113132450784666034856583179)
      ·
        refine ⟨169698676176999052284874769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113132450784666034856583179 169698676176999052284874769)
        ·
          refine ⟨127274007132749289213656077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169698676176999052284874769 127274007132749289213656077)
          ·
            refine ⟨47727752674780983455121029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127274007132749289213656077 47727752674780983455121029)
            ·
              refine ⟨8948953626521434397835193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47727752674780983455121029 8948953626521434397835193)
              ·
                refine ⟨6711715219891075798376395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8948953626521434397835193 6711715219891075798376395)
                ·
                  refine ⟨10067572829836613697564593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6711715219891075798376395 10067572829836613697564593)
                  ·
                    refine ⟨7550679622377460273173445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10067572829836613697564593 7550679622377460273173445)
                    ·
                      refine ⟨1415752429195773801220021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7550679622377460273173445 1415752429195773801220021)
                      ·
                        rfl

theorem cell23_2757168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_2757168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757168 prefixEnd_2757168 := by exact prefixLift 2757168
  have htrace : WordTrace (prefixWord ++ tailWord_2757168) baseStart_2757168 baseEnd_2757168 := by
    simpa [prefixWord, tailWord_2757168, baseEnd_2757168] using wordTrace_append hprefix tailTrace_2757168
  have hstable : (prefixWord ++ tailWord_2757168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757168).length < 2 ^ (prefixWord ++ tailWord_2757168).sum := by decide
  have hdescent : baseEnd_2757168 < baseStart_2757168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757175 : List Nat := [1, 1, 3, 1, 2, 3, 3, 3, 1, 2, 3]
def baseStart_2757175 : Nat := 118140960795 + 2757175 * 2 ^ 59
def prefixEnd_2757175 : Nat := 4983230072969 + 3 ^ 40 * 2757175 * 2
def baseEnd_2757175 : Nat := 1415756023560355273832489

theorem tailTrace_2757175 : CollatzResearch.WordTrace tailWord_2757175 prefixEnd_2757175 1415756023560355273832489 := by
  unfold tailWord_2757175
  simp only [CollatzResearch.WordTrace]
  refine ⟨100562433786233337845800979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67041622524155558563867319 100562433786233337845800979)
  ·
    refine ⟨150843650679350006768701469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100562433786233337845800979 150843650679350006768701469)
    ·
      refine ⟨56566369004756252538263051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150843650679350006768701469 56566369004756252538263051)
      ·
        refine ⟨84849553507134378807394577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56566369004756252538263051 84849553507134378807394577)
        ·
          refine ⟨63637165130350784105545933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84849553507134378807394577 63637165130350784105545933)
          ·
            refine ⟨23863936923881544039579725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63637165130350784105545933 23863936923881544039579725)
            ·
              refine ⟨8948976346455579014842397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23863936923881544039579725 8948976346455579014842397)
              ·
                refine ⟨3355866129920842130565899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8948976346455579014842397 3355866129920842130565899)
                ·
                  refine ⟨5033799194881263195848849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355866129920842130565899 5033799194881263195848849)
                  ·
                    refine ⟨3775349396160947396886637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5033799194881263195848849 3775349396160947396886637)
                    ·
                      refine ⟨1415756023560355273832489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3775349396160947396886637 1415756023560355273832489)
                      ·
                        rfl

theorem cell23_2757175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_2757175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757175 prefixEnd_2757175 := by exact prefixLift 2757175
  have htrace : WordTrace (prefixWord ++ tailWord_2757175) baseStart_2757175 baseEnd_2757175 := by
    simpa [prefixWord, tailWord_2757175, baseEnd_2757175] using wordTrace_append hprefix tailTrace_2757175
  have hstable : (prefixWord ++ tailWord_2757175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757175).length < 2 ^ (prefixWord ++ tailWord_2757175).sum := by decide
  have hdescent : baseEnd_2757175 < baseStart_2757175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757189 : List Nat := [1, 3, 1, 1, 1, 5, 2, 4, 1, 2, 2]
def baseStart_2757189 : Nat := 118140960795 + 2757189 * 2 ^ 59
def prefixEnd_2757189 : Nat := 4983230072969 + 3 ^ 40 * 2757189 * 2
def baseEnd_2757189 : Nat := 1415763212289518219057425

theorem tailTrace_2757189 : CollatzResearch.WordTrace tailWord_2757189 prefixEnd_2757189 1415763212289518219057425 := by
  unfold tailWord_2757189
  simp only [CollatzResearch.WordTrace]
  refine ⟨100562944408182618236810621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67041962938788412157873747 100562944408182618236810621)
  ·
    refine ⟨37711104153068481838803983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100562944408182618236810621 37711104153068481838803983)
    ·
      refine ⟨56566656229602722758205975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37711104153068481838803983 56566656229602722758205975)
      ·
        refine ⟨84849984344404084137308963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56566656229602722758205975 84849984344404084137308963)
        ·
          refine ⟨127274976516606126205963445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84849984344404084137308963 127274976516606126205963445)
          ·
            refine ⟨11932029048431824331809073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127274976516606126205963445 11932029048431824331809073)
            ·
              refine ⟨8949021786323868248856805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11932029048431824331809073 8949021786323868248856805)
              ·
                refine ⟨1677941584935725296660651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8949021786323868248856805 1677941584935725296660651)
                ·
                  refine ⟨2516912377403587944990977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677941584935725296660651 2516912377403587944990977)
                  ·
                    refine ⟨1887684283052690958743233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2516912377403587944990977 1887684283052690958743233)
                    ·
                      refine ⟨1415763212289518219057425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1887684283052690958743233 1415763212289518219057425)
                      ·
                        rfl

theorem cell23_2757189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 1, 2, 2].length) (baseStart_2757189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757189 prefixEnd_2757189 := by exact prefixLift 2757189
  have htrace : WordTrace (prefixWord ++ tailWord_2757189) baseStart_2757189 baseEnd_2757189 := by
    simpa [prefixWord, tailWord_2757189, baseEnd_2757189] using wordTrace_append hprefix tailTrace_2757189
  have hstable : (prefixWord ++ tailWord_2757189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757189).length < 2 ^ (prefixWord ++ tailWord_2757189).sum := by decide
  have hdescent : baseEnd_2757189 < baseStart_2757189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757205 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 1, 3, 3]
def baseStart_2757205 : Nat := 118140960795 + 2757205 * 2 ^ 59
def prefixEnd_2757205 : Nat := 4983230072969 + 3 ^ 40 * 2757205 * 2
def baseEnd_2757205 : Nat := 1415771427979990156457351

theorem tailTrace_2757205 : CollatzResearch.WordTrace tailWord_2757205 prefixEnd_2757205 1415771427979990156457351 := by
  unfold tailWord_2757205
  simp only [CollatzResearch.WordTrace]
  refine ⟨100563527976124652969393069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67042351984083101979595379 100563527976124652969393069)
  ·
    refine ⟨37711322991046744863522401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100563527976124652969393069 37711322991046744863522401)
    ·
      refine ⟨28283492243285058647641801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37711322991046744863522401 28283492243285058647641801)
      ·
        refine ⟨21212619182463793985731351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28283492243285058647641801 21212619182463793985731351)
        ·
          refine ⟨31818928773695690978597027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21212619182463793985731351 31818928773695690978597027)
          ·
            refine ⟨47728393160543536467895541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31818928773695690978597027 47728393160543536467895541)
            ·
              refine ⟨4474536858800956543865207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47728393160543536467895541 4474536858800956543865207)
              ·
                refine ⟨6711805288201434815797811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4474536858800956543865207 6711805288201434815797811)
                ·
                  refine ⟨10067707932302152223696717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6711805288201434815797811 10067707932302152223696717)
                  ·
                    refine ⟨3775390474613307083886269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10067707932302152223696717 3775390474613307083886269)
                    ·
                      refine ⟨1415771427979990156457351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3775390474613307083886269 1415771427979990156457351)
                      ·
                        rfl

theorem cell23_2757205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_2757205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757205 prefixEnd_2757205 := by exact prefixLift 2757205
  have htrace : WordTrace (prefixWord ++ tailWord_2757205) baseStart_2757205 baseEnd_2757205 := by
    simpa [prefixWord, tailWord_2757205, baseEnd_2757205] using wordTrace_append hprefix tailTrace_2757205
  have hstable : (prefixWord ++ tailWord_2757205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757205).length < 2 ^ (prefixWord ++ tailWord_2757205).sum := by decide
  have hdescent : baseEnd_2757205 < baseStart_2757205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757212 : List Nat := [2, 2, 4, 1, 3, 2, 2, 7]
def baseStart_2757212 : Nat := 118140960795 + 2757212 * 2 ^ 59
def prefixEnd_2757212 : Nat := 4983230072969 + 3 ^ 40 * 2757212 * 2
def baseEnd_2757212 : Nat := 52436111938687838113697

theorem tailTrace_2757212 : CollatzResearch.WordTrace tailWord_2757212 prefixEnd_2757212 52436111938687838113697 := by
  unfold tailWord_2757212
  simp only [CollatzResearch.WordTrace]
  refine ⟨50281891643549646582448945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67042522191399528776598593 50281891643549646582448945)
  ·
    refine ⟨37711418732662234936836709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50281891643549646582448945 37711418732662234936836709)
    ·
      refine ⟨7070891012374169050656883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37711418732662234936836709 7070891012374169050656883)
      ·
        refine ⟨10606336518561253575985325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7070891012374169050656883 10606336518561253575985325)
        ·
          refine ⟨3977376194460470090994497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10606336518561253575985325 3977376194460470090994497)
          ·
            refine ⟨2983032145845352568245873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3977376194460470090994497 2983032145845352568245873)
            ·
              refine ⟨2237274109384014426184405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2983032145845352568245873 2237274109384014426184405)
              ·
                refine ⟨52436111938687838113697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2237274109384014426184405 52436111938687838113697)
                ·
                  rfl

theorem cell23_2757212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 7].length) (baseStart_2757212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757212 prefixEnd_2757212 := by exact prefixLift 2757212
  have htrace : WordTrace (prefixWord ++ tailWord_2757212) baseStart_2757212 baseEnd_2757212 := by
    simpa [prefixWord, tailWord_2757212, baseEnd_2757212] using wordTrace_append hprefix tailTrace_2757212
  have hstable : (prefixWord ++ tailWord_2757212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757212).length < 2 ^ (prefixWord ++ tailWord_2757212).sum := by decide
  have hdescent : baseEnd_2757212 < baseStart_2757212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757215 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 3, 3, 2]
def baseStart_2757215 : Nat := 118140960795 + 2757215 * 2 ^ 59
def prefixEnd_2757215 : Nat := 4983230072969 + 3 ^ 40 * 2757215 * 2
def baseEnd_2757215 : Nat := 1415776562786535117332305

theorem tailTrace_2757215 : CollatzResearch.WordTrace tailWord_2757215 prefixEnd_2757215 1415776562786535117332305 := by
  unfold tailWord_2757215
  simp only [CollatzResearch.WordTrace]
  refine ⟨100563892706088424677257099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67042595137392283118171399 100563892706088424677257099)
  ·
    refine ⟨150845839059132637015885649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100563892706088424677257099 150845839059132637015885649)
    ·
      refine ⟨113134379294349477761914237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150845839059132637015885649 113134379294349477761914237)
      ·
        refine ⟨42425392235381054160717839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113134379294349477761914237 42425392235381054160717839)
        ·
          refine ⟨63638088353071581241076759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42425392235381054160717839 63638088353071581241076759)
          ·
            refine ⟨95457132529607371861615139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63638088353071581241076759 95457132529607371861615139)
            ·
              refine ⟨143185698794411057792422709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95457132529607371861615139 143185698794411057792422709)
              ·
                refine ⟨13423659261976036668039629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143185698794411057792422709 13423659261976036668039629)
                ·
                  refine ⟨5033872223241013750514861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13423659261976036668039629 5033872223241013750514861)
                  ·
                    refine ⟨1887702083715380156443073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5033872223241013750514861 1887702083715380156443073)
                    ·
                      refine ⟨1415776562786535117332305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1887702083715380156443073 1415776562786535117332305)
                      ·
                        rfl

theorem cell23_2757215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_2757215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757215 prefixEnd_2757215 := by exact prefixLift 2757215
  have htrace : WordTrace (prefixWord ++ tailWord_2757215) baseStart_2757215 baseEnd_2757215 := by
    simpa [prefixWord, tailWord_2757215, baseEnd_2757215] using wordTrace_append hprefix tailTrace_2757215
  have hstable : (prefixWord ++ tailWord_2757215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757215).length < 2 ^ (prefixWord ++ tailWord_2757215).sum := by decide
  have hdescent : baseEnd_2757215 < baseStart_2757215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757250 : List Nat := [3, 4, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2757250 : Nat := 118140960795 + 2757250 * 2 ^ 59
def prefixEnd_2757250 : Nat := 4983230072969 + 3 ^ 40 * 2757250 * 2
def baseEnd_2757250 : Nat := 471931511536480826798215

theorem tailTrace_2757250 : CollatzResearch.WordTrace tailWord_2757250 prefixEnd_2757250 471931511536480826798215 := by
  unfold tailWord_2757250
  simp only [CollatzResearch.WordTrace]
  refine ⟨25141292315240406413695301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67043446173974417103187469 25141292315240406413695301)
  ·
    refine ⟨4713992309107576202567869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25141292315240406413695301 4713992309107576202567869)
    ·
      refine ⟨1767747115915341075962951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4713992309107576202567869 1767747115915341075962951)
      ·
        refine ⟨2651620673873011613944427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1767747115915341075962951 2651620673873011613944427)
        ·
          refine ⟨3977431010809517420916641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2651620673873011613944427 3977431010809517420916641)
          ·
            refine ⟨2983073258107138065687481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3977431010809517420916641 2983073258107138065687481)
            ·
              refine ⟨2237304943580353549265611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2983073258107138065687481 2237304943580353549265611)
              ·
                refine ⟨3355957415370530323898417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237304943580353549265611 3355957415370530323898417)
                ·
                  refine ⟨2516968061527897742923813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3355957415370530323898417 2516968061527897742923813)
                  ·
                    refine ⟨471931511536480826798215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2516968061527897742923813 471931511536480826798215)
                    ·
                      rfl

theorem cell23_2757250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2757250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757250 prefixEnd_2757250 := by exact prefixLift 2757250
  have htrace : WordTrace (prefixWord ++ tailWord_2757250) baseStart_2757250 baseEnd_2757250 := by
    simpa [prefixWord, tailWord_2757250, baseEnd_2757250] using wordTrace_append hprefix tailTrace_2757250
  have hstable : (prefixWord ++ tailWord_2757250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757250).length < 2 ^ (prefixWord ++ tailWord_2757250).sum := by decide
  have hdescent : baseEnd_2757250 < baseStart_2757250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757262 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2]
def baseStart_2757262 : Nat := 118140960795 + 2757262 * 2 ^ 59
def prefixEnd_2757262 : Nat := 4983230072969 + 3 ^ 40 * 2757262 * 2
def baseEnd_2757262 : Nat := 1415800696377296433444589

theorem tailTrace_2757262 : CollatzResearch.WordTrace tailWord_2757262 prefixEnd_2757262 1415800696377296433444589 := by
  unfold tailWord_2757262
  simp only [CollatzResearch.WordTrace]
  refine ⟨12570700867114768963027255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67043737957945434469478693 12570700867114768963027255)
  ·
    refine ⟨18856051300672153444540883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12570700867114768963027255 18856051300672153444540883)
    ·
      refine ⟨28284076951008230166811325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18856051300672153444540883 28284076951008230166811325)
      ·
        refine ⟨10606528856628086312554247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28284076951008230166811325 10606528856628086312554247)
        ·
          refine ⟨15909793284942129468831371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10606528856628086312554247 15909793284942129468831371)
          ·
            refine ⟨23864689927413194203247057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15909793284942129468831371 23864689927413194203247057)
            ·
              refine ⟨17898517445559895652435293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23864689927413194203247057 17898517445559895652435293)
              ·
                refine ⟨6711944042084960869663235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17898517445559895652435293 6711944042084960869663235)
                ·
                  refine ⟨10067916063127441304494853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6711944042084960869663235 10067916063127441304494853)
                  ·
                    refine ⟨1887734261836395244592785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10067916063127441304494853 1887734261836395244592785)
                    ·
                      refine ⟨1415800696377296433444589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1887734261836395244592785 1415800696377296433444589)
                      ·
                        rfl

theorem cell23_2757262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_2757262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757262 prefixEnd_2757262 := by exact prefixLift 2757262
  have htrace : WordTrace (prefixWord ++ tailWord_2757262) baseStart_2757262 baseEnd_2757262 := by
    simpa [prefixWord, tailWord_2757262, baseEnd_2757262] using wordTrace_append hprefix tailTrace_2757262
  have hstable : (prefixWord ++ tailWord_2757262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757262).length < 2 ^ (prefixWord ++ tailWord_2757262).sum := by decide
  have hdescent : baseEnd_2757262 < baseStart_2757262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757266 : List Nat := [3, 2, 3, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_2757266 : Nat := 118140960795 + 2757266 * 2 ^ 59
def prefixEnd_2757266 : Nat := 4983230072969 + 3 ^ 40 * 2757266 * 2
def baseEnd_2757266 : Nat := 1415802750299914417794571

theorem tailTrace_2757266 : CollatzResearch.WordTrace tailWord_2757266 prefixEnd_2757266 1415802750299914417794571 := by
  unfold tailWord_2757266
  simp only [CollatzResearch.WordTrace]
  refine ⟨25141438207225915096840913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67043835219269106924909101 25141438207225915096840913)
  ·
    refine ⟨18856078655419436322630685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25141438207225915096840913 18856078655419436322630685)
    ·
      refine ⟨7071029495782288620986507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18856078655419436322630685 7071029495782288620986507)
      ·
        refine ⟨10606544243673432931479761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7071029495782288620986507 10606544243673432931479761)
        ·
          refine ⟨7954908182755074698609821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10606544243673432931479761 7954908182755074698609821)
          ·
            refine ⟨2983090568533153011978683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7954908182755074698609821 2983090568533153011978683)
            ·
              refine ⟨4474635852799729517968025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2983090568533153011978683 4474635852799729517968025)
              ·
                refine ⟨3355976889599797138476019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4474635852799729517968025 3355976889599797138476019)
                ·
                  refine ⟨5033965334399695707714029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355976889599797138476019 5033965334399695707714029)
                  ·
                    refine ⟨1887737000399885890392761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5033965334399695707714029 1887737000399885890392761)
                    ·
                      refine ⟨1415802750299914417794571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1887737000399885890392761 1415802750299914417794571)
                      ·
                        rfl

theorem cell23_2757266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_2757266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757266 prefixEnd_2757266 := by exact prefixLift 2757266
  have htrace : WordTrace (prefixWord ++ tailWord_2757266) baseStart_2757266 baseEnd_2757266 := by
    simpa [prefixWord, tailWord_2757266, baseEnd_2757266] using wordTrace_append hprefix tailTrace_2757266
  have hstable : (prefixWord ++ tailWord_2757266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757266).length < 2 ^ (prefixWord ++ tailWord_2757266).sum := by decide
  have hdescent : baseEnd_2757266 < baseStart_2757266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757285 : List Nat := [1, 3, 1, 2, 1, 2, 1, 7, 5]
def baseStart_2757285 : Nat := 118140960795 + 2757285 * 2 ^ 59
def prefixEnd_2757285 : Nat := 4983230072969 + 3 ^ 40 * 2757285 * 2
def baseEnd_2757285 : Nat := 157312500714705538161887

theorem tailTrace_2757285 : CollatzResearch.WordTrace tailWord_2757285 prefixEnd_2757285 157312500714705538161887 := by
  unfold tailWord_2757285
  simp only [CollatzResearch.WordTrace]
  refine ⟨100566445815834826632305309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67044297210556551088203539 100566445815834826632305309)
  ·
    refine ⟨37712417180938059987114491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100566445815834826632305309 37712417180938059987114491)
    ·
      refine ⟨56568625771407089980671737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37712417180938059987114491 56568625771407089980671737)
      ·
        refine ⟨42426469328555317485503803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56568625771407089980671737 42426469328555317485503803)
        ·
          refine ⟨63639703992832976228255705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42426469328555317485503803 63639703992832976228255705)
          ·
            refine ⟨47729777994624732171191779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63639703992832976228255705 47729777994624732171191779)
            ·
              refine ⟨71594666991937098256787669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47729777994624732171191779 71594666991937098256787669)
              ·
                refine ⟨1678000007623525740393461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 71594666991937098256787669 1678000007623525740393461)
                ·
                  refine ⟨157312500714705538161887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1678000007623525740393461 157312500714705538161887)
                  ·
                    rfl

theorem cell23_2757285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 5].length) (baseStart_2757285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757285 prefixEnd_2757285 := by exact prefixLift 2757285
  have htrace : WordTrace (prefixWord ++ tailWord_2757285) baseStart_2757285 baseEnd_2757285 := by
    simpa [prefixWord, tailWord_2757285, baseEnd_2757285] using wordTrace_append hprefix tailTrace_2757285
  have hstable : (prefixWord ++ tailWord_2757285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757285).length < 2 ^ (prefixWord ++ tailWord_2757285).sum := by decide
  have hdescent : baseEnd_2757285 < baseStart_2757285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757298 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 3, 7]
def baseStart_2757298 : Nat := 118140960795 + 2757298 * 2 ^ 59
def prefixEnd_2757298 : Nat := 4983230072969 + 3 ^ 40 * 2757298 * 2
def baseEnd_2757298 : Nat := 471939727226952764198141

theorem tailTrace_2757298 : CollatzResearch.WordTrace tailWord_2757298 prefixEnd_2757298 471939727226952764198141 := by
  unfold tailWord_2757298
  simp only [CollatzResearch.WordTrace]
  refine ⟨25141729991196932463132137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67044613309858486568352365 25141729991196932463132137)
  ·
    refine ⟨18856297493397699347349103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25141729991196932463132137 18856297493397699347349103)
    ·
      refine ⟨28284446240096549021023655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18856297493397699347349103 28284446240096549021023655)
      ·
        refine ⟨42426669360144823531535483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28284446240096549021023655 42426669360144823531535483)
        ·
          refine ⟨63640004040217235297303225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42426669360144823531535483 63640004040217235297303225)
          ·
            refine ⟨47730003030162926472977419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63640004040217235297303225 47730003030162926472977419)
            ·
              refine ⟨71595004545244389709466129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47730003030162926472977419 71595004545244389709466129)
              ·
                refine ⟨53696253408933292282099597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71595004545244389709466129 53696253408933292282099597)
                ·
                  refine ⟨20136095028349984605787349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53696253408933292282099597 20136095028349984605787349)
                  ·
                    refine ⟨471939727226952764198141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20136095028349984605787349 471939727226952764198141)
                    ·
                      rfl

theorem cell23_2757298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_2757298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757298 prefixEnd_2757298 := by exact prefixLift 2757298
  have htrace : WordTrace (prefixWord ++ tailWord_2757298) baseStart_2757298 baseEnd_2757298 := by
    simpa [prefixWord, tailWord_2757298, baseEnd_2757298] using wordTrace_append hprefix tailTrace_2757298
  have hstable : (prefixWord ++ tailWord_2757298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757298).length < 2 ^ (prefixWord ++ tailWord_2757298).sum := by decide
  have hdescent : baseEnd_2757298 < baseStart_2757298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757332 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_2757332 : Nat := 118140960795 + 2757332 * 2 ^ 59
def prefixEnd_2757332 : Nat := 4983230072969 + 3 ^ 40 * 2757332 * 2
def baseEnd_2757332 : Nat := 471945546674370386523089

theorem tailTrace_2757332 : CollatzResearch.WordTrace tailWord_2757332 prefixEnd_2757332 471945546674370386523089 := by
  unfold tailWord_2757332
  simp only [CollatzResearch.WordTrace]
  refine ⟨50284080023332276829633125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67045440031109702439510833 50284080023332276829633125)
  ·
    refine ⟨9428265004374801905556211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50284080023332276829633125 9428265004374801905556211)
    ·
      refine ⟨14142397506562202858334317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9428265004374801905556211 14142397506562202858334317)
      ·
        refine ⟨5303399064960826071875369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14142397506562202858334317 5303399064960826071875369)
        ·
          refine ⟨3977549298720619553906527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5303399064960826071875369 3977549298720619553906527)
          ·
            refine ⟨5966323948080929330859791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3977549298720619553906527 5966323948080929330859791)
            ·
              refine ⟨8949485922121393996289687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5966323948080929330859791 8949485922121393996289687)
              ·
                refine ⟨13424228883182090994434531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8949485922121393996289687 13424228883182090994434531)
                ·
                  refine ⟨20136343324773136491651797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13424228883182090994434531 20136343324773136491651797)
                  ·
                    refine ⟨471945546674370386523089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20136343324773136491651797 471945546674370386523089)
                    ·
                      rfl

theorem cell23_2757332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_2757332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757332 prefixEnd_2757332 := by exact prefixLift 2757332
  have htrace : WordTrace (prefixWord ++ tailWord_2757332) baseStart_2757332 baseEnd_2757332 := by
    simpa [prefixWord, tailWord_2757332, baseEnd_2757332] using wordTrace_append hprefix tailTrace_2757332
  have hstable : (prefixWord ++ tailWord_2757332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757332).length < 2 ^ (prefixWord ++ tailWord_2757332).sum := by decide
  have hdescent : baseEnd_2757332 < baseStart_2757332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757335 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 4]
def baseStart_2757335 : Nat := 118140960795 + 2757335 * 2 ^ 59
def prefixEnd_2757335 : Nat := 4983230072969 + 3 ^ 40 * 2757335 * 2
def baseEnd_2757335 : Nat := 1415838180465074647831753

theorem tailTrace_2757335 : CollatzResearch.WordTrace tailWord_2757335 prefixEnd_2757335 1415838180465074647831753 := by
  unfold tailWord_2757335
  simp only [CollatzResearch.WordTrace]
  refine ⟨100568269465653685171625459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67045512977102456781083639 100568269465653685171625459)
  ·
    refine ⟨150852404198480527757438189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100568269465653685171625459 150852404198480527757438189)
    ·
      refine ⟨56569651574430197909039321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150852404198480527757438189 56569651574430197909039321)
      ·
        refine ⟨42427238680822648431779491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56569651574430197909039321 42427238680822648431779491)
        ·
          refine ⟨63640858021233972647669237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42427238680822648431779491 63640858021233972647669237)
          ·
            refine ⟨5966330439490684935718991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63640858021233972647669237 5966330439490684935718991)
            ·
              refine ⟨8949495659236027403578487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5966330439490684935718991 8949495659236027403578487)
              ·
                refine ⟨13424243488854041105367731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8949495659236027403578487 13424243488854041105367731)
                ·
                  refine ⟨20136365233281061658051597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13424243488854041105367731 20136365233281061658051597)
                  ·
                    refine ⟨7551136962480398121769349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20136365233281061658051597 7551136962480398121769349)
                    ·
                      refine ⟨1415838180465074647831753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7551136962480398121769349 1415838180465074647831753)
                      ·
                        rfl

theorem cell23_2757335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_2757335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757335 prefixEnd_2757335 := by exact prefixLift 2757335
  have htrace : WordTrace (prefixWord ++ tailWord_2757335) baseStart_2757335 baseEnd_2757335 := by
    simpa [prefixWord, tailWord_2757335, baseEnd_2757335] using wordTrace_append hprefix tailTrace_2757335
  have hstable : (prefixWord ++ tailWord_2757335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757335).length < 2 ^ (prefixWord ++ tailWord_2757335).sum := by decide
  have hdescent : baseEnd_2757335 < baseStart_2757335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757355 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 3]
def baseStart_2757355 : Nat := 118140960795 + 2757355 * 2 ^ 59
def prefixEnd_2757355 : Nat := 4983230072969 + 3 ^ 40 * 2757355 * 2
def baseEnd_2757355 : Nat := 1415848450078164569581661

theorem tailTrace_2757355 : CollatzResearch.WordTrace tailWord_2757355 prefixEnd_2757355 1415848450078164569581661 := by
  unfold tailWord_2757355
  simp only [CollatzResearch.WordTrace]
  refine ⟨100568998925581228587353519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67045999283720819058235679 100568998925581228587353519)
  ·
    refine ⟨150853498388371842881030279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100568998925581228587353519 150853498388371842881030279)
    ·
      refine ⟨226280247582557764321545419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150853498388371842881030279 226280247582557764321545419)
      ·
        refine ⟨339420371373836646482318129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226280247582557764321545419 339420371373836646482318129)
        ·
          refine ⟨254565278530377484861738597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339420371373836646482318129 254565278530377484861738597)
          ·
            refine ⟨47730989724445778411575987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 254565278530377484861738597 47730989724445778411575987)
            ·
              refine ⟨71596484586668667617363981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47730989724445778411575987 71596484586668667617363981)
              ·
                refine ⟨26848681720000750356511493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71596484586668667617363981 26848681720000750356511493)
                ·
                  refine ⟨5034127822500140691845905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26848681720000750356511493 5034127822500140691845905)
                  ·
                    refine ⟨3775595866875105518884429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5034127822500140691845905 3775595866875105518884429)
                    ·
                      refine ⟨1415848450078164569581661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3775595866875105518884429 1415848450078164569581661)
                      ·
                        rfl

theorem cell23_2757355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 3].length) (baseStart_2757355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757355 prefixEnd_2757355 := by exact prefixLift 2757355
  have htrace : WordTrace (prefixWord ++ tailWord_2757355) baseStart_2757355 baseEnd_2757355 := by
    simpa [prefixWord, tailWord_2757355, baseEnd_2757355] using wordTrace_append hprefix tailTrace_2757355
  have hstable : (prefixWord ++ tailWord_2757355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757355).length < 2 ^ (prefixWord ++ tailWord_2757355).sum := by decide
  have hdescent : baseEnd_2757355 < baseStart_2757355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757362 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 3, 4]
def baseStart_2757362 : Nat := 118140960795 + 2757362 * 2 ^ 59
def prefixEnd_2757362 : Nat := 4983230072969 + 3 ^ 40 * 2757362 * 2
def baseEnd_2757362 : Nat := 471950681480915347398043

theorem tailTrace_2757362 : CollatzResearch.WordTrace tailWord_2757362 prefixEnd_2757362 471950681480915347398043 := by
  unfold tailWord_2757362
  simp only [CollatzResearch.WordTrace]
  refine ⟨25142313559138967195714585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67046169491037245855238893 25142313559138967195714585)
  ·
    refine ⟨18856735169354225396785939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25142313559138967195714585 18856735169354225396785939)
    ·
      refine ⟨28285102754031338095178909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18856735169354225396785939 28285102754031338095178909)
      ·
        refine ⟨10606913532761751785692091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28285102754031338095178909 10606913532761751785692091)
        ·
          refine ⟨15910370299142627678538137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10606913532761751785692091 15910370299142627678538137)
          ·
            refine ⟨11932777724356970758903603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15910370299142627678538137 11932777724356970758903603)
            ·
              refine ⟨17899166586535456138355405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11932777724356970758903603 17899166586535456138355405)
              ·
                refine ⟨6712187469950796051883277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17899166586535456138355405 6712187469950796051883277)
                ·
                  refine ⟨2517070301231548519456229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6712187469950796051883277 2517070301231548519456229)
                  ·
                    refine ⟨471950681480915347398043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2517070301231548519456229 471950681480915347398043)
                    ·
                      rfl

theorem cell23_2757362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_2757362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757362 prefixEnd_2757362 := by exact prefixLift 2757362
  have htrace : WordTrace (prefixWord ++ tailWord_2757362) baseStart_2757362 baseEnd_2757362 := by
    simpa [prefixWord, tailWord_2757362, baseEnd_2757362] using wordTrace_append hprefix tailTrace_2757362
  have hstable : (prefixWord ++ tailWord_2757362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757362).length < 2 ^ (prefixWord ++ tailWord_2757362).sum := by decide
  have hdescent : baseEnd_2757362 < baseStart_2757362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757439 : List Nat := [1, 1, 2, 2, 5, 3, 1, 2, 1, 5]
def baseStart_2757439 : Nat := 118140960795 + 2757439 * 2 ^ 59
def prefixEnd_2757439 : Nat := 4983230072969 + 3 ^ 40 * 2757439 * 2
def baseEnd_2757439 : Nat := 471963860817714080310425

theorem tailTrace_2757439 : CollatzResearch.WordTrace tailWord_2757439 prefixEnd_2757439 471963860817714080310425 := by
  unfold tailWord_2757439
  simp only [CollatzResearch.WordTrace]
  refine ⟨100572062657276910933411371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67048041771517940622274247 100572062657276910933411371)
  ·
    refine ⟨150858093985915366400117057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100572062657276910933411371 150858093985915366400117057)
    ·
      refine ⟨113143570489436524800087793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150858093985915366400117057 113143570489436524800087793)
      ·
        refine ⟨84857677867077393600065845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113143570489436524800087793 84857677867077393600065845)
        ·
          refine ⟨7955407300038505650006173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84857677867077393600065845 7955407300038505650006173)
          ·
            refine ⟨2983277737514439618752315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7955407300038505650006173 2983277737514439618752315)
            ·
              refine ⟨4474916606271659428128473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2983277737514439618752315 4474916606271659428128473)
              ·
                refine ⟨3356187454703744571096355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4474916606271659428128473 3356187454703744571096355)
                ·
                  refine ⟨5034281182055616856644533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356187454703744571096355 5034281182055616856644533)
                  ·
                    refine ⟨471963860817714080310425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5034281182055616856644533 471963860817714080310425)
                    ·
                      rfl

theorem cell23_2757439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 5].length) (baseStart_2757439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757439 prefixEnd_2757439 := by exact prefixLift 2757439
  have htrace : WordTrace (prefixWord ++ tailWord_2757439) baseStart_2757439 baseEnd_2757439 := by
    simpa [prefixWord, tailWord_2757439, baseEnd_2757439] using wordTrace_append hprefix tailTrace_2757439
  have hstable : (prefixWord ++ tailWord_2757439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757439).length < 2 ^ (prefixWord ++ tailWord_2757439).sum := by decide
  have hdescent : baseEnd_2757439 < baseStart_2757439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757452 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 1, 6]
def baseStart_2757452 : Nat := 118140960795 + 2757452 * 2 ^ 59
def prefixEnd_2757452 : Nat := 4983230072969 + 3 ^ 40 * 2757452 * 2
def baseEnd_2757452 : Nat := 471966085900550230022905

theorem tailTrace_2757452 : CollatzResearch.WordTrace tailWord_2757452 prefixEnd_2757452 471966085900550230022905 := by
  unfold tailWord_2757452
  simp only [CollatzResearch.WordTrace]
  refine ⟨50286268403114907076817305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67048357870819876102423073 50286268403114907076817305)
  ·
    refine ⟨37714701302336180307612979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50286268403114907076817305 37714701302336180307612979)
    ·
      refine ⟨56572051953504270461419469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37714701302336180307612979 56572051953504270461419469)
      ·
        refine ⟨21214519482564101423032301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56572051953504270461419469 21214519482564101423032301)
        ·
          refine ⟨7955444805961538033637113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21214519482564101423032301 7955444805961538033637113)
          ·
            refine ⟨5966583604471153525227835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7955444805961538033637113 5966583604471153525227835)
            ·
              refine ⟨8949875406706730287841753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5966583604471153525227835 8949875406706730287841753)
              ·
                refine ⟨6712406555030047715881315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8949875406706730287841753 6712406555030047715881315)
                ·
                  refine ⟨10068609832545071573821973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6712406555030047715881315 10068609832545071573821973)
                  ·
                    refine ⟨471966085900550230022905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10068609832545071573821973 471966085900550230022905)
                    ·
                      rfl

theorem cell23_2757452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_2757452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757452 prefixEnd_2757452 := by exact prefixLift 2757452
  have htrace : WordTrace (prefixWord ++ tailWord_2757452) baseStart_2757452 baseEnd_2757452 := by
    simpa [prefixWord, tailWord_2757452, baseEnd_2757452] using wordTrace_append hprefix tailTrace_2757452
  have hstable : (prefixWord ++ tailWord_2757452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757452).length < 2 ^ (prefixWord ++ tailWord_2757452).sum := by decide
  have hdescent : baseEnd_2757452 < baseStart_2757452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757543 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_2757543 : Nat := 118140960795 + 2757543 * 2 ^ 59
def prefixEnd_2757543 : Nat := 4983230072969 + 3 ^ 40 * 2757543 * 2
def baseEnd_2757543 : Nat := 1415944984441209834030797

theorem tailTrace_2757543 : CollatzResearch.WordTrace tailWord_2757543 prefixEnd_2757543 1415944984441209834030797 := by
  unfold tailWord_2757543
  simp only [CollatzResearch.WordTrace]
  refine ⟨100575855848900136695197283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67050570565933424463464855 100575855848900136695197283)
  ·
    refine ⟨150863783773350205042795925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100575855848900136695197283 150863783773350205042795925)
    ·
      refine ⟨7071739864375790861381059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 150863783773350205042795925 7071739864375790861381059)
      ·
        refine ⟨10607609796563686292071589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7071739864375790861381059 10607609796563686292071589)
        ·
          refine ⟨1988926836855691179763423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10607609796563686292071589 1988926836855691179763423)
          ·
            refine ⟨2983390255283536769645135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988926836855691179763423 2983390255283536769645135)
            ·
              refine ⟨4475085382925305154467703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2983390255283536769645135 4475085382925305154467703)
              ·
                refine ⟨6712628074387957731701555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4475085382925305154467703 6712628074387957731701555)
                ·
                  refine ⟨10068942111581936597552333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6712628074387957731701555 10068942111581936597552333)
                  ·
                    refine ⟨3775853291843226224082125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10068942111581936597552333 3775853291843226224082125)
                    ·
                      refine ⟨1415944984441209834030797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3775853291843226224082125 1415944984441209834030797)
                      ·
                        rfl

theorem cell23_2757543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_2757543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757543 prefixEnd_2757543 := by exact prefixLift 2757543
  have htrace : WordTrace (prefixWord ++ tailWord_2757543) baseStart_2757543 baseEnd_2757543 := by
    simpa [prefixWord, tailWord_2757543, baseEnd_2757543] using wordTrace_append hprefix tailTrace_2757543
  have hstable : (prefixWord ++ tailWord_2757543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757543).length < 2 ^ (prefixWord ++ tailWord_2757543).sum := by decide
  have hdescent : baseEnd_2757543 < baseStart_2757543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757553 : List Nat := [1, 2, 2, 4, 3, 1, 2, 2, 1, 3, 2]
def baseStart_2757553 : Nat := 118140960795 + 2757553 * 2 ^ 59
def prefixEnd_2757553 : Nat := 4983230072969 + 3 ^ 40 * 2757553 * 2
def baseEnd_2757553 : Nat := 1415950119247754794905751

theorem tailTrace_2757553 : CollatzResearch.WordTrace tailWord_2757553 prefixEnd_2757553 1415950119247754794905751 := by
  unfold tailWord_2757553
  simp only [CollatzResearch.WordTrace]
  refine ⟨100576220578863908403061313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67050813719242605602040875 100576220578863908403061313)
  ·
    refine ⟨75432165434147931302295985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100576220578863908403061313 75432165434147931302295985)
    ·
      refine ⟨56574124075610948476721989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75432165434147931302295985 56574124075610948476721989)
      ·
        refine ⟨10607648264177052839385373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56574124075610948476721989 10607648264177052839385373)
        ·
          refine ⟨3977868099066394814769515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10607648264177052839385373 3977868099066394814769515)
          ·
            refine ⟨5966802148599592222154273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3977868099066394814769515 5966802148599592222154273)
            ·
              refine ⟨4475101611449694166615705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5966802148599592222154273 4475101611449694166615705)
              ·
                refine ⟨3356326208587270624961779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4475101611449694166615705 3356326208587270624961779)
                ·
                  refine ⟨5034489312880905937442669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356326208587270624961779 5034489312880905937442669)
                  ·
                    refine ⟨1887933492330339726541001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5034489312880905937442669 1887933492330339726541001)
                    ·
                      refine ⟨1415950119247754794905751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1887933492330339726541001 1415950119247754794905751)
                      ·
                        rfl

theorem cell23_2757553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_2757553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757553 prefixEnd_2757553 := by exact prefixLift 2757553
  have htrace : WordTrace (prefixWord ++ tailWord_2757553) baseStart_2757553 baseEnd_2757553 := by
    simpa [prefixWord, tailWord_2757553, baseEnd_2757553] using wordTrace_append hprefix tailTrace_2757553
  have hstable : (prefixWord ++ tailWord_2757553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757553).length < 2 ^ (prefixWord ++ tailWord_2757553).sum := by decide
  have hdescent : baseEnd_2757553 < baseStart_2757553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757555 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 9]
def baseStart_2757555 : Nat := 118140960795 + 2757555 * 2 ^ 59
def prefixEnd_2757555 : Nat := 4983230072969 + 3 ^ 40 * 2757555 * 2
def baseEnd_2757555 : Nat := 157327905134340420786749

theorem tailTrace_2757555 : CollatzResearch.WordTrace tailWord_2757555 prefixEnd_2757555 157327905134340420786749 := by
  unfold tailWord_2757555
  simp only [CollatzResearch.WordTrace]
  refine ⟨100576293524856662744634119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67050862349904441829756079 100576293524856662744634119)
  ·
    refine ⟨150864440287284994116951179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100576293524856662744634119 150864440287284994116951179)
    ·
      refine ⟨226296660430927491175426769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150864440287284994116951179 226296660430927491175426769)
      ·
        refine ⟨169722495323195618381570077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226296660430927491175426769 169722495323195618381570077)
        ·
          refine ⟨63645935746198356893088779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169722495323195618381570077 63645935746198356893088779)
          ·
            refine ⟨95468903619297535339633169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63645935746198356893088779 95468903619297535339633169)
            ·
              refine ⟨71601677714473151504724877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95468903619297535339633169 71601677714473151504724877)
              ·
                refine ⟨26850629142927431814271829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71601677714473151504724877 26850629142927431814271829)
                ·
                  refine ⟨157327905134340420786749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26850629142927431814271829 157327905134340420786749)
                  ·
                    rfl

theorem cell23_2757555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 9].length) (baseStart_2757555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757555 prefixEnd_2757555 := by exact prefixLift 2757555
  have htrace : WordTrace (prefixWord ++ tailWord_2757555) baseStart_2757555 baseEnd_2757555 := by
    simpa [prefixWord, tailWord_2757555, baseEnd_2757555] using wordTrace_append hprefix tailTrace_2757555
  have hstable : (prefixWord ++ tailWord_2757555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757555).length < 2 ^ (prefixWord ++ tailWord_2757555).sum := by decide
  have hdescent : baseEnd_2757555 < baseStart_2757555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757566 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2]
def baseStart_2757566 : Nat := 118140960795 + 2757566 * 2 ^ 59
def prefixEnd_2757566 : Nat := 4983230072969 + 3 ^ 40 * 2757566 * 2
def baseEnd_2757566 : Nat := 1415956794496263244043191

theorem tailTrace_2757566 : CollatzResearch.WordTrace tailWord_2757566 prefixEnd_2757566 1415956794496263244043191 := by
  unfold tailWord_2757566
  simp only [CollatzResearch.WordTrace]
  refine ⟨12572086840977101452910569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67051129818544541082189701 12572086840977101452910569)
  ·
    refine ⟨9429065130732826089682927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12572086840977101452910569 9429065130732826089682927)
    ·
      refine ⟨14143597696099239134524391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9429065130732826089682927 14143597696099239134524391)
      ·
        refine ⟨21215396544148858701786587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14143597696099239134524391 21215396544148858701786587)
        ·
          refine ⟨31823094816223288052679881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21215396544148858701786587 31823094816223288052679881)
          ·
            refine ⟨23867321112167466039509911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31823094816223288052679881 23867321112167466039509911)
            ·
              refine ⟨35800981668251199059264867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23867321112167466039509911 35800981668251199059264867)
              ·
                refine ⟨53701472502376798588897301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35800981668251199059264867 53701472502376798588897301)
                ·
                  refine ⟨2517256523548912433854561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53701472502376798588897301 2517256523548912433854561)
                  ·
                    refine ⟨1887942392661684325390921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2517256523548912433854561 1887942392661684325390921)
                    ·
                      refine ⟨1415956794496263244043191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1887942392661684325390921 1415956794496263244043191)
                      ·
                        rfl

theorem cell23_2757566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_2757566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757566 prefixEnd_2757566 := by exact prefixLift 2757566
  have htrace : WordTrace (prefixWord ++ tailWord_2757566) baseStart_2757566 baseEnd_2757566 := by
    simpa [prefixWord, tailWord_2757566, baseEnd_2757566] using wordTrace_append hprefix tailTrace_2757566
  have hstable : (prefixWord ++ tailWord_2757566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757566).length < 2 ^ (prefixWord ++ tailWord_2757566).sum := by decide
  have hdescent : baseEnd_2757566 < baseStart_2757566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757639 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_2757639 : Nat := 118140960795 + 2757639 * 2 ^ 59
def prefixEnd_2757639 : Nat := 4983230072969 + 3 ^ 40 * 2757639 * 2
def baseEnd_2757639 : Nat := 1415994278584041458430355

theorem tailTrace_2757639 : CollatzResearch.WordTrace tailWord_2757639 prefixEnd_2757639 1415994278584041458430355 := by
  unfold tailWord_2757639
  simp only [CollatzResearch.WordTrace]
  refine ⟨100579357256552345090691971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67052904837701563393794647 100579357256552345090691971)
  ·
    refine ⟨150869035884828517636037957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100579357256552345090691971 150869035884828517636037957)
    ·
      refine ⟨28287944228405347056757117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150869035884828517636037957 28287944228405347056757117)
      ·
        refine ⟨10607979085652005146283919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28287944228405347056757117 10607979085652005146283919)
        ·
          refine ⟨15911968628478007719425879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10607979085652005146283919 15911968628478007719425879)
          ·
            refine ⟨23867952942717011579138819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15911968628478007719425879 23867952942717011579138819)
            ·
              refine ⟨35801929414075517368708229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23867952942717011579138819 35801929414075517368708229)
              ·
                refine ⟨6712861765139159506632793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35801929414075517368708229 6712861765139159506632793)
                ·
                  refine ⟨5034646323854369629974595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6712861765139159506632793 5034646323854369629974595)
                  ·
                    refine ⟨7551969485781554444961893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5034646323854369629974595 7551969485781554444961893)
                    ·
                      refine ⟨1415994278584041458430355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7551969485781554444961893 1415994278584041458430355)
                      ·
                        rfl

theorem cell23_2757639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_2757639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757639 prefixEnd_2757639 := by exact prefixLift 2757639
  have htrace : WordTrace (prefixWord ++ tailWord_2757639) baseStart_2757639 baseEnd_2757639 := by
    simpa [prefixWord, tailWord_2757639, baseEnd_2757639] using wordTrace_append hprefix tailTrace_2757639
  have hstable : (prefixWord ++ tailWord_2757639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757639).length < 2 ^ (prefixWord ++ tailWord_2757639).sum := by decide
  have hdescent : baseEnd_2757639 < baseStart_2757639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757650 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2757650 : Nat := 118140960795 + 2757650 * 2 ^ 59
def prefixEnd_2757650 : Nat := 4983230072969 + 3 ^ 40 * 2757650 * 2
def baseEnd_2757650 : Nat := 1415999926871240915392805

theorem tailTrace_2757650 : CollatzResearch.WordTrace tailWord_2757650 prefixEnd_2757650 1415999926871240915392805 := by
  unfold tailWord_2757650
  simp only [CollatzResearch.WordTrace]
  refine ⟨25144939614878123492335601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67053172306341662646228269 25144939614878123492335601)
  ·
    refine ⟨18858704711158592619251701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25144939614878123492335601 18858704711158592619251701)
    ·
      refine ⟨1768003566671118058054847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18858704711158592619251701 1768003566671118058054847)
      ·
        refine ⟨2652005350006677087082271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1768003566671118058054847 2652005350006677087082271)
        ·
          refine ⟨3978008025010015630623407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2652005350006677087082271 3978008025010015630623407)
          ·
            refine ⟨5967012037515023445935111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3978008025010015630623407 5967012037515023445935111)
            ·
              refine ⟨8950518056272535168902667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5967012037515023445935111 8950518056272535168902667)
              ·
                refine ⟨13425777084408802753354001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8950518056272535168902667 13425777084408802753354001)
                ·
                  refine ⟨10069332813306602065015501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13425777084408802753354001 10069332813306602065015501)
                  ·
                    refine ⟨3775999804989975774380813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10069332813306602065015501 3775999804989975774380813)
                    ·
                      refine ⟨1415999926871240915392805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3775999804989975774380813 1415999926871240915392805)
                      ·
                        rfl

theorem cell23_2757650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2757650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757650 prefixEnd_2757650 := by exact prefixLift 2757650
  have htrace : WordTrace (prefixWord ++ tailWord_2757650) baseStart_2757650 baseEnd_2757650 := by
    simpa [prefixWord, tailWord_2757650, baseEnd_2757650] using wordTrace_append hprefix tailTrace_2757650
  have hstable : (prefixWord ++ tailWord_2757650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757650).length < 2 ^ (prefixWord ++ tailWord_2757650).sum := by decide
  have hdescent : baseEnd_2757650 < baseStart_2757650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757656 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 2, 4, 2]
def baseStart_2757656 : Nat := 118140960795 + 2757656 * 2 ^ 59
def prefixEnd_2757656 : Nat := 4983230072969 + 3 ^ 40 * 2757656 * 2
def baseEnd_2757656 : Nat := 1416003007755167891917777

theorem tailTrace_2757656 : CollatzResearch.WordTrace tailWord_2757656 prefixEnd_2757656 1416003007755167891917777 := by
  unfold tailWord_2757656
  simp only [CollatzResearch.WordTrace]
  refine ⟨50289988648745378497030411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67053318198327171329373881 50289988648745378497030411)
  ·
    refine ⟨75434982973118067745545617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50289988648745378497030411 75434982973118067745545617)
    ·
      refine ⟨56576237229838550809159213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75434982973118067745545617 56576237229838550809159213)
      ·
        refine ⟨21216088961189456553434705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56576237229838550809159213 21216088961189456553434705)
        ·
          refine ⟨15912066720892092415076029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21216088961189456553434705 15912066720892092415076029)
          ·
            refine ⟨5967025020334534655653511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15912066720892092415076029 5967025020334534655653511)
            ·
              refine ⟨8950537530501801983480267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5967025020334534655653511 8950537530501801983480267)
              ·
                refine ⟨13425806295752702975220401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8950537530501801983480267 13425806295752702975220401)
                ·
                  refine ⟨10069354721814527231415301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13425806295752702975220401 10069354721814527231415301)
                  ·
                    refine ⟨1888004010340223855890369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10069354721814527231415301 1888004010340223855890369)
                    ·
                      refine ⟨1416003007755167891917777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1888004010340223855890369 1416003007755167891917777)
                      ·
                        rfl

theorem cell23_2757656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_2757656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757656 prefixEnd_2757656 := by exact prefixLift 2757656
  have htrace : WordTrace (prefixWord ++ tailWord_2757656) baseStart_2757656 baseEnd_2757656 := by
    simpa [prefixWord, tailWord_2757656, baseEnd_2757656] using wordTrace_append hprefix tailTrace_2757656
  have hstable : (prefixWord ++ tailWord_2757656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757656).length < 2 ^ (prefixWord ++ tailWord_2757656).sum := by decide
  have hdescent : baseEnd_2757656 < baseStart_2757656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757666 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_2757666 : Nat := 118140960795 + 2757666 * 2 ^ 59
def prefixEnd_2757666 : Nat := 4983230072969 + 3 ^ 40 * 2757666 * 2
def baseEnd_2757666 : Nat := 472002714187237617597577

theorem tailTrace_2757666 : CollatzResearch.WordTrace tailWord_2757666 prefixEnd_2757666 472002714187237617597577 := by
  unfold tailWord_2757666
  simp only [CollatzResearch.WordTrace]
  refine ⟨25145085506863632175481213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67053561351636352467949901 25145085506863632175481213)
  ·
    refine ⟨9429407065073862065805455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25145085506863632175481213 9429407065073862065805455)
    ·
      refine ⟨14144110597610793098708183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9429407065073862065805455 14144110597610793098708183)
      ·
        refine ⟨21216165896416189648062275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14144110597610793098708183 21216165896416189648062275)
        ·
          refine ⟨31824248844624284472093413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21216165896416189648062275 31824248844624284472093413)
          ·
            refine ⟨5967046658367053338517515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31824248844624284472093413 5967046658367053338517515)
            ·
              refine ⟨8950569987550580007776273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5967046658367053338517515 8950569987550580007776273)
              ·
                refine ⟨6712927490662935005832205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8950569987550580007776273 6712927490662935005832205)
                ·
                  refine ⟨2517347808998600627187077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6712927490662935005832205 2517347808998600627187077)
                  ·
                    refine ⟨472002714187237617597577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2517347808998600627187077 472002714187237617597577)
                    ·
                      rfl

theorem cell23_2757666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_2757666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757666 prefixEnd_2757666 := by exact prefixLift 2757666
  have htrace : WordTrace (prefixWord ++ tailWord_2757666) baseStart_2757666 baseEnd_2757666 := by
    simpa [prefixWord, tailWord_2757666, baseEnd_2757666] using wordTrace_append hprefix tailTrace_2757666
  have hstable : (prefixWord ++ tailWord_2757666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757666).length < 2 ^ (prefixWord ++ tailWord_2757666).sum := by decide
  have hdescent : baseEnd_2757666 < baseStart_2757666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757706 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 3, 1, 3]
def baseStart_2757706 : Nat := 118140960795 + 2757706 * 2 ^ 59
def prefixEnd_2757706 : Nat := 4983230072969 + 3 ^ 40 * 2757706 * 2
def baseEnd_2757706 : Nat := 1416028681787892696292547

theorem tailTrace_2757706 : CollatzResearch.WordTrace tailWord_2757706 prefixEnd_2757706 1416028681787892696292547 := by
  unfold tailWord_2757706
  simp only [CollatzResearch.WordTrace]
  refine ⟨25145450236827403883345243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67054533964873077022253981 25145450236827403883345243)
  ·
    refine ⟨37718175355241105825017865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25145450236827403883345243 37718175355241105825017865)
    ·
      refine ⟨28288631516430829368763399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37718175355241105825017865 28288631516430829368763399)
      ·
        refine ⟨42432947274646244053145099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28288631516430829368763399 42432947274646244053145099)
        ·
          refine ⟨63649420911969366079717649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42432947274646244053145099 63649420911969366079717649)
          ·
            refine ⟨47737065683977024559788237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63649420911969366079717649 47737065683977024559788237)
            ·
              refine ⟨17901399631491384209920589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47737065683977024559788237 17901399631491384209920589)
              ·
                refine ⟨6713024861809269078720221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17901399631491384209920589 6713024861809269078720221)
                ·
                  refine ⟨2517384323178475904520083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6713024861809269078720221 2517384323178475904520083)
                  ·
                    refine ⟨3776076484767713856780125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2517384323178475904520083 3776076484767713856780125)
                    ·
                      refine ⟨1416028681787892696292547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3776076484767713856780125 1416028681787892696292547)
                      ·
                        rfl

theorem cell23_2757706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_2757706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757706 prefixEnd_2757706 := by exact prefixLift 2757706
  have htrace : WordTrace (prefixWord ++ tailWord_2757706) baseStart_2757706 baseEnd_2757706 := by
    simpa [prefixWord, tailWord_2757706, baseEnd_2757706] using wordTrace_append hprefix tailTrace_2757706
  have hstable : (prefixWord ++ tailWord_2757706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757706).length < 2 ^ (prefixWord ++ tailWord_2757706).sum := by decide
  have hdescent : baseEnd_2757706 < baseStart_2757706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757716 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 1, 5, 2]
def baseStart_2757716 : Nat := 118140960795 + 2757716 * 2 ^ 59
def prefixEnd_2757716 : Nat := 4983230072969 + 3 ^ 40 * 2757716 * 2
def baseEnd_2757716 : Nat := 1416033816594437657167501

theorem tailTrace_2757716 : CollatzResearch.WordTrace tailWord_2757716 prefixEnd_2757716 1416033816594437657167501 := by
  unfold tailWord_2757716
  simp only [CollatzResearch.WordTrace]
  refine ⟨50291082838636693620622501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67054777118182258160830001 50291082838636693620622501)
  ·
    refine ⟨9429578032244380053866719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50291082838636693620622501 9429578032244380053866719)
    ·
      refine ⟨14144367048366570080800079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9429578032244380053866719 14144367048366570080800079)
      ·
        refine ⟨21216550572549855121200119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14144367048366570080800079 21216550572549855121200119)
        ·
          refine ⟨31824825858824782681800179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21216550572549855121200119 31824825858824782681800179)
          ·
            refine ⟨47737238788237174022700269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31824825858824782681800179 47737238788237174022700269)
            ·
              refine ⟨17901464545588940258512601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47737238788237174022700269 17901464545588940258512601)
              ·
                refine ⟨13426098409191705193884451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17901464545588940258512601 13426098409191705193884451)
                ·
                  refine ⟨20139147613787557790826677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13426098409191705193884451 20139147613787557790826677)
                  ·
                    refine ⟨1888045088792583542890001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20139147613787557790826677 1888045088792583542890001)
                    ·
                      refine ⟨1416033816594437657167501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1888045088792583542890001 1416033816594437657167501)
                      ·
                        rfl

theorem cell23_2757716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_2757716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757716 prefixEnd_2757716 := by exact prefixLift 2757716
  have htrace : WordTrace (prefixWord ++ tailWord_2757716) baseStart_2757716 baseEnd_2757716 := by
    simpa [prefixWord, tailWord_2757716, baseEnd_2757716] using wordTrace_append hprefix tailTrace_2757716
  have hstable : (prefixWord ++ tailWord_2757716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757716).length < 2 ^ (prefixWord ++ tailWord_2757716).sum := by decide
  have hdescent : baseEnd_2757716 < baseStart_2757716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757729 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_2757729 : Nat := 118140960795 + 2757729 * 2 ^ 59
def prefixEnd_2757729 : Nat := 4983230072969 + 3 ^ 40 * 2757729 * 2
def baseEnd_2757729 : Nat := 1416040491842946106304941

theorem tailTrace_2757729 : CollatzResearch.WordTrace tailWord_2757729 prefixEnd_2757729 1416040491842946106304941 := by
  unfold tailWord_2757729
  simp only [CollatzResearch.WordTrace]
  refine ⟨100582639826226290461468241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67055093217484193640978827 100582639826226290461468241)
  ·
    refine ⟨75436979869669717846101181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100582639826226290461468241 75436979869669717846101181)
    ·
      refine ⟨28288867451126144192287943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75436979869669717846101181 28288867451126144192287943)
      ·
        refine ⟨42433301176689216288431915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28288867451126144192287943 42433301176689216288431915)
        ·
          refine ⟨63649951765033824432647873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42433301176689216288431915 63649951765033824432647873)
          ·
            refine ⟨47737463823775368324485905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63649951765033824432647873 47737463823775368324485905)
            ·
              refine ⟨35803097867831526243364429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47737463823775368324485905 35803097867831526243364429)
              ·
                refine ⟨13426161700436822341261661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35803097867831526243364429 13426161700436822341261661)
                ·
                  refine ⟨5034810637663808377973123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13426161700436822341261661 5034810637663808377973123)
                  ·
                    refine ⟨7552215956495712566959685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5034810637663808377973123 7552215956495712566959685)
                    ·
                      refine ⟨1416040491842946106304941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7552215956495712566959685 1416040491842946106304941)
                      ·
                        rfl

theorem cell23_2757729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_2757729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757729 prefixEnd_2757729 := by exact prefixLift 2757729
  have htrace : WordTrace (prefixWord ++ tailWord_2757729) baseStart_2757729 baseEnd_2757729 := by
    simpa [prefixWord, tailWord_2757729, baseEnd_2757729] using wordTrace_append hprefix tailTrace_2757729
  have hstable : (prefixWord ++ tailWord_2757729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757729).length < 2 ^ (prefixWord ++ tailWord_2757729).sum := by decide
  have hdescent : baseEnd_2757729 < baseStart_2757729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757746 : List Nat := [3, 2, 1, 2, 2, 1, 1, 5, 1, 1, 4]
def baseStart_2757746 : Nat := 118140960795 + 2757746 * 2 ^ 59
def prefixEnd_2757746 : Nat := 4983230072969 + 3 ^ 40 * 2757746 * 2
def baseEnd_2757746 : Nat := 1416049221014072539792363

theorem tailTrace_2757746 : CollatzResearch.WordTrace tailWord_2757746 prefixEnd_2757746 1416049221014072539792363 := by
  unfold tailWord_2757746
  simp only [CollatzResearch.WordTrace]
  refine ⟨25145814966791175591209273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67055506578109801576558061 25145814966791175591209273)
  ·
    refine ⟨18859361225093381693406955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25145814966791175591209273 18859361225093381693406955)
    ·
      refine ⟨28289041837640072540110433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18859361225093381693406955 28289041837640072540110433)
      ·
        refine ⟨21216781378230054405082825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28289041837640072540110433 21216781378230054405082825)
        ·
          refine ⟨15912586033672540803812119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21216781378230054405082825 15912586033672540803812119)
          ·
            refine ⟨23868879050508811205718179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15912586033672540803812119 23868879050508811205718179)
            ·
              refine ⟨35803318575763216808577269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23868879050508811205718179 35803318575763216808577269)
              ·
                refine ⟨3356561116477801575804119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35803318575763216808577269 3356561116477801575804119)
                ·
                  refine ⟨5034841674716702363706179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356561116477801575804119 5034841674716702363706179)
                  ·
                    refine ⟨7552262512075053545559269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5034841674716702363706179 7552262512075053545559269)
                    ·
                      refine ⟨1416049221014072539792363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7552262512075053545559269 1416049221014072539792363)
                      ·
                        rfl

theorem cell23_2757746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_2757746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757746 prefixEnd_2757746 := by exact prefixLift 2757746
  have htrace : WordTrace (prefixWord ++ tailWord_2757746) baseStart_2757746 baseEnd_2757746 := by
    simpa [prefixWord, tailWord_2757746, baseEnd_2757746] using wordTrace_append hprefix tailTrace_2757746
  have hstable : (prefixWord ++ tailWord_2757746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757746).length < 2 ^ (prefixWord ++ tailWord_2757746).sum := by decide
  have hdescent : baseEnd_2757746 < baseStart_2757746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757752 : List Nat := [2, 1, 2, 1, 1, 1, 15]
def baseStart_2757752 : Nat := 118140960795 + 2757752 * 2 ^ 59
def prefixEnd_2757752 : Nat := 4983230072969 + 3 ^ 40 * 2757752 * 2
def baseEnd_2757752 : Nat := 17482127183925919954535

theorem tailTrace_2757752 : CollatzResearch.WordTrace tailWord_2757752 prefixEnd_2757752 17482127183925919954535 := by
  unfold tailWord_2757752
  simp only [CollatzResearch.WordTrace]
  refine ⟨50291739352571482694777755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67055652470095310259703673 50291739352571482694777755)
  ·
    refine ⟨75437609028857224042166633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50291739352571482694777755 75437609028857224042166633)
    ·
      refine ⟨56578206771642918031624975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75437609028857224042166633 56578206771642918031624975)
      ·
        refine ⟨84867310157464377047437463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56578206771642918031624975 84867310157464377047437463)
        ·
          refine ⟨127300965236196565571156195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84867310157464377047437463 127300965236196565571156195)
          ·
            refine ⟨190951447854294848356734293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127300965236196565571156195 190951447854294848356734293)
            ·
              refine ⟨17482127183925919954535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 190951447854294848356734293 17482127183925919954535)
              ·
                rfl

theorem cell23_2757752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 15].length) (baseStart_2757752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757752 prefixEnd_2757752 := by exact prefixLift 2757752
  have htrace : WordTrace (prefixWord ++ tailWord_2757752) baseStart_2757752 baseEnd_2757752 := by
    simpa [prefixWord, tailWord_2757752, baseEnd_2757752] using wordTrace_append hprefix tailTrace_2757752
  have hstable : (prefixWord ++ tailWord_2757752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757752).length < 2 ^ (prefixWord ++ tailWord_2757752).sum := by decide
  have hdescent : baseEnd_2757752 < baseStart_2757752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757756 : List Nat := [2, 2, 2, 1, 1, 3, 2, 4, 2, 4]
def baseStart_2757756 : Nat := 118140960795 + 2757756 * 2 ^ 59
def prefixEnd_2757756 : Nat := 4983230072969 + 3 ^ 40 * 2757756 * 2
def baseEnd_2757756 : Nat := 472018118606872500222439

theorem tailTrace_2757756 : CollatzResearch.WordTrace tailWord_2757756 prefixEnd_2757756 472018118606872500222439 := by
  unfold tailWord_2757756
  simp only [CollatzResearch.WordTrace]
  refine ⟨50291812298564237036350561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67055749731418982715134081 50291812298564237036350561)
  ·
    refine ⟨37718859223923177777262921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50291812298564237036350561 37718859223923177777262921)
    ·
      refine ⟨28289144417942383332947191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37718859223923177777262921 28289144417942383332947191)
      ·
        refine ⟨42433716626913574999420787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28289144417942383332947191 42433716626913574999420787)
        ·
          refine ⟨63650574940370362499131181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42433716626913574999420787 63650574940370362499131181)
          ·
            refine ⟨23868965602638885937174193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63650574940370362499131181 23868965602638885937174193)
            ·
              refine ⟨17901724201979164452880645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23868965602638885937174193 17901724201979164452880645)
              ·
                refine ⟨3356573287871093334915121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17901724201979164452880645 3356573287871093334915121)
                ·
                  refine ⟨2517429965903320001186341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3356573287871093334915121 2517429965903320001186341)
                  ·
                    refine ⟨472018118606872500222439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2517429965903320001186341 472018118606872500222439)
                    ·
                      rfl

theorem cell23_2757756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_2757756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757756 prefixEnd_2757756 := by exact prefixLift 2757756
  have htrace : WordTrace (prefixWord ++ tailWord_2757756) baseStart_2757756 baseEnd_2757756 := by
    simpa [prefixWord, tailWord_2757756, baseEnd_2757756] using wordTrace_append hprefix tailTrace_2757756
  have hstable : (prefixWord ++ tailWord_2757756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757756).length < 2 ^ (prefixWord ++ tailWord_2757756).sum := by decide
  have hdescent : baseEnd_2757756 < baseStart_2757756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757769 : List Nat := [1, 2, 1, 1, 4, 4, 2, 8]
def baseStart_2757769 : Nat := 118140960795 + 2757769 * 2 ^ 59
def prefixEnd_2757769 : Nat := 4983230072969 + 3 ^ 40 * 2757769 * 2
def baseEnd_2757769 : Nat := 52446704854412072214991

theorem tailTrace_2757769 : CollatzResearch.WordTrace tailWord_2757769 prefixEnd_2757769 52446704854412072214991 := by
  unfold tailWord_2757769
  simp only [CollatzResearch.WordTrace]
  refine ⟨100584098746081377292924361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67056065830720918195282907 100584098746081377292924361)
  ·
    refine ⟨75438074059561032969693271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100584098746081377292924361 75438074059561032969693271)
    ·
      refine ⟨113157111089341549454539907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75438074059561032969693271 113157111089341549454539907)
      ·
        refine ⟨169735666634012324181809861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113157111089341549454539907 169735666634012324181809861)
        ·
          refine ⟨31825437493877310784089349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169735666634012324181809861 31825437493877310784089349)
          ·
            refine ⟨5967269530101995772016753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31825437493877310784089349 5967269530101995772016753)
            ·
              refine ⟨4475452147576496829012565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5967269530101995772016753 4475452147576496829012565)
              ·
                refine ⟨52446704854412072214991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4475452147576496829012565 52446704854412072214991)
                ·
                  rfl

theorem cell23_2757769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 8].length) (baseStart_2757769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757769 prefixEnd_2757769 := by exact prefixLift 2757769
  have htrace : WordTrace (prefixWord ++ tailWord_2757769) baseStart_2757769 baseEnd_2757769 := by
    simpa [prefixWord, tailWord_2757769, baseEnd_2757769] using wordTrace_append hprefix tailTrace_2757769
  have hstable : (prefixWord ++ tailWord_2757769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757769).length < 2 ^ (prefixWord ++ tailWord_2757769).sum := by decide
  have hdescent : baseEnd_2757769 < baseStart_2757769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757783 : List Nat := [1, 1, 3, 3, 3, 1, 3, 2, 1, 2, 3]
def baseStart_2757783 : Nat := 118140960795 + 2757783 * 2 ^ 59
def prefixEnd_2757783 : Nat := 4983230072969 + 3 ^ 40 * 2757783 * 2
def baseEnd_2757783 : Nat := 1416068219798288895029693

theorem tailTrace_2757783 : CollatzResearch.WordTrace tailWord_2757783 prefixEnd_2757783 1416068219798288895029693 := by
  unfold tailWord_2757783
  simp only [CollatzResearch.WordTrace]
  refine ⟨100584609368030657683934003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67056406245353771789289335 100584609368030657683934003)
  ·
    refine ⟨150876914052045986525901005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100584609368030657683934003 150876914052045986525901005)
    ·
      refine ⟨56578842769517244947212877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150876914052045986525901005 56578842769517244947212877)
      ·
        refine ⟨21217066038568966855204829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56578842769517244947212877 21217066038568966855204829)
        ·
          refine ⟨7956399764463362570701811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21217066038568966855204829 7956399764463362570701811)
          ·
            refine ⟨11934599646695043856052717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7956399764463362570701811 11934599646695043856052717)
            ·
              refine ⟨4475474867510641446019769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11934599646695043856052717 4475474867510641446019769)
              ·
                refine ⟨3356606150632981084514827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4475474867510641446019769 3356606150632981084514827)
                ·
                  refine ⟨5034909225949471626772241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356606150632981084514827 5034909225949471626772241)
                  ·
                    refine ⟨3776181919462103720079181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5034909225949471626772241 3776181919462103720079181)
                    ·
                      refine ⟨1416068219798288895029693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3776181919462103720079181 1416068219798288895029693)
                      ·
                        rfl

theorem cell23_2757783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_2757783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757783 prefixEnd_2757783 := by exact prefixLift 2757783
  have htrace : WordTrace (prefixWord ++ tailWord_2757783) baseStart_2757783 baseEnd_2757783 := by
    simpa [prefixWord, tailWord_2757783, baseEnd_2757783] using wordTrace_append hprefix tailTrace_2757783
  have hstable : (prefixWord ++ tailWord_2757783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757783).length < 2 ^ (prefixWord ++ tailWord_2757783).sum := by decide
  have hdescent : baseEnd_2757783 < baseStart_2757783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757796 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 3, 3, 3]
def baseStart_2757796 : Nat := 118140960795 + 2757796 * 2 ^ 59
def prefixEnd_2757796 : Nat := 4983230072969 + 3 ^ 40 * 2757796 * 2
def baseEnd_2757796 : Nat := 1416074895046797344167133

theorem tailTrace_2757796 : CollatzResearch.WordTrace tailWord_2757796 prefixEnd_2757796 1416074895046797344167133 := by
  unfold tailWord_2757796
  simp only [CollatzResearch.WordTrace]
  refine ⟨50292541758491780452078621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67056722344655707269438161 50292541758491780452078621)
  ·
    refine ⟨18859703159434417669529483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50292541758491780452078621 18859703159434417669529483)
    ·
      refine ⟨28289554739151626504294225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18859703159434417669529483 28289554739151626504294225)
      ·
        refine ⟨21217166054363719878220669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28289554739151626504294225 21217166054363719878220669)
        ·
          refine ⟨7956437270386394954332751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21217166054363719878220669 7956437270386394954332751)
          ·
            refine ⟨11934655905579592431499127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7956437270386394954332751 11934655905579592431499127)
            ·
              refine ⟨17901983858369388647248691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11934655905579592431499127 17901983858369388647248691)
              ·
                refine ⟨26852975787554082970873037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17901983858369388647248691 26852975787554082970873037)
                ·
                  refine ⟨10069865920332781114077389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26852975787554082970873037 10069865920332781114077389)
                  ·
                    refine ⟨3776199720124792917779021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10069865920332781114077389 3776199720124792917779021)
                    ·
                      refine ⟨1416074895046797344167133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3776199720124792917779021 1416074895046797344167133)
                      ·
                        rfl

theorem cell23_2757796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_2757796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757796 prefixEnd_2757796 := by exact prefixLift 2757796
  have htrace : WordTrace (prefixWord ++ tailWord_2757796) baseStart_2757796 baseEnd_2757796 := by
    simpa [prefixWord, tailWord_2757796, baseEnd_2757796] using wordTrace_append hprefix tailTrace_2757796
  have hstable : (prefixWord ++ tailWord_2757796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757796).length < 2 ^ (prefixWord ++ tailWord_2757796).sum := by decide
  have hdescent : baseEnd_2757796 < baseStart_2757796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757839 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 5]
def baseStart_2757839 : Nat := 118140960795 + 2757839 * 2 ^ 59
def prefixEnd_2757839 : Nat := 4983230072969 + 3 ^ 40 * 2757839 * 2
def baseEnd_2757839 : Nat := 1416096974714940675929435

theorem tailTrace_2757839 : CollatzResearch.WordTrace tailWord_2757839 prefixEnd_2757839 1416096974714940675929435 := by
  unfold tailWord_2757839
  simp only [CollatzResearch.WordTrace]
  refine ⟨100586651855827779247972571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67057767903885186165315047 100586651855827779247972571)
  ·
    refine ⟨150879977783741668871958857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100586651855827779247972571 150879977783741668871958857)
    ·
      refine ⟨113159983337806251653969143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150879977783741668871958857 113159983337806251653969143)
      ·
        refine ⟨169739975006709377480953715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113159983337806251653969143 169739975006709377480953715)
        ·
          refine ⟨254609962510064066221430573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169739975006709377480953715 254609962510064066221430573)
          ·
            refine ⟨95478735941274024833036465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254609962510064066221430573 95478735941274024833036465)
            ·
              refine ⟨71609051955955518624777349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95478735941274024833036465 71609051955955518624777349)
              ·
                refine ⟨13426697241741659742145753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71609051955955518624777349 13426697241741659742145753)
                ·
                  refine ⟨10070022931306244806609315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13426697241741659742145753 10070022931306244806609315)
                  ·
                    refine ⟨15105034396959367209913973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10070022931306244806609315 15105034396959367209913973)
                    ·
                      refine ⟨1416096974714940675929435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15105034396959367209913973 1416096974714940675929435)
                      ·
                        rfl

theorem cell23_2757839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_2757839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757839 prefixEnd_2757839 := by exact prefixLift 2757839
  have htrace : WordTrace (prefixWord ++ tailWord_2757839) baseStart_2757839 baseEnd_2757839 := by
    simpa [prefixWord, tailWord_2757839, baseEnd_2757839] using wordTrace_append hprefix tailTrace_2757839
  have hstable : (prefixWord ++ tailWord_2757839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757839).length < 2 ^ (prefixWord ++ tailWord_2757839).sum := by decide
  have hdescent : baseEnd_2757839 < baseStart_2757839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757849 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 3, 4, 4]
def baseStart_2757849 : Nat := 118140960795 + 2757849 * 2 ^ 59
def prefixEnd_2757849 : Nat := 4983230072969 + 3 ^ 40 * 2757849 * 2
def baseEnd_2757849 : Nat := 1416102109521485636804389

theorem tailTrace_2757849 : CollatzResearch.WordTrace tailWord_2757849 prefixEnd_2757849 1416102109521485636804389 := by
  unfold tailWord_2757849
  simp only [CollatzResearch.WordTrace]
  refine ⟨100587016585791550955836601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67058011057194367303891067 100587016585791550955836601)
  ·
    refine ⟨75440262439343663216877451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100587016585791550955836601 75440262439343663216877451)
    ·
      refine ⟨113160393659015494825316177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75440262439343663216877451 113160393659015494825316177)
      ·
        refine ⟨84870295244261621118987133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113160393659015494825316177 84870295244261621118987133)
        ·
          refine ⟨31826360716598107919620175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84870295244261621118987133 31826360716598107919620175)
          ·
            refine ⟨47739541074897161879430263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31826360716598107919620175 47739541074897161879430263)
            ·
              refine ⟨71609311612345742819145395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47739541074897161879430263 71609311612345742819145395)
              ·
                refine ⟨107413967418518614228718093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71609311612345742819145395 107413967418518614228718093)
                ·
                  refine ⟨40280237781944480335769285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107413967418518614228718093 40280237781944480335769285)
                  ·
                    refine ⟨7552544584114590062956741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40280237781944480335769285 7552544584114590062956741)
                    ·
                      refine ⟨1416102109521485636804389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7552544584114590062956741 1416102109521485636804389)
                      ·
                        rfl

theorem cell23_2757849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_2757849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757849 prefixEnd_2757849 := by exact prefixLift 2757849
  have htrace : WordTrace (prefixWord ++ tailWord_2757849) baseStart_2757849 baseEnd_2757849 := by
    simpa [prefixWord, tailWord_2757849, baseEnd_2757849] using wordTrace_append hprefix tailTrace_2757849
  have hstable : (prefixWord ++ tailWord_2757849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757849).length < 2 ^ (prefixWord ++ tailWord_2757849).sum := by decide
  have hdescent : baseEnd_2757849 < baseStart_2757849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757857 : List Nat := [1, 2, 3, 1, 3, 4, 2, 1, 1, 3, 2]
def baseStart_2757857 : Nat := 118140960795 + 2757857 * 2 ^ 59
def prefixEnd_2757857 : Nat := 4983230072969 + 3 ^ 40 * 2757857 * 2
def baseEnd_2757857 : Nat := 1416106217366721605504353

theorem tailTrace_2757857 : CollatzResearch.WordTrace tailWord_2757857 prefixEnd_2757857 1416106217366721605504353 := by
  unfold tailWord_2757857
  simp only [CollatzResearch.WordTrace]
  refine ⟨100587308369762568322127825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67058205579841712214751883 100587308369762568322127825)
  ·
    refine ⟨75440481277321926241595869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100587308369762568322127825 75440481277321926241595869)
    ·
      refine ⟨28290180478995722340598451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75440481277321926241595869 28290180478995722340598451)
      ·
        refine ⟨42435270718493583510897677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28290180478995722340598451 42435270718493583510897677)
        ·
          refine ⟨15913226519435093816586629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42435270718493583510897677 15913226519435093816586629)
          ·
            refine ⟨2983729972394080090609993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15913226519435093816586629 2983729972394080090609993)
            ·
              refine ⟨2237797479295560067957495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2983729972394080090609993 2237797479295560067957495)
              ·
                refine ⟨3356696218943340101936243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237797479295560067957495 3356696218943340101936243)
                ·
                  refine ⟨5035044328415010152904365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356696218943340101936243 5035044328415010152904365)
                  ·
                    refine ⟨1888141623155628807339137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5035044328415010152904365 1888141623155628807339137)
                    ·
                      refine ⟨1416106217366721605504353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1888141623155628807339137 1416106217366721605504353)
                      ·
                        rfl

theorem cell23_2757857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_2757857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757857 prefixEnd_2757857 := by exact prefixLift 2757857
  have htrace : WordTrace (prefixWord ++ tailWord_2757857) baseStart_2757857 baseEnd_2757857 := by
    simpa [prefixWord, tailWord_2757857, baseEnd_2757857] using wordTrace_append hprefix tailTrace_2757857
  have hstable : (prefixWord ++ tailWord_2757857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757857).length < 2 ^ (prefixWord ++ tailWord_2757857).sum := by decide
  have hdescent : baseEnd_2757857 < baseStart_2757857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757866 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_2757866 : Nat := 118140960795 + 2757866 * 2 ^ 59
def prefixEnd_2757866 : Nat := 4983230072969 + 3 ^ 40 * 2757866 * 2
def baseEnd_2757866 : Nat := 1416110838692612070291811

theorem tailTrace_2757866 : CollatzResearch.WordTrace tailWord_2757866 prefixEnd_2757866 1416110838692612070291811 := by
  unfold tailWord_2757866
  simp only [CollatzResearch.WordTrace]
  refine ⟨25146909156682490714801363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67058424417819975239470301 25146909156682490714801363)
  ·
    refine ⟨37720363735023736072202045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25146909156682490714801363 37720363735023736072202045)
    ·
      refine ⟨14145136400633901027075767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37720363735023736072202045 14145136400633901027075767)
      ·
        refine ⟨21217704600950851540613651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14145136400633901027075767 21217704600950851540613651)
        ·
          refine ⟨31826556901426277310920477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21217704600950851540613651 31826556901426277310920477)
          ·
            refine ⟨11934958838034853991595179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31826556901426277310920477 11934958838034853991595179)
            ·
              refine ⟨17902438257052280987392769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11934958838034853991595179 17902438257052280987392769)
              ·
                refine ⟨13426828692789210740544577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17902438257052280987392769 13426828692789210740544577)
                ·
                  refine ⟨10070121519591908055408433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13426828692789210740544577 10070121519591908055408433)
                  ·
                    refine ⟨7552591139693931041556325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10070121519591908055408433 7552591139693931041556325)
                    ·
                      refine ⟨1416110838692612070291811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7552591139693931041556325 1416110838692612070291811)
                      ·
                        rfl

theorem cell23_2757866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_2757866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757866 prefixEnd_2757866 := by exact prefixLift 2757866
  have htrace : WordTrace (prefixWord ++ tailWord_2757866) baseStart_2757866 baseEnd_2757866 := by
    simpa [prefixWord, tailWord_2757866, baseEnd_2757866] using wordTrace_append hprefix tailTrace_2757866
  have hstable : (prefixWord ++ tailWord_2757866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757866).length < 2 ^ (prefixWord ++ tailWord_2757866).sum := by decide
  have hdescent : baseEnd_2757866 < baseStart_2757866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757887 : List Nat := [1, 1, 2, 2, 1, 6, 3, 1, 2, 2, 2]
def baseStart_2757887 : Nat := 118140960795 + 2757887 * 2 ^ 59
def prefixEnd_2757887 : Nat := 4983230072969 + 3 ^ 40 * 2757887 * 2
def baseEnd_2757887 : Nat := 1416121621786356488129215

theorem tailTrace_2757887 : CollatzResearch.WordTrace tailWord_2757887 prefixEnd_2757887 1416121621786356488129215 := by
  unfold tailWord_2757887
  simp only [CollatzResearch.WordTrace]
  refine ⟨100588402559653883445719915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67058935039769255630479943 100588402559653883445719915)
  ·
    refine ⟨150882603839480825168579873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100588402559653883445719915 150882603839480825168579873)
    ·
      refine ⟨113161952879610618876434905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150882603839480825168579873 113161952879610618876434905)
      ·
        refine ⟨84871464659707964157326179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113161952879610618876434905 84871464659707964157326179)
        ·
          refine ⟨127307196989561946235989269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84871464659707964157326179 127307196989561946235989269)
          ·
            refine ⟨5967524858885716229811997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 127307196989561946235989269 5967524858885716229811997)
            ·
              refine ⟨2237821822082143586179499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5967524858885716229811997 2237821822082143586179499)
              ·
                refine ⟨3356732733123215379269249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237821822082143586179499 3356732733123215379269249)
                ·
                  refine ⟨2517549549842411534451937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3356732733123215379269249 2517549549842411534451937)
                  ·
                    refine ⟨1888162162381808650838953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2517549549842411534451937 1888162162381808650838953)
                    ·
                      refine ⟨1416121621786356488129215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1888162162381808650838953 1416121621786356488129215)
                      ·
                        rfl

theorem cell23_2757887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 2, 2, 2].length) (baseStart_2757887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757887 prefixEnd_2757887 := by exact prefixLift 2757887
  have htrace : WordTrace (prefixWord ++ tailWord_2757887) baseStart_2757887 baseEnd_2757887 := by
    simpa [prefixWord, tailWord_2757887, baseEnd_2757887] using wordTrace_append hprefix tailTrace_2757887
  have hstable : (prefixWord ++ tailWord_2757887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757887).length < 2 ^ (prefixWord ++ tailWord_2757887).sum := by decide
  have hdescent : baseEnd_2757887 < baseStart_2757887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757933 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2757933 : Nat := 118140960795 + 2757933 * 2 ^ 59
def prefixEnd_2757933 : Nat := 4983230072969 + 3 ^ 40 * 2757933 * 2
def baseEnd_2757933 : Nat := 1416145241896463308154003

theorem tailTrace_2757933 : CollatzResearch.WordTrace tailWord_2757933 prefixEnd_2757933 1416145241896463308154003 := by
  unfold tailWord_2757933
  simp only [CollatzResearch.WordTrace]
  refine ⟨100590080317487233301894453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67060053544991488867929635 100590080317487233301894453)
  ·
    refine ⟨9430320029764428122052605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100590080317487233301894453 9430320029764428122052605)
    ·
      refine ⟨3536370011161660545769727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9430320029764428122052605 3536370011161660545769727)
      ·
        refine ⟨5304555016742490818654591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3536370011161660545769727 5304555016742490818654591)
        ·
          refine ⟨7956832525113736227981887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5304555016742490818654591 7956832525113736227981887)
          ·
            refine ⟨11935248787670604341972831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7956832525113736227981887 11935248787670604341972831)
            ·
              refine ⟨17902873181505906512959247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11935248787670604341972831 17902873181505906512959247)
              ·
                refine ⟨26854309772258859769438871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17902873181505906512959247 26854309772258859769438871)
                ·
                  refine ⟨40281464658388289654158307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26854309772258859769438871 40281464658388289654158307)
                  ·
                    refine ⟨60422196987582434481237461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40281464658388289654158307 60422196987582434481237461)
                    ·
                      refine ⟨1416145241896463308154003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60422196987582434481237461 1416145241896463308154003)
                      ·
                        rfl

theorem cell23_2757933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2757933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757933 prefixEnd_2757933 := by exact prefixLift 2757933
  have htrace : WordTrace (prefixWord ++ tailWord_2757933) baseStart_2757933 baseEnd_2757933 := by
    simpa [prefixWord, tailWord_2757933, baseEnd_2757933] using wordTrace_append hprefix tailTrace_2757933
  have hstable : (prefixWord ++ tailWord_2757933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757933).length < 2 ^ (prefixWord ++ tailWord_2757933).sum := by decide
  have hdescent : baseEnd_2757933 < baseStart_2757933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757970 : List Nat := [3, 2, 2, 1, 1, 1, 1, 7, 1, 4]
def baseStart_2757970 : Nat := 118140960795 + 2757970 * 2 ^ 59
def prefixEnd_2757970 : Nat := 4983230072969 + 3 ^ 40 * 2757970 * 2
def baseEnd_2757970 : Nat := 472054746893559887797111

theorem tailTrace_2757970 : CollatzResearch.WordTrace tailWord_2757970 prefixEnd_2757970 472054746893559887797111 := by
  unfold tailWord_2757970
  simp only [CollatzResearch.WordTrace]
  refine ⟨25147857454588297155247841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67060953212235459080660909 25147857454588297155247841)
  ·
    refine ⟨18860893090941222866435881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25147857454588297155247841 18860893090941222866435881)
    ·
      refine ⟨14145669818205917149826911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18860893090941222866435881 14145669818205917149826911)
      ·
        refine ⟨21218504727308875724740367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14145669818205917149826911 21218504727308875724740367)
        ·
          refine ⟨31827757090963313587110551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21218504727308875724740367 31827757090963313587110551)
          ·
            refine ⟨47741635636444970380665827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31827757090963313587110551 47741635636444970380665827)
            ·
              refine ⟨71612453454667455570998741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47741635636444970380665827 71612453454667455570998741)
              ·
                refine ⟨1678416877843768489945283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 71612453454667455570998741 1678416877843768489945283)
                ·
                  refine ⟨2517625316765652734917925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678416877843768489945283 2517625316765652734917925)
                  ·
                    refine ⟨472054746893559887797111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2517625316765652734917925 472054746893559887797111)
                    ·
                      rfl

theorem cell23_2757970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_2757970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757970 prefixEnd_2757970 := by exact prefixLift 2757970
  have htrace : WordTrace (prefixWord ++ tailWord_2757970) baseStart_2757970 baseEnd_2757970 := by
    simpa [prefixWord, tailWord_2757970, baseEnd_2757970] using wordTrace_append hprefix tailTrace_2757970
  have hstable : (prefixWord ++ tailWord_2757970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757970).length < 2 ^ (prefixWord ++ tailWord_2757970).sum := by decide
  have hdescent : baseEnd_2757970 < baseStart_2757970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757987 : List Nat := [1, 1, 1, 5, 2, 2, 4, 2, 1, 4]
def baseStart_2757987 : Nat := 118140960795 + 2757987 * 2 ^ 59
def prefixEnd_2757987 : Nat := 4983230072969 + 3 ^ 40 * 2757987 * 2
def baseEnd_2757987 : Nat := 472057656617268698959585

theorem tailTrace_2757987 : CollatzResearch.WordTrace tailWord_2757987 prefixEnd_2757987 472057656617268698959585 := by
  unfold tailWord_2757987
  simp only [CollatzResearch.WordTrace]
  refine ⟨100592049859291600524360215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67061366572861067016240143 100592049859291600524360215)
  ·
    refine ⟨150888074788937400786540323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100592049859291600524360215 150888074788937400786540323)
    ·
      refine ⟨226332112183406101179810485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150888074788937400786540323 226332112183406101179810485)
      ·
        refine ⟨21218635517194321985607233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226332112183406101179810485 21218635517194321985607233)
        ·
          refine ⟨15913976637895741489205425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21218635517194321985607233 15913976637895741489205425)
          ·
            refine ⟨11935482478421806116904069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15913976637895741489205425 11935482478421806116904069)
            ·
              refine ⟨2237902964704088646919513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11935482478421806116904069 2237902964704088646919513)
              ·
                refine ⟨1678427223528066485189635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2237902964704088646919513 1678427223528066485189635)
                ·
                  refine ⟨2517640835292099727784453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678427223528066485189635 2517640835292099727784453)
                  ·
                    refine ⟨472057656617268698959585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2517640835292099727784453 472057656617268698959585)
                    ·
                      rfl

theorem cell23_2757987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 1, 4].length) (baseStart_2757987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2757987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2757987 prefixEnd_2757987 := by exact prefixLift 2757987
  have htrace : WordTrace (prefixWord ++ tailWord_2757987) baseStart_2757987 baseEnd_2757987 := by
    simpa [prefixWord, tailWord_2757987, baseEnd_2757987] using wordTrace_append hprefix tailTrace_2757987
  have hstable : (prefixWord ++ tailWord_2757987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757987).length < 2 ^ (prefixWord ++ tailWord_2757987).sum := by decide
  have hdescent : baseEnd_2757987 < baseStart_2757987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758013 : List Nat := [1, 4, 1, 1, 2, 2, 2, 4, 1, 5]
def baseStart_2758013 : Nat := 118140960795 + 2758013 * 2 ^ 59
def prefixEnd_2758013 : Nat := 4983230072969 + 3 ^ 40 * 2758013 * 2
def baseEnd_2758013 : Nat := 472062106782940998384545

theorem tailTrace_2758013 : CollatzResearch.WordTrace tailWord_2758013 prefixEnd_2758013 472062106782940998384545 := by
  unfold tailWord_2758013
  simp only [CollatzResearch.WordTrace]
  refine ⟨100592998157197406964806693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67061998771464937976537795 100592998157197406964806693)
  ·
    refine ⟨18861187154474513805901255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100592998157197406964806693 18861187154474513805901255)
    ·
      refine ⟨28291780731711770708851883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18861187154474513805901255 28291780731711770708851883)
      ·
        refine ⟨42437671097567656063277825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28291780731711770708851883 42437671097567656063277825)
        ·
          refine ⟨31828253323175742047458369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42437671097567656063277825 31828253323175742047458369)
          ·
            refine ⟨23871189992381806535593777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31828253323175742047458369 23871189992381806535593777)
            ·
              refine ⟨17903392494286354901695333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23871189992381806535593777 17903392494286354901695333)
              ·
                refine ⟨3356886092678691544067875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17903392494286354901695333 3356886092678691544067875)
                ·
                  refine ⟨5035329139018037316101813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356886092678691544067875 5035329139018037316101813)
                  ·
                    refine ⟨472062106782940998384545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5035329139018037316101813 472062106782940998384545)
                    ·
                      rfl

theorem cell23_2758013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_2758013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758013 prefixEnd_2758013 := by exact prefixLift 2758013
  have htrace : WordTrace (prefixWord ++ tailWord_2758013) baseStart_2758013 baseEnd_2758013 := by
    simpa [prefixWord, tailWord_2758013, baseEnd_2758013] using wordTrace_append hprefix tailTrace_2758013
  have hstable : (prefixWord ++ tailWord_2758013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758013).length < 2 ^ (prefixWord ++ tailWord_2758013).sum := by decide
  have hdescent : baseEnd_2758013 < baseStart_2758013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758020 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 1, 5, 2]
def baseStart_2758020 : Nat := 118140960795 + 2758020 * 2 ^ 59
def prefixEnd_2758020 : Nat := 4983230072969 + 3 ^ 40 * 2758020 * 2
def baseEnd_2758020 : Nat := 1416189914713404467766103

theorem tailTrace_2758020 : CollatzResearch.WordTrace tailWord_2758020 prefixEnd_2758020 1416189914713404467766103 := by
  unfold tailWord_2758020
  simp only [CollatzResearch.WordTrace]
  refine ⟨50296626734086023580155757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67062168978781364773541009 50296626734086023580155757)
  ·
    refine ⟨18861235025282258842558409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50296626734086023580155757 18861235025282258842558409)
    ·
      refine ⟨14145926268961694131918807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18861235025282258842558409 14145926268961694131918807)
      ·
        refine ⟨21218889403442541197878211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14145926268961694131918807 21218889403442541197878211)
        ·
          refine ⟨31828334105163811796817317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21218889403442541197878211 31828334105163811796817317)
          ·
            refine ⟨5967812644718214711903247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31828334105163811796817317 5967812644718214711903247)
            ·
              refine ⟨8951718967077322067854871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5967812644718214711903247 8951718967077322067854871)
              ·
                refine ⟨13427578450615983101782307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8951718967077322067854871 13427578450615983101782307)
                ·
                  refine ⟨20141367675923974652673461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13427578450615983101782307 20141367675923974652673461)
                  ·
                    refine ⟨1888253219617872623688137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20141367675923974652673461 1888253219617872623688137)
                    ·
                      refine ⟨1416189914713404467766103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1888253219617872623688137 1416189914713404467766103)
                      ·
                        rfl

theorem cell23_2758020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_2758020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758020 prefixEnd_2758020 := by exact prefixLift 2758020
  have htrace : WordTrace (prefixWord ++ tailWord_2758020) baseStart_2758020 baseEnd_2758020 := by
    simpa [prefixWord, tailWord_2758020, baseEnd_2758020] using wordTrace_append hprefix tailTrace_2758020
  have hstable : (prefixWord ++ tailWord_2758020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758020).length < 2 ^ (prefixWord ++ tailWord_2758020).sum := by decide
  have hdescent : baseEnd_2758020 < baseStart_2758020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758027 : List Nat := [1, 1, 1, 1, 4, 3, 4, 3, 1, 1, 3]
def baseStart_2758027 : Nat := 118140960795 + 2758027 * 2 ^ 59
def prefixEnd_2758027 : Nat := 4983230072969 + 3 ^ 40 * 2758027 * 2
def baseEnd_2758027 : Nat := 1416193509077985940378571

theorem tailTrace_2758027 : CollatzResearch.WordTrace tailWord_2758027 prefixEnd_2758027 1416193509077985940378571 := by
  unfold tailWord_2758027
  simp only [CollatzResearch.WordTrace]
  refine ⟨100593508779146687355816335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67062339186097791570544223 100593508779146687355816335)
  ·
    refine ⟨150890263168720031033724503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100593508779146687355816335 150890263168720031033724503)
    ·
      refine ⟨226335394753080046550586755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150890263168720031033724503 226335394753080046550586755)
      ·
        refine ⟨339503092129620069825880133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226335394753080046550586755 339503092129620069825880133)
        ·
          refine ⟨63656829774303763092352525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 339503092129620069825880133 63656829774303763092352525)
          ·
            refine ⟨23871311165363911159632197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63656829774303763092352525 23871311165363911159632197)
            ·
              refine ⟨4475870843505733342431037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23871311165363911159632197 4475870843505733342431037)
              ·
                refine ⟨1678451566314650003411639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4475870843505733342431037 1678451566314650003411639)
                ·
                  refine ⟨2517677349471975005117459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678451566314650003411639 2517677349471975005117459)
                  ·
                    refine ⟨3776516024207962507676189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2517677349471975005117459 3776516024207962507676189)
                    ·
                      refine ⟨1416193509077985940378571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3776516024207962507676189 1416193509077985940378571)
                      ·
                        rfl

theorem cell23_2758027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 1, 1, 3].length) (baseStart_2758027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758027 prefixEnd_2758027 := by exact prefixLift 2758027
  have htrace : WordTrace (prefixWord ++ tailWord_2758027) baseStart_2758027 baseEnd_2758027 := by
    simpa [prefixWord, tailWord_2758027, baseEnd_2758027] using wordTrace_append hprefix tailTrace_2758027
  have hstable : (prefixWord ++ tailWord_2758027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758027).length < 2 ^ (prefixWord ++ tailWord_2758027).sum := by decide
  have hdescent : baseEnd_2758027 < baseStart_2758027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758033 : List Nat := [1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 4]
def baseStart_2758033 : Nat := 118140960795 + 2758033 * 2 ^ 59
def prefixEnd_2758033 : Nat := 4983230072969 + 3 ^ 40 * 2758033 * 2
def baseEnd_2758033 : Nat := 1416196589961912916903543

theorem tailTrace_2758033 : CollatzResearch.WordTrace tailWord_2758033 prefixEnd_2758033 1416196589961912916903543 := by
  unfold tailWord_2758033
  simp only [CollatzResearch.WordTrace]
  refine ⟨100593727617124950380534753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67062485078083300253689835 100593727617124950380534753)
  ·
    refine ⟨75445295712843712785401065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100593727617124950380534753 75445295712843712785401065)
    ·
      refine ⟨56583971784632784589050799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75445295712843712785401065 56583971784632784589050799)
      ·
        refine ⟨84875957676949176883576199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56583971784632784589050799 84875957676949176883576199)
        ·
          refine ⟨127313936515423765325364299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84875957676949176883576199 127313936515423765325364299)
          ·
            refine ⟨190970904773135647988046449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127313936515423765325364299 190970904773135647988046449)
            ·
              refine ⟨143228178579851735991034837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190970904773135647988046449 143228178579851735991034837)
              ·
                refine ⟨3356910435465275062289879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 143228178579851735991034837 3356910435465275062289879)
                ·
                  refine ⟨5035365653197912593434819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356910435465275062289879 5035365653197912593434819)
                  ·
                    refine ⟨7553048479796868890152229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5035365653197912593434819 7553048479796868890152229)
                    ·
                      refine ⟨1416196589961912916903543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7553048479796868890152229 1416196589961912916903543)
                      ·
                        rfl

theorem cell23_2758033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_2758033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758033 prefixEnd_2758033 := by exact prefixLift 2758033
  have htrace : WordTrace (prefixWord ++ tailWord_2758033) baseStart_2758033 baseEnd_2758033 := by
    simpa [prefixWord, tailWord_2758033, baseEnd_2758033] using wordTrace_append hprefix tailTrace_2758033
  have hstable : (prefixWord ++ tailWord_2758033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758033).length < 2 ^ (prefixWord ++ tailWord_2758033).sum := by decide
  have hdescent : baseEnd_2758033 < baseStart_2758033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758034 : List Nat := [3, 2, 3, 3, 2, 1, 1, 2, 6]
def baseStart_2758034 : Nat := 118140960795 + 2758034 * 2 ^ 59
def prefixEnd_2758034 : Nat := 4983230072969 + 3 ^ 40 * 2758034 * 2
def baseEnd_2758034 : Nat := 157355233715840823665671

theorem tailTrace_2758034 : CollatzResearch.WordTrace tailWord_2758034 prefixEnd_2758034 157355233715840823665671 := by
  unfold tailWord_2758034
  simp only [CollatzResearch.WordTrace]
  refine ⟨25148441022530331887830289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67062509393414218367547437 25148441022530331887830289)
  ·
    refine ⟨18861330766897748915872717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25148441022530331887830289 18861330766897748915872717)
    ·
      refine ⟨7072999037586655843452269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18861330766897748915872717 7072999037586655843452269)
      ·
        refine ⟨2652374639094995941294601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7072999037586655843452269 2652374639094995941294601)
        ·
          refine ⟨1989280979321246955970951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2652374639094995941294601 1989280979321246955970951)
          ·
            refine ⟨2983921468981870433956427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1989280979321246955970951 2983921468981870433956427)
            ·
              refine ⟨4475882203472805650934641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2983921468981870433956427 4475882203472805650934641)
              ·
                refine ⟨3356911652604604238200981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4475882203472805650934641 3356911652604604238200981)
                ·
                  refine ⟨157355233715840823665671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3356911652604604238200981 157355233715840823665671)
                  ·
                    rfl

theorem cell23_2758034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_2758034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758034 prefixEnd_2758034 := by exact prefixLift 2758034
  have htrace : WordTrace (prefixWord ++ tailWord_2758034) baseStart_2758034 baseEnd_2758034 := by
    simpa [prefixWord, tailWord_2758034, baseEnd_2758034] using wordTrace_append hprefix tailTrace_2758034
  have hstable : (prefixWord ++ tailWord_2758034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758034).length < 2 ^ (prefixWord ++ tailWord_2758034).sum := by decide
  have hdescent : baseEnd_2758034 < baseStart_2758034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758044 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2758044 : Nat := 118140960795 + 2758044 * 2 ^ 59
def prefixEnd_2758044 : Nat := 4983230072969 + 3 ^ 40 * 2758044 * 2
def baseEnd_2758044 : Nat := 1416202238249112373865993

theorem tailTrace_2758044 : CollatzResearch.WordTrace tailWord_2758044 prefixEnd_2758044 1416202238249112373865993 := by
  unfold tailWord_2758044
  simp only [CollatzResearch.WordTrace]
  refine ⟨50297064410042549629592593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67062752546723399506123457 50297064410042549629592593)
  ·
    refine ⟨37722798307531912222194445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50297064410042549629592593 37722798307531912222194445)
    ·
      refine ⟨14146049365324467083322917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37722798307531912222194445 14146049365324467083322917)
      ·
        refine ⟨2652384255998337578123047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14146049365324467083322917 2652384255998337578123047)
        ·
          refine ⟨3978576383997506367184571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2652384255998337578123047 3978576383997506367184571)
          ·
            refine ⟨5967864575996259550776857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3978576383997506367184571 5967864575996259550776857)
            ·
              refine ⟨4475898431997194663082643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5967864575996259550776857 4475898431997194663082643)
              ·
                refine ⟨6713847647995791994623965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4475898431997194663082643 6713847647995791994623965)
                ·
                  refine ⟨2517692867998421997983987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6713847647995791994623965 2517692867998421997983987)
                  ·
                    refine ⟨3776539301997632996975981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2517692867998421997983987 3776539301997632996975981)
                    ·
                      refine ⟨1416202238249112373865993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3776539301997632996975981 1416202238249112373865993)
                      ·
                        rfl

theorem cell23_2758044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2758044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758044 prefixEnd_2758044 := by exact prefixLift 2758044
  have htrace : WordTrace (prefixWord ++ tailWord_2758044) baseStart_2758044 baseEnd_2758044 := by
    simpa [prefixWord, tailWord_2758044, baseEnd_2758044] using wordTrace_append hprefix tailTrace_2758044
  have hstable : (prefixWord ++ tailWord_2758044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758044).length < 2 ^ (prefixWord ++ tailWord_2758044).sum := by decide
  have hdescent : baseEnd_2758044 < baseStart_2758044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758053 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 3, 2, 3]
def baseStart_2758053 : Nat := 118140960795 + 2758053 * 2 ^ 59
def prefixEnd_2758053 : Nat := 4983230072969 + 3 ^ 40 * 2758053 * 2
def baseEnd_2758053 : Nat := 1416206859575002838653451

theorem tailTrace_2758053 : CollatzResearch.WordTrace tailWord_2758053 prefixEnd_2758053 1416206859575002838653451 := by
  unfold tailWord_2758053
  simp only [CollatzResearch.WordTrace]
  refine ⟨100594457077052493796262813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67062971384701662530841875 100594457077052493796262813)
  ·
    refine ⟨37722921403894685173598555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100594457077052493796262813 37722921403894685173598555)
    ·
      refine ⟨56584382105842027760397833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37722921403894685173598555 56584382105842027760397833)
      ·
        refine ⟨42438286579381520820298375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56584382105842027760397833 42438286579381520820298375)
        ·
          refine ⟨63657429869072281230447563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42438286579381520820298375 63657429869072281230447563)
          ·
            refine ⟨95486144803608421845671345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63657429869072281230447563 95486144803608421845671345)
            ·
              refine ⟨71614608602706316384253509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95486144803608421845671345 71614608602706316384253509)
              ·
                refine ⟨13427739113007434322047533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71614608602706316384253509 13427739113007434322047533)
                ·
                  refine ⟨5035402167377787870767825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13427739113007434322047533 5035402167377787870767825)
                  ·
                    refine ⟨3776551625533340903075869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5035402167377787870767825 3776551625533340903075869)
                    ·
                      refine ⟨1416206859575002838653451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3776551625533340903075869 1416206859575002838653451)
                      ·
                        rfl

theorem cell23_2758053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_2758053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758053 prefixEnd_2758053 := by exact prefixLift 2758053
  have htrace : WordTrace (prefixWord ++ tailWord_2758053) baseStart_2758053 baseEnd_2758053 := by
    simpa [prefixWord, tailWord_2758053, baseEnd_2758053] using wordTrace_append hprefix tailTrace_2758053
  have hstable : (prefixWord ++ tailWord_2758053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758053).length < 2 ^ (prefixWord ++ tailWord_2758053).sum := by decide
  have hdescent : baseEnd_2758053 < baseStart_2758053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758073 : List Nat := [1, 2, 1, 4, 4, 1, 1, 9]
def baseStart_2758073 : Nat := 118140960795 + 2758073 * 2 ^ 59
def prefixEnd_2758073 : Nat := 4983230072969 + 3 ^ 40 * 2758073 * 2
def baseEnd_2758073 : Nat := 52452486266225657792717

theorem tailTrace_2758073 : CollatzResearch.WordTrace tailWord_2758073 prefixEnd_2758073 52452486266225657792717 := by
  unfold tailWord_2758073
  simp only [CollatzResearch.WordTrace]
  refine ⟨100595186536980037211990873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67063457691320024807993915 100595186536980037211990873)
  ·
    refine ⟨75446389902735027908993155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100595186536980037211990873 75446389902735027908993155)
    ·
      refine ⟨113169584854102541863489733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75446389902735027908993155 113169584854102541863489733)
      ·
        refine ⟨21219297160144226599404325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113169584854102541863489733 21219297160144226599404325)
        ·
          refine ⟨3978618217527042487388311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21219297160144226599404325 3978618217527042487388311)
          ·
            refine ⟨5967927326290563731082467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3978618217527042487388311 5967927326290563731082467)
            ·
              refine ⟨8951890989435845596623701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5967927326290563731082467 8951890989435845596623701)
              ·
                refine ⟨52452486266225657792717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8951890989435845596623701 52452486266225657792717)
                ·
                  rfl

theorem cell23_2758073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 9].length) (baseStart_2758073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758073 prefixEnd_2758073 := by exact prefixLift 2758073
  have htrace : WordTrace (prefixWord ++ tailWord_2758073) baseStart_2758073 baseEnd_2758073 := by
    simpa [prefixWord, tailWord_2758073, baseEnd_2758073] using wordTrace_append hprefix tailTrace_2758073
  have hstable : (prefixWord ++ tailWord_2758073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758073).length < 2 ^ (prefixWord ++ tailWord_2758073).sum := by decide
  have hdescent : baseEnd_2758073 < baseStart_2758073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758083 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 3]
def baseStart_2758083 : Nat := 118140960795 + 2758083 * 2 ^ 59
def prefixEnd_2758083 : Nat := 4983230072969 + 3 ^ 40 * 2758083 * 2
def baseEnd_2758083 : Nat := 1416222263994637721278313

theorem tailTrace_2758083 : CollatzResearch.WordTrace tailWord_2758083 prefixEnd_2758083 1416222263994637721278313 := by
  unfold tailWord_2758083
  simp only [CollatzResearch.WordTrace]
  refine ⟨100595551266943808919854903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67063700844629205946569935 100595551266943808919854903)
  ·
    refine ⟨150893326900415713379782355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100595551266943808919854903 150893326900415713379782355)
    ·
      refine ⟨226339990350623570069673533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150893326900415713379782355 226339990350623570069673533)
      ·
        refine ⟨84877496381483838776127575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226339990350623570069673533 84877496381483838776127575)
        ·
          refine ⟨127316244572225758164191363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84877496381483838776127575 127316244572225758164191363)
          ·
            refine ⟨190974366858338637246287045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127316244572225758164191363 190974366858338637246287045)
            ·
              refine ⟨35807693785938494483678821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190974366858338637246287045 35807693785938494483678821)
              ·
                refine ⟨6713942584863467715689779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35807693785938494483678821 6713942584863467715689779)
                ·
                  refine ⟨10070913877295201573534669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6713942584863467715689779 10070913877295201573534669)
                  ·
                    refine ⟨3776592703985700590075501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10070913877295201573534669 3776592703985700590075501)
                    ·
                      refine ⟨1416222263994637721278313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3776592703985700590075501 1416222263994637721278313)
                      ·
                        rfl

theorem cell23_2758083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_2758083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758083 prefixEnd_2758083 := by exact prefixLift 2758083
  have htrace : WordTrace (prefixWord ++ tailWord_2758083) baseStart_2758083 baseEnd_2758083 := by
    simpa [prefixWord, tailWord_2758083, baseEnd_2758083] using wordTrace_append hprefix tailTrace_2758083
  have hstable : (prefixWord ++ tailWord_2758083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758083).length < 2 ^ (prefixWord ++ tailWord_2758083).sum := by decide
  have hdescent : baseEnd_2758083 < baseStart_2758083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758101 : List Nat := [1, 3, 2, 3, 1, 1, 5, 2, 1, 2, 2]
def baseStart_2758101 : Nat := 118140960795 + 2758101 * 2 ^ 59
def prefixEnd_2758101 : Nat := 4983230072969 + 3 ^ 40 * 2758101 * 2
def baseEnd_2758101 : Nat := 1416231506646418650853231

theorem tailTrace_2758101 : CollatzResearch.WordTrace tailWord_2758101 prefixEnd_2758101 1416231506646418650853231 := by
  unfold tailWord_2758101
  simp only [CollatzResearch.WordTrace]
  refine ⟨100596207780878597994010157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67064138520585731996006771 100596207780878597994010157)
  ·
    refine ⟨37723577917829474247753809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100596207780878597994010157 37723577917829474247753809)
    ·
      refine ⟨28292683438372105685815357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37723577917829474247753809 28292683438372105685815357)
      ·
        refine ⟨10609756289389539632180759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28292683438372105685815357 10609756289389539632180759)
        ·
          refine ⟨15914634434084309448271139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10609756289389539632180759 15914634434084309448271139)
          ·
            refine ⟨23871951651126464172406709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15914634434084309448271139 23871951651126464172406709)
            ·
              refine ⟨2237995467293106016163129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23871951651126464172406709 2237995467293106016163129)
              ·
                refine ⟨1678496600469829512122347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2237995467293106016163129 1678496600469829512122347)
                ·
                  refine ⟨2517744900704744268183521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678496600469829512122347 2517744900704744268183521)
                  ·
                    refine ⟨1888308675528558201137641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2517744900704744268183521 1888308675528558201137641)
                    ·
                      refine ⟨1416231506646418650853231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1888308675528558201137641 1416231506646418650853231)
                      ·
                        rfl

theorem cell23_2758101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_2758101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758101 prefixEnd_2758101 := by exact prefixLift 2758101
  have htrace : WordTrace (prefixWord ++ tailWord_2758101) baseStart_2758101 baseEnd_2758101 := by
    simpa [prefixWord, tailWord_2758101, baseEnd_2758101] using wordTrace_append hprefix tailTrace_2758101
  have hstable : (prefixWord ++ tailWord_2758101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758101).length < 2 ^ (prefixWord ++ tailWord_2758101).sum := by decide
  have hdescent : baseEnd_2758101 < baseStart_2758101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758127 : List Nat := [1, 1, 2, 1, 4, 1, 5, 2, 1, 3, 2]
def baseStart_2758127 : Nat := 118140960795 + 2758127 * 2 ^ 59
def prefixEnd_2758127 : Nat := 4983230072969 + 3 ^ 40 * 2758127 * 2
def baseEnd_2758127 : Nat := 1416244857143435549128111

theorem tailTrace_2758127 : CollatzResearch.WordTrace tailWord_2758127 prefixEnd_2758127 1416244857143435549128111 := by
  unfold tailWord_2758127
  simp only [CollatzResearch.WordTrace]
  refine ⟨100597156078784404434456635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67064770719189602956304423 100597156078784404434456635)
  ·
    refine ⟨150895734118176606651684953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100597156078784404434456635 150895734118176606651684953)
    ·
      refine ⟨113171800588632454988763715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150895734118176606651684953 113171800588632454988763715)
      ·
        refine ⟨169757700882948682483145573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113171800588632454988763715 169757700882948682483145573)
        ·
          refine ⟨31829568915552877965589795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169757700882948682483145573 31829568915552877965589795)
          ·
            refine ⟨47744353373329316948384693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31829568915552877965589795 47744353373329316948384693)
            ·
              refine ⟨4476033128749623463911065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47744353373329316948384693 4476033128749623463911065)
              ·
                refine ⟨3357024846562217597933299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4476033128749623463911065 3357024846562217597933299)
                ·
                  refine ⟨5035537269843326396899949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3357024846562217597933299 5035537269843326396899949)
                  ·
                    refine ⟨1888326476191247398837481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5035537269843326396899949 1888326476191247398837481)
                    ·
                      refine ⟨1416244857143435549128111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1888326476191247398837481 1416244857143435549128111)
                      ·
                        rfl

theorem cell23_2758127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 3, 2].length) (baseStart_2758127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758127 prefixEnd_2758127 := by exact prefixLift 2758127
  have htrace : WordTrace (prefixWord ++ tailWord_2758127) baseStart_2758127 baseEnd_2758127 := by
    simpa [prefixWord, tailWord_2758127, baseEnd_2758127] using wordTrace_append hprefix tailTrace_2758127
  have hstable : (prefixWord ++ tailWord_2758127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758127).length < 2 ^ (prefixWord ++ tailWord_2758127).sum := by decide
  have hdescent : baseEnd_2758127 < baseStart_2758127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758140 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 3, 4, 2]
def baseStart_2758140 : Nat := 118140960795 + 2758140 * 2 ^ 59
def prefixEnd_2758140 : Nat := 4983230072969 + 3 ^ 40 * 2758140 * 2
def baseEnd_2758140 : Nat := 1416251532391943998265551

theorem tailTrace_2758140 : CollatzResearch.WordTrace tailWord_2758140 prefixEnd_2758140 1416251532391943998265551 := by
  unfold tailWord_2758140
  simp only [CollatzResearch.WordTrace]
  refine ⟨50298815113868653827339937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67065086818491538436453249 50298815113868653827339937)
  ·
    refine ⟨37724111335401490370504953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50298815113868653827339937 37724111335401490370504953)
    ·
      refine ⟨28293083501551117777878715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37724111335401490370504953 28293083501551117777878715)
      ·
        refine ⟨42439625252326676666818073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28293083501551117777878715 42439625252326676666818073)
        ·
          refine ⟨31829718939245007500113555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42439625252326676666818073 31829718939245007500113555)
          ·
            refine ⟨47744578408867511250170333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31829718939245007500113555 47744578408867511250170333)
            ·
              refine ⟨17904216903325316718813875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47744578408867511250170333 17904216903325316718813875)
              ·
                refine ⟨26856325354987975078220813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17904216903325316718813875 26856325354987975078220813)
                ·
                  refine ⟨10071122008120490654332805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26856325354987975078220813 10071122008120490654332805)
                  ·
                    refine ⟨1888335376522591997687401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10071122008120490654332805 1888335376522591997687401)
                    ·
                      refine ⟨1416251532391943998265551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1888335376522591997687401 1416251532391943998265551)
                      ·
                        rfl

theorem cell23_2758140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_2758140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758140 prefixEnd_2758140 := by exact prefixLift 2758140
  have htrace : WordTrace (prefixWord ++ tailWord_2758140) baseStart_2758140 baseEnd_2758140 := by
    simpa [prefixWord, tailWord_2758140, baseEnd_2758140] using wordTrace_append hprefix tailTrace_2758140
  have hstable : (prefixWord ++ tailWord_2758140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758140).length < 2 ^ (prefixWord ++ tailWord_2758140).sum := by decide
  have hdescent : baseEnd_2758140 < baseStart_2758140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758153 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 2, 2, 4]
def baseStart_2758153 : Nat := 118140960795 + 2758153 * 2 ^ 59
def prefixEnd_2758153 : Nat := 4983230072969 + 3 ^ 40 * 2758153 * 2
def baseEnd_2758153 : Nat := 1416258207640452447402991

theorem tailTrace_2758153 : CollatzResearch.WordTrace tailWord_2758153 prefixEnd_2758153 1416258207640452447402991 := by
  unfold tailWord_2758153
  simp only [CollatzResearch.WordTrace]
  refine ⟨100598104376690210874903113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67065402917793473916602075 100598104376690210874903113)
  ·
    refine ⟨75448578282517658156177335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100598104376690210874903113 75448578282517658156177335)
    ·
      refine ⟨113172867423776487234266003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75448578282517658156177335 113172867423776487234266003)
      ·
        refine ⟨169759301135664730851399005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113172867423776487234266003 169759301135664730851399005)
        ·
          refine ⟨63659737925874274069274627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169759301135664730851399005 63659737925874274069274627)
          ·
            refine ⟨95489606888811411103911941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63659737925874274069274627 95489606888811411103911941)
            ·
              refine ⟨17904301291652139581983489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95489606888811411103911941 17904301291652139581983489)
              ·
                refine ⟨13428225968739104686487617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17904301291652139581983489 13428225968739104686487617)
                ·
                  refine ⟨10071169476554328514865713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13428225968739104686487617 10071169476554328514865713)
                  ·
                    refine ⟨7553377107415746386149285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10071169476554328514865713 7553377107415746386149285)
                    ·
                      refine ⟨1416258207640452447402991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7553377107415746386149285 1416258207640452447402991)
                      ·
                        rfl

theorem cell23_2758153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_2758153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758153 prefixEnd_2758153 := by exact prefixLift 2758153
  have htrace : WordTrace (prefixWord ++ tailWord_2758153) baseStart_2758153 baseEnd_2758153 := by
    simpa [prefixWord, tailWord_2758153, baseEnd_2758153] using wordTrace_append hprefix tailTrace_2758153
  have hstable : (prefixWord ++ tailWord_2758153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758153).length < 2 ^ (prefixWord ++ tailWord_2758153).sum := by decide
  have hdescent : baseEnd_2758153 < baseStart_2758153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758197 : List Nat := [1, 3, 3, 1, 1, 4, 2, 3, 5]
def baseStart_2758197 : Nat := 118140960795 + 2758197 * 2 ^ 59
def prefixEnd_2758197 : Nat := 4983230072969 + 3 ^ 40 * 2758197 * 2
def baseEnd_2758197 : Nat := 157364533421027808361421

theorem tailTrace_2758197 : CollatzResearch.WordTrace tailWord_2758197 prefixEnd_2758197 157364533421027808361421 := by
  unfold tailWord_2758197
  simp only [CollatzResearch.WordTrace]
  refine ⟨100599709188530806389504845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67066472792353870926336563 100599709188530806389504845)
  ·
    refine ⟨37724890945699052396064317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100599709188530806389504845 37724890945699052396064317)
    ·
      refine ⟨14146834104637144648524119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37724890945699052396064317 14146834104637144648524119)
      ·
        refine ⟨21220251156955716972786179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14146834104637144648524119 21220251156955716972786179)
        ·
          refine ⟨31830376735433575459179269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21220251156955716972786179 31830376735433575459179269)
          ·
            refine ⟨5968195637893795398596113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31830376735433575459179269 5968195637893795398596113)
            ·
              refine ⟨4476146728420346548947085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5968195637893795398596113 4476146728420346548947085)
              ·
                refine ⟨1678555023157629955855157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4476146728420346548947085 1678555023157629955855157)
                ·
                  refine ⟨157364533421027808361421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1678555023157629955855157 157364533421027808361421)
                  ·
                    rfl

theorem cell23_2758197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 5].length) (baseStart_2758197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758197 prefixEnd_2758197 := by exact prefixLift 2758197
  have htrace : WordTrace (prefixWord ++ tailWord_2758197) baseStart_2758197 baseEnd_2758197 := by
    simpa [prefixWord, tailWord_2758197, baseEnd_2758197] using wordTrace_append hprefix tailTrace_2758197
  have hstable : (prefixWord ++ tailWord_2758197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758197).length < 2 ^ (prefixWord ++ tailWord_2758197).sum := by decide
  have hdescent : baseEnd_2758197 < baseStart_2758197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758214 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_2758214 : Nat := 118140960795 + 2758214 * 2 ^ 59
def prefixEnd_2758214 : Nat := 4983230072969 + 3 ^ 40 * 2758214 * 2
def baseEnd_2758214 : Nat := 157365503328930745415579

theorem tailTrace_2758214 : CollatzResearch.WordTrace tailWord_2758214 prefixEnd_2758214 157365503328930745415579 := by
  unfold tailWord_2758214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3143760288420913071652303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67066886152979478861915797 3143760288420913071652303)
  ·
    refine ⟨4715640432631369607478455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3143760288420913071652303 4715640432631369607478455)
    ·
      refine ⟨7073460648947054411217683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4715640432631369607478455 7073460648947054411217683)
      ·
        refine ⟨10610190973420581616826525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7073460648947054411217683 10610190973420581616826525)
        ·
          refine ⟨3978821615032718106309947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10610190973420581616826525 3978821615032718106309947)
          ·
            refine ⟨5968232422549077159464921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3978821615032718106309947 5968232422549077159464921)
            ·
              refine ⟨4476174316911807869598691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5968232422549077159464921 4476174316911807869598691)
              ·
                refine ⟨6714261475367711804398037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4476174316911807869598691 6714261475367711804398037)
                ·
                  refine ⟨157365503328930745415579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6714261475367711804398037 157365503328930745415579)
                  ·
                    rfl

theorem cell23_2758214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_2758214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758214 prefixEnd_2758214 := by exact prefixLift 2758214
  have htrace : WordTrace (prefixWord ++ tailWord_2758214) baseStart_2758214 baseEnd_2758214 := by
    simpa [prefixWord, tailWord_2758214, baseEnd_2758214] using wordTrace_append hprefix tailTrace_2758214
  have hstable : (prefixWord ++ tailWord_2758214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758214).length < 2 ^ (prefixWord ++ tailWord_2758214).sum := by decide
  have hdescent : baseEnd_2758214 < baseStart_2758214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758313 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 2, 10]
def baseStart_2758313 : Nat := 118140960795 + 2758313 * 2 ^ 59
def prefixEnd_2758313 : Nat := 4983230072969 + 3 ^ 40 * 2758313 * 2
def baseEnd_2758313 : Nat := 472113454848390607134085

theorem tailTrace_2758313 : CollatzResearch.WordTrace tailWord_2758313 prefixEnd_2758313 472113454848390607134085 := by
  unfold tailWord_2758313
  simp only [CollatzResearch.WordTrace]
  refine ⟨100603940056110558200727593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67069293370740372133818395 100603940056110558200727593)
  ·
    refine ⟨75452955042082918650545695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100603940056110558200727593 75452955042082918650545695)
    ·
      refine ⟨113179432563124377975818543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75452955042082918650545695 113179432563124377975818543)
      ·
        refine ⟨169769148844686566963727815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113179432563124377975818543 169769148844686566963727815)
        ·
          refine ⟨254653723267029850445591723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169769148844686566963727815 254653723267029850445591723)
          ·
            refine ⟨381980584900544775668387585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254653723267029850445591723 381980584900544775668387585)
            ·
              refine ⟨286485438675408581751290689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381980584900544775668387585 286485438675408581751290689)
              ·
                refine ⟨214864079006556436313468017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286485438675408581751290689 214864079006556436313468017)
                ·
                  refine ⟨161148059254917327235101013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214864079006556436313468017 161148059254917327235101013)
                  ·
                    refine ⟨472113454848390607134085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 161148059254917327235101013 472113454848390607134085)
                    ·
                      rfl

theorem cell23_2758313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 10].length) (baseStart_2758313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758313 prefixEnd_2758313 := by exact prefixLift 2758313
  have htrace : WordTrace (prefixWord ++ tailWord_2758313) baseStart_2758313 baseEnd_2758313 := by
    simpa [prefixWord, tailWord_2758313, baseEnd_2758313] using wordTrace_append hprefix tailTrace_2758313
  have hstable : (prefixWord ++ tailWord_2758313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758313).length < 2 ^ (prefixWord ++ tailWord_2758313).sum := by decide
  have hdescent : baseEnd_2758313 < baseStart_2758313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758325 : List Nat := [1, 3, 3, 3, 3, 1, 2, 2, 1, 4]
def baseStart_2758325 : Nat := 118140960795 + 2758325 * 2 ^ 59
def prefixEnd_2758325 : Nat := 4983230072969 + 3 ^ 40 * 2758325 * 2
def baseEnd_2758325 : Nat := 472115508771008591484067

theorem tailTrace_2758325 : CollatzResearch.WordTrace tailWord_2758325 prefixEnd_2758325 472115508771008591484067 := by
  unfold tailWord_2758325
  simp only [CollatzResearch.WordTrace]
  refine ⟨100604377732067084250164429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67069585154711389500109619 100604377732067084250164429)
  ·
    refine ⟨37726641649525156593811661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100604377732067084250164429 37726641649525156593811661)
    ·
      refine ⟨14147490618571933722679373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37726641649525156593811661 14147490618571933722679373)
      ·
        refine ⟨5305308981964475146004765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14147490618571933722679373 5305308981964475146004765)
        ·
          refine ⟨1989490868236678179751787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5305308981964475146004765 1989490868236678179751787)
          ·
            refine ⟨2984236302355017269627681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1989490868236678179751787 2984236302355017269627681)
            ·
              refine ⟨2238177226766262952220761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2984236302355017269627681 2238177226766262952220761)
              ·
                refine ⟨1678632920074697214165571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2238177226766262952220761 1678632920074697214165571)
                ·
                  refine ⟨2517949380112045821248357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678632920074697214165571 2517949380112045821248357)
                  ·
                    refine ⟨472115508771008591484067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2517949380112045821248357 472115508771008591484067)
                    ·
                      rfl

theorem cell23_2758325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_2758325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758325 prefixEnd_2758325 := by exact prefixLift 2758325
  have htrace : WordTrace (prefixWord ++ tailWord_2758325) baseStart_2758325 baseEnd_2758325 := by
    simpa [prefixWord, tailWord_2758325, baseEnd_2758325] using wordTrace_append hprefix tailTrace_2758325
  have hstable : (prefixWord ++ tailWord_2758325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758325).length < 2 ^ (prefixWord ++ tailWord_2758325).sum := by decide
  have hdescent : baseEnd_2758325 < baseStart_2758325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758358 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_2758358 : Nat := 118140960795 + 2758358 * 2 ^ 59
def prefixEnd_2758358 : Nat := 4983230072969 + 3 ^ 40 * 2758358 * 2
def baseEnd_2758358 : Nat := 1416363471174624145339549

theorem tailTrace_2758358 : CollatzResearch.WordTrace tailWord_2758358 prefixEnd_2758358 1416363471174624145339549 := by
  unfold tailWord_2758358
  simp only [CollatzResearch.WordTrace]
  refine ⟨6287848833809220680382233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67070387560631687257410485 6287848833809220680382233)
  ·
    refine ⟨4715886625356915510286675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6287848833809220680382233 4715886625356915510286675)
    ·
      refine ⟨7073829938035373265430013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4715886625356915510286675 7073829938035373265430013)
      ·
        refine ⟨2652686226763264974536255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7073829938035373265430013 2652686226763264974536255)
        ·
          refine ⟨3979029340144897461804383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2652686226763264974536255 3979029340144897461804383)
          ·
            refine ⟨5968544010217346192706575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3979029340144897461804383 5968544010217346192706575)
            ·
              refine ⟨8952816015326019289059863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5968544010217346192706575 8952816015326019289059863)
              ·
                refine ⟨13429224022989028933589795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8952816015326019289059863 13429224022989028933589795)
                ·
                  refine ⟨20143836034483543400384693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13429224022989028933589795 20143836034483543400384693)
                  ·
                    refine ⟨1888484628232832193786065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20143836034483543400384693 1888484628232832193786065)
                    ·
                      refine ⟨1416363471174624145339549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1888484628232832193786065 1416363471174624145339549)
                      ·
                        rfl

theorem cell23_2758358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_2758358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758358 prefixEnd_2758358 := by exact prefixLift 2758358
  have htrace : WordTrace (prefixWord ++ tailWord_2758358) baseStart_2758358 baseEnd_2758358 := by
    simpa [prefixWord, tailWord_2758358, baseEnd_2758358] using wordTrace_append hprefix tailTrace_2758358
  have hstable : (prefixWord ++ tailWord_2758358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758358).length < 2 ^ (prefixWord ++ tailWord_2758358).sum := by decide
  have hdescent : baseEnd_2758358 < baseStart_2758358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758365 : List Nat := [1, 4, 3, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2758365 : Nat := 118140960795 + 2758365 * 2 ^ 59
def prefixEnd_2758365 : Nat := 4983230072969 + 3 ^ 40 * 2758365 * 2
def baseEnd_2758365 : Nat := 1416367065539205617952017

theorem tailTrace_2758365 : CollatzResearch.WordTrace tailWord_2758365 prefixEnd_2758365 1416367065539205617952017 := by
  unfold tailWord_2758365
  simp only [CollatzResearch.WordTrace]
  refine ⟨100605836651922171081620549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67070557767948114054413699 100605836651922171081620549)
  ·
    refine ⟨18863594372235407077803853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100605836651922171081620549 18863594372235407077803853)
    ·
      refine ⟨7073847889588277654176445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18863594372235407077803853 7073847889588277654176445)
      ·
        refine ⟨2652692958595604120316167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7073847889588277654176445 2652692958595604120316167)
        ·
          refine ⟨3979039437893406180474251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2652692958595604120316167 3979039437893406180474251)
          ·
            refine ⟨5968559156840109270711377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3979039437893406180474251 5968559156840109270711377)
            ·
              refine ⟨4476419367630081953033533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5968559156840109270711377 4476419367630081953033533)
              ·
                refine ⟨1678657262861280732387575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4476419367630081953033533 1678657262861280732387575)
                ·
                  refine ⟨2517985894291921098581363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678657262861280732387575 2517985894291921098581363)
                  ·
                    refine ⟨3776978841437881647872045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2517985894291921098581363 3776978841437881647872045)
                    ·
                      refine ⟨1416367065539205617952017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3776978841437881647872045 1416367065539205617952017)
                      ·
                        rfl

theorem cell23_2758365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2758365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758365 prefixEnd_2758365 := by exact prefixLift 2758365
  have htrace : WordTrace (prefixWord ++ tailWord_2758365) baseStart_2758365 baseEnd_2758365 := by
    simpa [prefixWord, tailWord_2758365, baseEnd_2758365] using wordTrace_append hprefix tailTrace_2758365
  have hstable : (prefixWord ++ tailWord_2758365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758365).length < 2 ^ (prefixWord ++ tailWord_2758365).sum := by decide
  have hdescent : baseEnd_2758365 < baseStart_2758365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758381 : List Nat := [1, 5, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_2758381 : Nat := 118140960795 + 2758381 * 2 ^ 59
def prefixEnd_2758381 : Nat := 4983230072969 + 3 ^ 40 * 2758381 * 2
def baseEnd_2758381 : Nat := 472125093743225851783981

theorem tailTrace_2758381 : CollatzResearch.WordTrace tailWord_2758381 prefixEnd_2758381 472125093743225851783981 := by
  unfold tailWord_2758381
  simp only [CollatzResearch.WordTrace]
  refine ⟨100606420219864205814202997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67070946813242803876135331 100606420219864205814202997)
  ·
    refine ⟨9431851895612269295081531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100606420219864205814202997 9431851895612269295081531)
    ·
      refine ⟨14147777843418403942622297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9431851895612269295081531 14147777843418403942622297)
      ·
        refine ⟨10610833382563802956966723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14147777843418403942622297 10610833382563802956966723)
        ·
          refine ⟨15916250073845704435450085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10610833382563802956966723 15916250073845704435450085)
          ·
            refine ⟨2984296888846069581646891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15916250073845704435450085 2984296888846069581646891)
            ·
              refine ⟨4476445333269104372470337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2984296888846069581646891 4476445333269104372470337)
              ·
                refine ⟨3357333999951828279352753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4476445333269104372470337 3357333999951828279352753)
                ·
                  refine ⟨2518000499963871209514565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3357333999951828279352753 2518000499963871209514565)
                  ·
                    refine ⟨472125093743225851783981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2518000499963871209514565 472125093743225851783981)
                    ·
                      rfl

theorem cell23_2758381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_2758381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758381 prefixEnd_2758381 := by exact prefixLift 2758381
  have htrace : WordTrace (prefixWord ++ tailWord_2758381) baseStart_2758381 baseEnd_2758381 := by
    simpa [prefixWord, tailWord_2758381, baseEnd_2758381] using wordTrace_append hprefix tailTrace_2758381
  have hstable : (prefixWord ++ tailWord_2758381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758381).length < 2 ^ (prefixWord ++ tailWord_2758381).sum := by decide
  have hdescent : baseEnd_2758381 < baseStart_2758381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758397 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 2, 7, 2]
def baseStart_2758397 : Nat := 118140960795 + 2758397 * 2 ^ 59
def prefixEnd_2758397 : Nat := 4983230072969 + 3 ^ 40 * 2758397 * 2
def baseEnd_2758397 : Nat := 1416383496920149492751869

theorem tailTrace_2758397 : CollatzResearch.WordTrace tailWord_2758397 prefixEnd_2758397 1416383496920149492751869 := by
  unfold tailWord_2758397
  simp only [CollatzResearch.WordTrace]
  refine ⟨100607003787806240546785445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67071335858537493697856963 100607003787806240546785445)
  ·
    refine ⟨18863813210213670102522271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100607003787806240546785445 18863813210213670102522271)
    ·
      refine ⟨28295719815320505153783407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18863813210213670102522271 28295719815320505153783407)
      ·
        refine ⟨42443579722980757730675111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28295719815320505153783407 42443579722980757730675111)
        ·
          refine ⟨63665369584471136596012667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42443579722980757730675111 63665369584471136596012667)
          ·
            refine ⟨95498054376706704894019001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63665369584471136596012667 95498054376706704894019001)
            ·
              refine ⟨71623540782530028670514251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95498054376706704894019001 71623540782530028670514251)
              ·
                refine ⟨107435311173795043005771377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71623540782530028670514251 107435311173795043005771377)
                ·
                  refine ⟨80576483380346282254328533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107435311173795043005771377 80576483380346282254328533)
                  ·
                    refine ⟨1888511329226865990335825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 80576483380346282254328533 1888511329226865990335825)
                    ·
                      refine ⟨1416383496920149492751869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1888511329226865990335825 1416383496920149492751869)
                      ·
                        rfl

theorem cell23_2758397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_2758397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758397 prefixEnd_2758397 := by exact prefixLift 2758397
  have htrace : WordTrace (prefixWord ++ tailWord_2758397) baseStart_2758397 baseEnd_2758397 := by
    simpa [prefixWord, tailWord_2758397, baseEnd_2758397] using wordTrace_append hprefix tailTrace_2758397
  have hstable : (prefixWord ++ tailWord_2758397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758397).length < 2 ^ (prefixWord ++ tailWord_2758397).sum := by decide
  have hdescent : baseEnd_2758397 < baseStart_2758397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758398 : List Nat := [4, 2, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_2758398 : Nat := 118140960795 + 2758398 * 2 ^ 59
def prefixEnd_2758398 : Nat := 4983230072969 + 3 ^ 40 * 2758398 * 2
def baseEnd_2758398 : Nat := 472128003466934662946455

theorem tailTrace_2758398 : CollatzResearch.WordTrace tailWord_2758398 prefixEnd_2758398 472128003466934662946455 := by
  unfold tailWord_2758398
  simp only [CollatzResearch.WordTrace]
  refine ⟨12575880032600327214696481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67071360173868411811714565 12575880032600327214696481)
  ·
    refine ⟨9431910024450245411022361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12575880032600327214696481 9431910024450245411022361)
    ·
      refine ⟨7073932518337684058266771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9431910024450245411022361 7073932518337684058266771)
      ·
        refine ⟨10610898777506526087400157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7073932518337684058266771 10610898777506526087400157)
        ·
          refine ⟨3979087041564947282775059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10610898777506526087400157 3979087041564947282775059)
          ·
            refine ⟨5968630562347420924162589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3979087041564947282775059 5968630562347420924162589)
            ·
              refine ⟨2238236460880282846560971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5968630562347420924162589 2238236460880282846560971)
              ·
                refine ⟨3357354691320424269841457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2238236460880282846560971 3357354691320424269841457)
                ·
                  refine ⟨2518016018490318202381093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3357354691320424269841457 2518016018490318202381093)
                  ·
                    refine ⟨472128003466934662946455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2518016018490318202381093 472128003466934662946455)
                    ·
                      rfl

theorem cell23_2758398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_2758398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758398 prefixEnd_2758398 := by exact prefixLift 2758398
  have htrace : WordTrace (prefixWord ++ tailWord_2758398) baseStart_2758398 baseEnd_2758398 := by
    simpa [prefixWord, tailWord_2758398, baseEnd_2758398] using wordTrace_append hprefix tailTrace_2758398
  have hstable : (prefixWord ++ tailWord_2758398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758398).length < 2 ^ (prefixWord ++ tailWord_2758398).sum := by decide
  have hdescent : baseEnd_2758398 < baseStart_2758398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758404 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_2758404 : Nat := 118140960795 + 2758404 * 2 ^ 59
def prefixEnd_2758404 : Nat := 4983230072969 + 3 ^ 40 * 2758404 * 2
def baseEnd_2758404 : Nat := 1416387091284730965364337

theorem tailTrace_2758404 : CollatzResearch.WordTrace tailWord_2758404 prefixEnd_2758404 1416387091284730965364337 := by
  unfold tailWord_2758404
  simp only [CollatzResearch.WordTrace]
  refine ⟨50303629549390440371145133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67071506065853920494860177 50303629549390440371145133)
  ·
    refine ⟨18863861081021415139179425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50303629549390440371145133 18863861081021415139179425)
    ·
      refine ⟨14147895810766061354384569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18863861081021415139179425 14147895810766061354384569)
      ·
        refine ⟨10610921858074546015788427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14147895810766061354384569 10610921858074546015788427)
        ·
          refine ⟨15916382787111819023682641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10610921858074546015788427 15916382787111819023682641)
          ·
            refine ⟨11937287090333864267761981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15916382787111819023682641 11937287090333864267761981)
            ·
              refine ⟨4476482658875199100410743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11937287090333864267761981 4476482658875199100410743)
              ·
                refine ⟨6714723988312798650616115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4476482658875199100410743 6714723988312798650616115)
                ·
                  refine ⟨10072085982469197975924173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6714723988312798650616115 10072085982469197975924173)
                  ·
                    refine ⟨3777032243425949240971565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10072085982469197975924173 3777032243425949240971565)
                    ·
                      refine ⟨1416387091284730965364337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3777032243425949240971565 1416387091284730965364337)
                      ·
                        rfl

theorem cell23_2758404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_2758404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758404 prefixEnd_2758404 := by exact prefixLift 2758404
  have htrace : WordTrace (prefixWord ++ tailWord_2758404) baseStart_2758404 baseEnd_2758404 := by
    simpa [prefixWord, tailWord_2758404, baseEnd_2758404] using wordTrace_append hprefix tailTrace_2758404
  have hstable : (prefixWord ++ tailWord_2758404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758404).length < 2 ^ (prefixWord ++ tailWord_2758404).sum := by decide
  have hdescent : baseEnd_2758404 < baseStart_2758404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758414 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2]
def baseStart_2758414 : Nat := 118140960795 + 2758414 * 2 ^ 59
def prefixEnd_2758414 : Nat := 4983230072969 + 3 ^ 40 * 2758414 * 2
def baseEnd_2758414 : Nat := 1416392226091275926239291

theorem tailTrace_2758414 : CollatzResearch.WordTrace tailWord_2758414 prefixEnd_2758414 1416392226091275926239291 := by
  unfold tailWord_2758414
  simp only [CollatzResearch.WordTrace]
  refine ⟨12575952978593081556269287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67071749219163101633436197 12575952978593081556269287)
  ·
    refine ⟨18863929467889622334403931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12575952978593081556269287 18863929467889622334403931)
    ·
      refine ⟨28295894201834433501605897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18863929467889622334403931 28295894201834433501605897)
      ·
        refine ⟨21221920651375825126204423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28295894201834433501605897 21221920651375825126204423)
        ·
          refine ⟨31832880977063737689306635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21221920651375825126204423 31832880977063737689306635)
          ·
            refine ⟨47749321465595606533959953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31832880977063737689306635 47749321465595606533959953)
            ·
              refine ⟨35811991099196704900469965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47749321465595606533959953 35811991099196704900469965)
              ·
                refine ⟨13429496662198764337676237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35811991099196704900469965 13429496662198764337676237)
                ·
                  refine ⟨5036061248324536626628589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13429496662198764337676237 5036061248324536626628589)
                  ·
                    refine ⟨1888522968121701234985721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5036061248324536626628589 1888522968121701234985721)
                    ·
                      refine ⟨1416392226091275926239291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1888522968121701234985721 1416392226091275926239291)
                      ·
                        rfl

theorem cell23_2758414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_2758414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758414 prefixEnd_2758414 := by exact prefixLift 2758414
  have htrace : WordTrace (prefixWord ++ tailWord_2758414) baseStart_2758414 baseEnd_2758414 := by
    simpa [prefixWord, tailWord_2758414, baseEnd_2758414] using wordTrace_append hprefix tailTrace_2758414
  have hstable : (prefixWord ++ tailWord_2758414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758414).length < 2 ^ (prefixWord ++ tailWord_2758414).sum := by decide
  have hdescent : baseEnd_2758414 < baseStart_2758414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758497 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 2, 5]
def baseStart_2758497 : Nat := 118140960795 + 2758497 * 2 ^ 59
def prefixEnd_2758497 : Nat := 4983230072969 + 3 ^ 40 * 2758497 * 2
def baseEnd_2758497 : Nat := 472144948328533033833803

theorem tailTrace_2758497 : CollatzResearch.WordTrace tailWord_2758497 prefixEnd_2758497 472144948328533033833803 := by
  unfold tailWord_2758497
  simp only [CollatzResearch.WordTrace]
  refine ⟨100610651087443957625425745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67073767391629305083617163 100610651087443957625425745)
  ·
    refine ⟨75457988315582968219069309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100610651087443957625425745 75457988315582968219069309)
    ·
      refine ⟨28296745618343613082150991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75457988315582968219069309 28296745618343613082150991)
      ·
        refine ⟨42445118427515419623226487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28296745618343613082150991 42445118427515419623226487)
        ·
          refine ⟨63667677641273129434839731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42445118427515419623226487 63667677641273129434839731)
          ·
            refine ⟨95501516461909694152259597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63667677641273129434839731 95501516461909694152259597)
            ·
              refine ⟨35813068673216135307097349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95501516461909694152259597 35813068673216135307097349)
              ·
                refine ⟨6714950376228025370080753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35813068673216135307097349 6714950376228025370080753)
                ·
                  refine ⟨5036212782171019027560565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6714950376228025370080753 5036212782171019027560565)
                  ·
                    refine ⟨472144948328533033833803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5036212782171019027560565 472144948328533033833803)
                    ·
                      rfl

theorem cell23_2758497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_2758497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758497 prefixEnd_2758497 := by exact prefixLift 2758497
  have htrace : WordTrace (prefixWord ++ tailWord_2758497) baseStart_2758497 baseEnd_2758497 := by
    simpa [prefixWord, tailWord_2758497, baseEnd_2758497] using wordTrace_append hprefix tailTrace_2758497
  have hstable : (prefixWord ++ tailWord_2758497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758497).length < 2 ^ (prefixWord ++ tailWord_2758497).sum := by decide
  have hdescent : baseEnd_2758497 < baseStart_2758497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758504 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 1, 7, 2]
def baseStart_2758504 : Nat := 118140960795 + 2758504 * 2 ^ 59
def prefixEnd_2758504 : Nat := 4983230072969 + 3 ^ 40 * 2758504 * 2
def baseEnd_2758504 : Nat := 1416438439350180574113877

theorem tailTrace_2758504 : CollatzResearch.WordTrace tailWord_2758504 prefixEnd_2758504 1416438439350180574113877 := by
  unfold tailWord_2758504
  simp only [CollatzResearch.WordTrace]
  refine ⟨50305453199209298910465283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67073937598945731880620377 50305453199209298910465283)
  ·
    refine ⟨75458179798813948365697925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50305453199209298910465283 75458179798813948365697925)
    ·
      refine ⟨14148408712277615318568361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75458179798813948365697925 14148408712277615318568361)
      ·
        refine ⟨10611306534208211488926271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14148408712277615318568361 10611306534208211488926271)
        ·
          refine ⟨15916959801312317233389407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10611306534208211488926271 15916959801312317233389407)
          ·
            refine ⟨23875439701968475850084111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15916959801312317233389407 23875439701968475850084111)
            ·
              refine ⟨35813159552952713775126167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23875439701968475850084111 35813159552952713775126167)
              ·
                refine ⟨53719739329429070662689251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35813159552952713775126167 53719739329429070662689251)
                ·
                  refine ⟨80579608994143605994033877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53719739329429070662689251 80579608994143605994033877)
                  ·
                    refine ⟨1888584585800240765485169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 80579608994143605994033877 1888584585800240765485169)
                    ·
                      refine ⟨1416438439350180574113877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1888584585800240765485169 1416438439350180574113877)
                      ·
                        rfl

theorem cell23_2758504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_2758504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758504 prefixEnd_2758504 := by exact prefixLift 2758504
  have htrace : WordTrace (prefixWord ++ tailWord_2758504) baseStart_2758504 baseEnd_2758504 := by
    simpa [prefixWord, tailWord_2758504, baseEnd_2758504] using wordTrace_append hprefix tailTrace_2758504
  have hstable : (prefixWord ++ tailWord_2758504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758504).length < 2 ^ (prefixWord ++ tailWord_2758504).sum := by decide
  have hdescent : baseEnd_2758504 < baseStart_2758504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758634 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 1, 6]
def baseStart_2758634 : Nat := 118140960795 + 2758634 * 2 ^ 59
def prefixEnd_2758634 : Nat := 4983230072969 + 3 ^ 40 * 2758634 * 2
def baseEnd_2758634 : Nat := 472168397278421688496093

theorem tailTrace_2758634 : CollatzResearch.WordTrace tailWord_2758634 prefixEnd_2758634 472168397278421688496093 := by
  unfold tailWord_2758634
  simp only [CollatzResearch.WordTrace]
  refine ⟨25153911971986907505790739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67077098591965086682108637 25153911971986907505790739)
  ·
    refine ⟨37730867957980361258686109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25153911971986907505790739 37730867957980361258686109)
    ·
      refine ⟨14149075484242635472007291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37730867957980361258686109 14149075484242635472007291)
      ·
        refine ⟨21223613226363953208010937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14149075484242635472007291 21223613226363953208010937)
        ·
          refine ⟨15917709919772964906008203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21223613226363953208010937 15917709919772964906008203)
          ·
            refine ⟨23876564879659447359012305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15917709919772964906008203 23876564879659447359012305)
            ·
              refine ⟨17907423659744585519259229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23876564879659447359012305 17907423659744585519259229)
              ·
                refine ⟨6715283872404219569722211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17907423659744585519259229 6715283872404219569722211)
                ·
                  refine ⟨10072925808606329354583317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6715283872404219569722211 10072925808606329354583317)
                  ·
                    refine ⟨472168397278421688496093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10072925808606329354583317 472168397278421688496093)
                    ·
                      rfl

theorem cell23_2758634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_2758634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758634 prefixEnd_2758634 := by exact prefixLift 2758634
  have htrace : WordTrace (prefixWord ++ tailWord_2758634) baseStart_2758634 baseEnd_2758634 := by
    simpa [prefixWord, tailWord_2758634, baseEnd_2758634] using wordTrace_append hprefix tailTrace_2758634
  have hstable : (prefixWord ++ tailWord_2758634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758634).length < 2 ^ (prefixWord ++ tailWord_2758634).sum := by decide
  have hdescent : baseEnd_2758634 < baseStart_2758634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758638 : List Nat := [4, 1, 2, 1, 3, 3, 1, 2, 1, 5]
def baseStart_2758638 : Nat := 118140960795 + 2758638 * 2 ^ 59
def prefixEnd_2758638 : Nat := 4983230072969 + 3 ^ 40 * 2758638 * 2
def baseEnd_2758638 : Nat := 472169081919294349946087

theorem tailTrace_2758638 : CollatzResearch.WordTrace tailWord_2758638 prefixEnd_2758638 472169081919294349946087 := by
  unfold tailWord_2758638
  simp only [CollatzResearch.WordTrace]
  refine ⟨12576974222491642338288571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67077195853288759137539045 12576974222491642338288571)
  ·
    refine ⟨18865461333737463507432857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12576974222491642338288571 18865461333737463507432857)
    ·
      refine ⟨14149096000303097630574643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18865461333737463507432857 14149096000303097630574643)
      ·
        refine ⟨21223644000454646445861965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14149096000303097630574643 21223644000454646445861965)
        ·
          refine ⟨7958866500170492417198237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21223644000454646445861965 7958866500170492417198237)
          ·
            refine ⟨2984574937563934656449339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7958866500170492417198237 2984574937563934656449339)
            ·
              refine ⟨4476862406345901984674009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2984574937563934656449339 4476862406345901984674009)
              ·
                refine ⟨3357646804759426488505507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4476862406345901984674009 3357646804759426488505507)
                ·
                  refine ⟨5036470207139139732758261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3357646804759426488505507 5036470207139139732758261)
                  ·
                    refine ⟨472169081919294349946087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5036470207139139732758261 472169081919294349946087)
                    ·
                      rfl

theorem cell23_2758638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_2758638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758638 prefixEnd_2758638 := by exact prefixLift 2758638
  have htrace : WordTrace (prefixWord ++ tailWord_2758638) baseStart_2758638 baseEnd_2758638 := by
    simpa [prefixWord, tailWord_2758638, baseEnd_2758638] using wordTrace_append hprefix tailTrace_2758638
  have hstable : (prefixWord ++ tailWord_2758638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758638).length < 2 ^ (prefixWord ++ tailWord_2758638).sum := by decide
  have hdescent : baseEnd_2758638 < baseStart_2758638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758641 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 3, 1, 4]
def baseStart_2758641 : Nat := 118140960795 + 2758641 * 2 ^ 59
def prefixEnd_2758641 : Nat := 4983230072969 + 3 ^ 40 * 2758641 * 2
def baseEnd_2758641 : Nat := 1416508786199846538100747

theorem tailTrace_2758641 : CollatzResearch.WordTrace tailWord_2758641 prefixEnd_2758641 1416508786199846538100747 := by
  unfold tailWord_2758641
  simp only [CollatzResearch.WordTrace]
  refine ⟨100615903198922270218667777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67077268799281513479111851 100615903198922270218667777)
  ·
    refine ⟨75461927399191702664000833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100615903198922270218667777 75461927399191702664000833)
    ·
      refine ⟨56596445549393776998000625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75461927399191702664000833 56596445549393776998000625)
      ·
        refine ⟨42447334162045332748500469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56596445549393776998000625 42447334162045332748500469)
        ·
          refine ⟨3979437577691749945171919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42447334162045332748500469 3979437577691749945171919)
          ·
            refine ⟨5969156366537624917757879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3979437577691749945171919 5969156366537624917757879)
            ·
              refine ⟨8953734549806437376636819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5969156366537624917757879 8953734549806437376636819)
              ·
                refine ⟨13430601824709656064955229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8953734549806437376636819 13430601824709656064955229)
                ·
                  refine ⟨5036475684266121024358211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13430601824709656064955229 5036475684266121024358211)
                  ·
                    refine ⟨7554713526399181536537317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5036475684266121024358211 7554713526399181536537317)
                    ·
                      refine ⟨1416508786199846538100747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7554713526399181536537317 1416508786199846538100747)
                      ·
                        rfl

theorem cell23_2758641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_2758641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758641 prefixEnd_2758641 := by exact prefixLift 2758641
  have htrace : WordTrace (prefixWord ++ tailWord_2758641) baseStart_2758641 baseEnd_2758641 := by
    simpa [prefixWord, tailWord_2758641, baseEnd_2758641] using wordTrace_append hprefix tailTrace_2758641
  have hstable : (prefixWord ++ tailWord_2758641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758641).length < 2 ^ (prefixWord ++ tailWord_2758641).sum := by decide
  have hdescent : baseEnd_2758641 < baseStart_2758641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758661 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 1, 1, 5]
def baseStart_2758661 : Nat := 118140960795 + 2758661 * 2 ^ 59
def prefixEnd_2758661 : Nat := 4983230072969 + 3 ^ 40 * 2758661 * 2
def baseEnd_2758661 : Nat := 1416519055812936459850655

theorem tailTrace_2758661 : CollatzResearch.WordTrace tailWord_2758661 prefixEnd_2758661 1416519055812936459850655 := by
  unfold tailWord_2758661
  simp only [CollatzResearch.WordTrace]
  refine ⟨100616632658849813634395837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67077755105899875756263891 100616632658849813634395837)
  ·
    refine ⟨37731237247068680112898439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100616632658849813634395837 37731237247068680112898439)
    ·
      refine ⟨56596855870603020169347659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37731237247068680112898439 56596855870603020169347659)
      ·
        refine ⟨84895283805904530254021489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56596855870603020169347659 84895283805904530254021489)
        ·
          refine ⟨63671462854428397690516117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84895283805904530254021489 63671462854428397690516117)
          ·
            refine ⟨2984599821301331141742943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 63671462854428397690516117 2984599821301331141742943)
            ·
              refine ⟨4476899731951996712614415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2984599821301331141742943 4476899731951996712614415)
              ·
                refine ⟨6715349597927995068921623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4476899731951996712614415 6715349597927995068921623)
                ·
                  refine ⟨10073024396891992603382435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6715349597927995068921623 10073024396891992603382435)
                  ·
                    refine ⟨15109536595337988905073653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10073024396891992603382435 15109536595337988905073653)
                    ·
                      refine ⟨1416519055812936459850655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15109536595337988905073653 1416519055812936459850655)
                      ·
                        rfl

theorem cell23_2758661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_2758661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758661 prefixEnd_2758661 := by exact prefixLift 2758661
  have htrace : WordTrace (prefixWord ++ tailWord_2758661) baseStart_2758661 baseEnd_2758661 := by
    simpa [prefixWord, tailWord_2758661, baseEnd_2758661] using wordTrace_append hprefix tailTrace_2758661
  have hstable : (prefixWord ++ tailWord_2758661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758661).length < 2 ^ (prefixWord ++ tailWord_2758661).sum := by decide
  have hdescent : baseEnd_2758661 < baseStart_2758661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758691 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 3]
def baseStart_2758691 : Nat := 118140960795 + 2758691 * 2 ^ 59
def prefixEnd_2758691 : Nat := 4983230072969 + 3 ^ 40 * 2758691 * 2
def baseEnd_2758691 : Nat := 1416534460232571342475517

theorem tailTrace_2758691 : CollatzResearch.WordTrace tailWord_2758691 prefixEnd_2758691 1416534460232571342475517 := by
  unfold tailWord_2758691
  simp only [CollatzResearch.WordTrace]
  refine ⟨100617726848741128757987927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67078484565827419171991951 100617726848741128757987927)
  ·
    refine ⟨150926590273111693136981891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100617726848741128757987927 150926590273111693136981891)
    ·
      refine ⟨226389885409667539705472837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150926590273111693136981891 226389885409667539705472837)
      ·
        refine ⟨42448103514312663694776157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226389885409667539705472837 42448103514312663694776157)
        ·
          refine ⟨15918038817867248885541059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42448103514312663694776157 15918038817867248885541059)
          ·
            refine ⟨23877058226800873328311589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15918038817867248885541059 23877058226800873328311589)
            ·
              refine ⟨4476948417525163749058423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23877058226800873328311589 4476948417525163749058423)
              ·
                refine ⟨6715422626287745623587635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4476948417525163749058423 6715422626287745623587635)
                ·
                  refine ⟨10073133939431618435381453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6715422626287745623587635 10073133939431618435381453)
                  ·
                    refine ⟨3777425227286856913268045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10073133939431618435381453 3777425227286856913268045)
                    ·
                      refine ⟨1416534460232571342475517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3777425227286856913268045 1416534460232571342475517)
                      ·
                        rfl

theorem cell23_2758691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_2758691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758691 prefixEnd_2758691 := by exact prefixLift 2758691
  have htrace : WordTrace (prefixWord ++ tailWord_2758691) baseStart_2758691 baseEnd_2758691 := by
    simpa [prefixWord, tailWord_2758691, baseEnd_2758691] using wordTrace_append hprefix tailTrace_2758691
  have hstable : (prefixWord ++ tailWord_2758691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758691).length < 2 ^ (prefixWord ++ tailWord_2758691).sum := by decide
  have hdescent : baseEnd_2758691 < baseStart_2758691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758712 : List Nat := [2, 1, 2, 1, 7, 1, 2, 1, 1, 2, 3]
def baseStart_2758712 : Nat := 118140960795 + 2758712 * 2 ^ 59
def prefixEnd_2758712 : Nat := 4983230072969 + 3 ^ 40 * 2758712 * 2
def baseEnd_2758712 : Nat := 1416545243326315760312921

theorem tailTrace_2758712 : CollatzResearch.WordTrace tailWord_2758712 prefixEnd_2758712 1416545243326315760312921 := by
  unfold tailWord_2758712
  simp only [CollatzResearch.WordTrace]
  refine ⟨50309246390832524672251195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67078995187776699563001593 50309246390832524672251195)
  ·
    refine ⟨75463869586248787008376793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50309246390832524672251195 75463869586248787008376793)
    ·
      refine ⟨56597902189686590256282595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75463869586248787008376793 56597902189686590256282595)
      ·
        refine ⟨84896853284529885384423893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56597902189686590256282595 84896853284529885384423893)
        ·
          refine ⟨1989769998856169188697435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 84896853284529885384423893 1989769998856169188697435)
          ·
            refine ⟨2984654998284253783046153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1989769998856169188697435 2984654998284253783046153)
            ·
              refine ⟨2238491248713190337284615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2984654998284253783046153 2238491248713190337284615)
              ·
                refine ⟨3357736873069785505926923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2238491248713190337284615 3357736873069785505926923)
                ·
                  refine ⟨5036605309604678258890385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3357736873069785505926923 5036605309604678258890385)
                  ·
                    refine ⟨3777453982203508694167789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5036605309604678258890385 3777453982203508694167789)
                    ·
                      refine ⟨1416545243326315760312921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3777453982203508694167789 1416545243326315760312921)
                      ·
                        rfl

theorem cell23_2758712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 1, 2, 3].length) (baseStart_2758712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758712 prefixEnd_2758712 := by exact prefixLift 2758712
  have htrace : WordTrace (prefixWord ++ tailWord_2758712) baseStart_2758712 baseEnd_2758712 := by
    simpa [prefixWord, tailWord_2758712, baseEnd_2758712] using wordTrace_append hprefix tailTrace_2758712
  have hstable : (prefixWord ++ tailWord_2758712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758712).length < 2 ^ (prefixWord ++ tailWord_2758712).sum := by decide
  have hdescent : baseEnd_2758712 < baseStart_2758712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758742 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_2758742 : Nat := 118140960795 + 2758742 * 2 ^ 59
def prefixEnd_2758742 : Nat := 4983230072969 + 3 ^ 40 * 2758742 * 2
def baseEnd_2758742 : Nat := 1416560647745950642937783

theorem tailTrace_2758742 : CollatzResearch.WordTrace tailWord_2758742 prefixEnd_2758742 1416560647745950642937783 := by
  unfold tailWord_2758742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6288724185722272779255905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67079724647704242978729653 6288724185722272779255905)
  ·
    refine ⟨4716543139291704584441929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6288724185722272779255905 4716543139291704584441929)
    ·
      refine ⟨3537407354468778438331447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4716543139291704584441929 3537407354468778438331447)
      ·
        refine ⟨5306111031703167657497171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3537407354468778438331447 5306111031703167657497171)
        ·
          refine ⟨7959166547554751486245757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5306111031703167657497171 7959166547554751486245757)
          ·
            refine ⟨2984687455333031807342159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7959166547554751486245757 2984687455333031807342159)
            ·
              refine ⟨4477031182999547711013239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2984687455333031807342159 4477031182999547711013239)
              ·
                refine ⟨6715546774499321566519859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4477031182999547711013239 6715546774499321566519859)
                ·
                  refine ⟨10073320161748982349779789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6715546774499321566519859 10073320161748982349779789)
                  ·
                    refine ⟨3777495060655868381167421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10073320161748982349779789 3777495060655868381167421)
                    ·
                      refine ⟨1416560647745950642937783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3777495060655868381167421 1416560647745950642937783)
                      ·
                        rfl

theorem cell23_2758742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_2758742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758742 prefixEnd_2758742 := by exact prefixLift 2758742
  have htrace : WordTrace (prefixWord ++ tailWord_2758742) baseStart_2758742 baseEnd_2758742 := by
    simpa [prefixWord, tailWord_2758742, baseEnd_2758742] using wordTrace_append hprefix tailTrace_2758742
  have hstable : (prefixWord ++ tailWord_2758742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758742).length < 2 ^ (prefixWord ++ tailWord_2758742).sum := by decide
  have hdescent : baseEnd_2758742 < baseStart_2758742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758818 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_2758818 : Nat := 118140960795 + 2758818 * 2 ^ 59
def prefixEnd_2758818 : Nat := 4983230072969 + 3 ^ 40 * 2758818 * 2
def baseEnd_2758818 : Nat := 472199890758564115195811

theorem tailTrace_2758818 : CollatzResearch.WordTrace tailWord_2758818 prefixEnd_2758818 472199890758564115195811 := by
  unfold tailWord_2758818
  simp only [CollatzResearch.WordTrace]
  refine ⟨25155589729820257361965277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67081572612854019631907405 25155589729820257361965277)
  ·
    refine ⟨9433346148682596510736979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25155589729820257361965277 9433346148682596510736979)
    ·
      refine ⟨14150019223023894766105469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9433346148682596510736979 14150019223023894766105469)
      ·
        refine ⟨5306257208633960537289551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14150019223023894766105469 5306257208633960537289551)
        ·
          refine ⟨7959385812950940805934327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5306257208633960537289551 7959385812950940805934327)
          ·
            refine ⟨11939078719426411208901491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7959385812950940805934327 11939078719426411208901491)
            ·
              refine ⟨17908618079139616813352237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11939078719426411208901491 17908618079139616813352237)
              ·
                refine ⟨6715731779677356305007089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17908618079139616813352237 6715731779677356305007089)
                ·
                  refine ⟨5036798834758017228755317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6715731779677356305007089 5036798834758017228755317)
                  ·
                    refine ⟨472199890758564115195811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5036798834758017228755317 472199890758564115195811)
                    ·
                      rfl

theorem cell23_2758818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_2758818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758818 prefixEnd_2758818 := by exact prefixLift 2758818
  have htrace : WordTrace (prefixWord ++ tailWord_2758818) baseStart_2758818 baseEnd_2758818 := by
    simpa [prefixWord, tailWord_2758818, baseEnd_2758818] using wordTrace_append hprefix tailTrace_2758818
  have hstable : (prefixWord ++ tailWord_2758818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758818).length < 2 ^ (prefixWord ++ tailWord_2758818).sum := by decide
  have hdescent : baseEnd_2758818 < baseStart_2758818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758931 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 3]
def baseStart_2758931 : Nat := 118140960795 + 2758931 * 2 ^ 59
def prefixEnd_2758931 : Nat := 4983230072969 + 3 ^ 40 * 2758931 * 2
def baseEnd_2758931 : Nat := 1416657695589650403474413

theorem tailTrace_2758931 : CollatzResearch.WordTrace tailWord_2758931 prefixEnd_2758931 1416657695589650403474413 := by
  unfold tailWord_2758931
  simp only [CollatzResearch.WordTrace]
  refine ⟨100626480367871649746724647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67084320245247766497816431 100626480367871649746724647)
  ·
    refine ⟨150939720551807474620086971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100626480367871649746724647 150939720551807474620086971)
    ·
      refine ⟨226409580827711211930130457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150939720551807474620086971 226409580827711211930130457)
      ·
        refine ⟨169807185620783408947597843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226409580827711211930130457 169807185620783408947597843)
        ·
          refine ⟨254710778431175113421396765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169807185620783408947597843 254710778431175113421396765)
          ·
            refine ⟨95516541911690667533023787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254710778431175113421396765 95516541911690667533023787)
            ·
              refine ⟨143274812867536001299535681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95516541911690667533023787 143274812867536001299535681)
              ·
                refine ⟨107456109650652000974651761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143274812867536001299535681 107456109650652000974651761)
                ·
                  refine ⟨80592082237989000730988821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107456109650652000974651761 80592082237989000730988821)
                  ·
                    refine ⟨3777753854905734409265101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80592082237989000730988821 3777753854905734409265101)
                    ·
                      refine ⟨1416657695589650403474413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3777753854905734409265101 1416657695589650403474413)
                      ·
                        rfl

theorem cell23_2758931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 3].length) (baseStart_2758931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758931 prefixEnd_2758931 := by exact prefixLift 2758931
  have htrace : WordTrace (prefixWord ++ tailWord_2758931) baseStart_2758931 baseEnd_2758931 := by
    simpa [prefixWord, tailWord_2758931, baseEnd_2758931] using wordTrace_append hprefix tailTrace_2758931
  have hstable : (prefixWord ++ tailWord_2758931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758931).length < 2 ^ (prefixWord ++ tailWord_2758931).sum := by decide
  have hdescent : baseEnd_2758931 < baseStart_2758931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758942 : List Nat := [4, 3, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_2758942 : Nat := 118140960795 + 2758942 * 2 ^ 59
def prefixEnd_2758942 : Nat := 4983230072969 + 3 ^ 40 * 2758942 * 2
def baseEnd_2758942 : Nat := 472221114625616620145621

theorem tailTrace_2758942 : CollatzResearch.WordTrace tailWord_2758942 prefixEnd_2758942 472221114625616620145621 := by
  unfold tailWord_2758942
  simp only [CollatzResearch.WordTrace]
  refine ⟨12578360196353974828171885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67084587713887865750250053 12578360196353974828171885)
  ·
    refine ⟨4716885073632740560564457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12578360196353974828171885 4716885073632740560564457)
    ·
      refine ⟨3537663805224555420423343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4716885073632740560564457 3537663805224555420423343)
      ·
        refine ⟨5306495707836833130635015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3537663805224555420423343 5306495707836833130635015)
        ·
          refine ⟨7959743561755249695952523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5306495707836833130635015 7959743561755249695952523)
          ·
            refine ⟨11939615342632874543928785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7959743561755249695952523 11939615342632874543928785)
            ·
              refine ⟨8954711506974655907946589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11939615342632874543928785 8954711506974655907946589)
              ·
                refine ⟨3358016815115495965479971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8954711506974655907946589 3358016815115495965479971)
                ·
                  refine ⟨5037025222673243948219957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3358016815115495965479971 5037025222673243948219957)
                  ·
                    refine ⟨472221114625616620145621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5037025222673243948219957 472221114625616620145621)
                    ·
                      rfl

theorem cell23_2758942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_2758942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758942 prefixEnd_2758942 := by exact prefixLift 2758942
  have htrace : WordTrace (prefixWord ++ tailWord_2758942) baseStart_2758942 baseEnd_2758942 := by
    simpa [prefixWord, tailWord_2758942, baseEnd_2758942] using wordTrace_append hprefix tailTrace_2758942
  have hstable : (prefixWord ++ tailWord_2758942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758942).length < 2 ^ (prefixWord ++ tailWord_2758942).sum := by decide
  have hdescent : baseEnd_2758942 < baseStart_2758942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758945 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 5, 2, 2]
def baseStart_2758945 : Nat := 118140960795 + 2758945 * 2 ^ 59
def prefixEnd_2758945 : Nat := 4983230072969 + 3 ^ 40 * 2758945 * 2
def baseEnd_2758945 : Nat := 1416664884318813348699349

theorem tailTrace_2758945 : CollatzResearch.WordTrace tailWord_2758945 prefixEnd_2758945 1416664884318813348699349 := by
  unfold tailWord_2758945
  simp only [CollatzResearch.WordTrace]
  refine ⟨100626990989820930137734289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67084660659880620091822859 100626990989820930137734289)
  ·
    refine ⟨75470243242365697603300717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100626990989820930137734289 75470243242365697603300717)
    ·
      refine ⟨28301341215887136601237769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75470243242365697603300717 28301341215887136601237769)
      ·
        refine ⟨21226005911915352450928327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28301341215887136601237769 21226005911915352450928327)
        ·
          refine ⟨31839008867873028676392491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21226005911915352450928327 31839008867873028676392491)
          ·
            refine ⟨47758513301809543014588737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31839008867873028676392491 47758513301809543014588737)
            ·
              refine ⟨35818884976357157260941553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47758513301809543014588737 35818884976357157260941553)
              ·
                refine ⟨26864163732267867945706165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35818884976357157260941553 26864163732267867945706165)
                ·
                  refine ⟨2518515349900112619909953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26864163732267867945706165 2518515349900112619909953)
                  ·
                    refine ⟨1888886512425084464932465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2518515349900112619909953 1888886512425084464932465)
                    ·
                      refine ⟨1416664884318813348699349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1888886512425084464932465 1416664884318813348699349)
                      ·
                        rfl

theorem cell23_2758945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_2758945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758945 prefixEnd_2758945 := by exact prefixLift 2758945
  have htrace : WordTrace (prefixWord ++ tailWord_2758945) baseStart_2758945 baseEnd_2758945 := by
    simpa [prefixWord, tailWord_2758945, baseEnd_2758945] using wordTrace_append hprefix tailTrace_2758945
  have hstable : (prefixWord ++ tailWord_2758945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758945).length < 2 ^ (prefixWord ++ tailWord_2758945).sum := by decide
  have hdescent : baseEnd_2758945 < baseStart_2758945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758948 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_2758948 : Nat := 118140960795 + 2758948 * 2 ^ 59
def prefixEnd_2758948 : Nat := 4983230072969 + 3 ^ 40 * 2758948 * 2
def baseEnd_2758948 : Nat := 1416666424760776836961835

theorem tailTrace_2758948 : CollatzResearch.WordTrace tailWord_2758948 prefixEnd_2758948 1416666424760776836961835 := by
  unfold tailWord_2758948
  simp only [CollatzResearch.WordTrace]
  refine ⟨50313550204405030825046749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67084733605873374433395665 50313550204405030825046749)
  ·
    refine ⟨18867581326651886559392531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50313550204405030825046749 18867581326651886559392531)
    ·
      refine ⟨28301371989977829839088797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18867581326651886559392531 28301371989977829839088797)
      ·
        refine ⟨10613014496241686189658299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28301371989977829839088797 10613014496241686189658299)
        ·
          refine ⟨15919521744362529284487449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10613014496241686189658299 15919521744362529284487449)
          ·
            refine ⟨11939641308271896963365587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15919521744362529284487449 11939641308271896963365587)
            ·
              refine ⟨17909461962407845445048381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11939641308271896963365587 17909461962407845445048381)
              ·
                refine ⟨6716048235902942041893143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17909461962407845445048381 6716048235902942041893143)
                ·
                  refine ⟨10074072353854413062839715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6716048235902942041893143 10074072353854413062839715)
                  ·
                    refine ⟨15111108530781619594259573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10074072353854413062839715 15111108530781619594259573)
                    ·
                      refine ⟨1416666424760776836961835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15111108530781619594259573 1416666424760776836961835)
                      ·
                        rfl

theorem cell23_2758948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_2758948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758948 prefixEnd_2758948 := by exact prefixLift 2758948
  have htrace : WordTrace (prefixWord ++ tailWord_2758948) baseStart_2758948 baseEnd_2758948 := by
    simpa [prefixWord, tailWord_2758948, baseEnd_2758948] using wordTrace_append hprefix tailTrace_2758948
  have hstable : (prefixWord ++ tailWord_2758948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758948).length < 2 ^ (prefixWord ++ tailWord_2758948).sum := by decide
  have hdescent : baseEnd_2758948 < baseStart_2758948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758991 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 5]
def baseStart_2758991 : Nat := 118140960795 + 2758991 * 2 ^ 59
def prefixEnd_2758991 : Nat := 4983230072969 + 3 ^ 40 * 2758991 * 2
def baseEnd_2758991 : Nat := 1416688504428920168724137

theorem tailTrace_2758991 : CollatzResearch.WordTrace tailWord_2758991 prefixEnd_2758991 1416688504428920168724137 := by
  unfold tailWord_2758991
  simp only [CollatzResearch.WordTrace]
  refine ⟨100628668747654279993908827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67085779165102853329272551 100628668747654279993908827)
  ·
    refine ⟨150943003121481419990863241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100628668747654279993908827 150943003121481419990863241)
    ·
      refine ⟨113207252341111064993147431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150943003121481419990863241 113207252341111064993147431)
      ·
        refine ⟨169810878511666597489721147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113207252341111064993147431 169810878511666597489721147)
        ·
          refine ⟨254716317767499896234581721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169810878511666597489721147 254716317767499896234581721)
          ·
            refine ⟨191037238325624922175936291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254716317767499896234581721 191037238325624922175936291)
            ·
              refine ⟨286555857488437383263904437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191037238325624922175936291 286555857488437383263904437)
              ·
                refine ⟨26864611639541004680991041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 286555857488437383263904437 26864611639541004680991041)
                ·
                  refine ⟨20148458729655753510743281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26864611639541004680991041 20148458729655753510743281)
                  ·
                    refine ⟨15111344047241815133057461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20148458729655753510743281 15111344047241815133057461)
                    ·
                      refine ⟨1416688504428920168724137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15111344047241815133057461 1416688504428920168724137)
                      ·
                        rfl

theorem cell23_2758991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_2758991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2758991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2758991 prefixEnd_2758991 := by exact prefixLift 2758991
  have htrace : WordTrace (prefixWord ++ tailWord_2758991) baseStart_2758991 baseEnd_2758991 := by
    simpa [prefixWord, tailWord_2758991, baseEnd_2758991] using wordTrace_append hprefix tailTrace_2758991
  have hstable : (prefixWord ++ tailWord_2758991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758991).length < 2 ^ (prefixWord ++ tailWord_2758991).sum := by decide
  have hdescent : baseEnd_2758991 < baseStart_2758991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759012 : List Nat := [2, 3, 1, 1, 3, 1, 4, 2, 2, 1, 3]
def baseStart_2759012 : Nat := 118140960795 + 2759012 * 2 ^ 59
def prefixEnd_2759012 : Nat := 4983230072969 + 3 ^ 40 * 2759012 * 2
def baseEnd_2759012 : Nat := 1416699287522664586561541

theorem tailTrace_2759012 : CollatzResearch.WordTrace tailWord_2759012 prefixEnd_2759012 1416699287522664586561541 := by
  unfold tailWord_2759012
  simp only [CollatzResearch.WordTrace]
  refine ⟨50314717340289100290211645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67086289787052133720282193 50314717340289100290211645)
  ·
    refine ⟨18868019002608412608829367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50314717340289100290211645 18868019002608412608829367)
    ·
      refine ⟨28302028503912618913244051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18868019002608412608829367 28302028503912618913244051)
      ·
        refine ⟨42453042755868928369866077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28302028503912618913244051 42453042755868928369866077)
        ·
          refine ⟨15919891033450848138699779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42453042755868928369866077 15919891033450848138699779)
          ·
            refine ⟨23879836550176272208049669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15919891033450848138699779 23879836550176272208049669)
            ·
              refine ⟨4477469353158051039009313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23879836550176272208049669 4477469353158051039009313)
              ·
                refine ⟨3358102014868538279256985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4477469353158051039009313 3358102014868538279256985)
                ·
                  refine ⟨2518576511151403709442739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3358102014868538279256985 2518576511151403709442739)
                  ·
                    refine ⟨3777864766727105564164109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2518576511151403709442739 3777864766727105564164109)
                    ·
                      refine ⟨1416699287522664586561541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3777864766727105564164109 1416699287522664586561541)
                      ·
                        rfl

theorem cell23_2759012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_2759012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759012 prefixEnd_2759012 := by exact prefixLift 2759012
  have htrace : WordTrace (prefixWord ++ tailWord_2759012) baseStart_2759012 baseEnd_2759012 := by
    simpa [prefixWord, tailWord_2759012, baseEnd_2759012] using wordTrace_append hprefix tailTrace_2759012
  have hstable : (prefixWord ++ tailWord_2759012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759012).length < 2 ^ (prefixWord ++ tailWord_2759012).sum := by decide
  have hdescent : baseEnd_2759012 < baseStart_2759012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759035 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 1, 4, 2]
def baseStart_2759035 : Nat := 118140960795 + 2759035 * 2 ^ 59
def prefixEnd_2759035 : Nat := 4983230072969 + 3 ^ 40 * 2759035 * 2
def baseEnd_2759035 : Nat := 1416711097577717996573935

theorem tailTrace_2759035 : CollatzResearch.WordTrace tailWord_2759035 prefixEnd_2759035 1416711097577717996573935 := by
  unfold tailWord_2759035
  simp only [CollatzResearch.WordTrace]
  refine ⟨100630273559494875508510559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67086849039663250339007039 100630273559494875508510559)
  ·
    refine ⟨150945410339242313262765839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100630273559494875508510559 150945410339242313262765839)
    ·
      refine ⟨226418115508863469894148759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150945410339242313262765839 226418115508863469894148759)
      ·
        refine ⟨339627173263295204841223139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226418115508863469894148759 339627173263295204841223139)
        ·
          refine ⟨509440759894942807261834709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339627173263295204841223139 509440759894942807261834709)
          ·
            refine ⟨11940017810037722045199251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 509440759894942807261834709 11940017810037722045199251)
            ·
              refine ⟨17910026715056583067798877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11940017810037722045199251 17910026715056583067798877)
              ·
                refine ⟨6716260018146218650424579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17910026715056583067798877 6716260018146218650424579)
                ·
                  refine ⟨10074390027219327975636869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6716260018146218650424579 10074390027219327975636869)
                  ·
                    refine ⟨1888948130103623995431913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10074390027219327975636869 1888948130103623995431913)
                    ·
                      refine ⟨1416711097577717996573935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1888948130103623995431913 1416711097577717996573935)
                      ·
                        rfl

theorem cell23_2759035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 4, 2].length) (baseStart_2759035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759035 prefixEnd_2759035 := by exact prefixLift 2759035
  have htrace : WordTrace (prefixWord ++ tailWord_2759035) baseStart_2759035 baseEnd_2759035 := by
    simpa [prefixWord, tailWord_2759035, baseEnd_2759035] using wordTrace_append hprefix tailTrace_2759035
  have hstable : (prefixWord ++ tailWord_2759035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759035).length < 2 ^ (prefixWord ++ tailWord_2759035).sum := by decide
  have hdescent : baseEnd_2759035 < baseStart_2759035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759048 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2759048 : Nat := 118140960795 + 2759048 * 2 ^ 59
def prefixEnd_2759048 : Nat := 4983230072969 + 3 ^ 40 * 2759048 * 2
def baseEnd_2759048 : Nat := 1416717772826226445711375

theorem tailTrace_2759048 : CollatzResearch.WordTrace tailWord_2759048 prefixEnd_2759048 1416717772826226445711375 := by
  unfold tailWord_2759048
  simp only [CollatzResearch.WordTrace]
  refine ⟨50315373854223889364366899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67087165138965185819155865 50315373854223889364366899)
  ·
    refine ⟨75473060781335834046550349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50315373854223889364366899 75473060781335834046550349)
    ·
      refine ⟨28302397793000937767456381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75473060781335834046550349 28302397793000937767456381)
      ·
        refine ⟨10613399172375351662796143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28302397793000937767456381 10613399172375351662796143)
        ·
          refine ⟨15920098758563027494194215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10613399172375351662796143 15920098758563027494194215)
          ·
            refine ⟨23880148137844541241291323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15920098758563027494194215 23880148137844541241291323)
            ·
              refine ⟨35820222206766811861936985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23880148137844541241291323 35820222206766811861936985)
              ·
                refine ⟨26865166655075108896452739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35820222206766811861936985 26865166655075108896452739)
                ·
                  refine ⟨40297749982612663344679109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26865166655075108896452739 40297749982612663344679109)
                  ·
                    refine ⟨7555828121739874377127333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40297749982612663344679109 7555828121739874377127333)
                    ·
                      refine ⟨1416717772826226445711375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7555828121739874377127333 1416717772826226445711375)
                      ·
                        rfl

theorem cell23_2759048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2759048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759048 prefixEnd_2759048 := by exact prefixLift 2759048
  have htrace : WordTrace (prefixWord ++ tailWord_2759048) baseStart_2759048 baseEnd_2759048 := by
    simpa [prefixWord, tailWord_2759048, baseEnd_2759048] using wordTrace_append hprefix tailTrace_2759048
  have hstable : (prefixWord ++ tailWord_2759048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759048).length < 2 ^ (prefixWord ++ tailWord_2759048).sum := by decide
  have hdescent : baseEnd_2759048 < baseStart_2759048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759069 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 4, 2, 2]
def baseStart_2759069 : Nat := 118140960795 + 2759069 * 2 ^ 59
def prefixEnd_2759069 : Nat := 4983230072969 + 3 ^ 40 * 2759069 * 2
def baseEnd_2759069 : Nat := 1416728555919970863548779

theorem tailTrace_2759069 : CollatzResearch.WordTrace tailWord_2759069 prefixEnd_2759069 1416728555919970863548779 := by
  unfold tailWord_2759069
  simp only [CollatzResearch.WordTrace]
  refine ⟨100631513641371699315248261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67087675760914466210165507 100631513641371699315248261)
  ·
    refine ⟨18868408807757193621609049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100631513641371699315248261 18868408807757193621609049)
    ·
      refine ⟨14151306605817895216206787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18868408807757193621609049 14151306605817895216206787)
      ·
        refine ⟨21226959908726842824310181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14151306605817895216206787 21226959908726842824310181)
        ·
          refine ⟨3980054982886283029558159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21226959908726842824310181 3980054982886283029558159)
          ·
            refine ⟨5970082474329424544337239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3980054982886283029558159 5970082474329424544337239)
            ·
              refine ⟨8955123711494136816505859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5970082474329424544337239 8955123711494136816505859)
              ·
                refine ⟨13432685567241205224758789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8955123711494136816505859 13432685567241205224758789)
                ·
                  refine ⟨2518628543857725979642273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13432685567241205224758789 2518628543857725979642273)
                  ·
                    refine ⟨1888971407893294484731705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2518628543857725979642273 1888971407893294484731705)
                    ·
                      refine ⟨1416728555919970863548779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1888971407893294484731705 1416728555919970863548779)
                      ·
                        rfl

theorem cell23_2759069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_2759069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759069 prefixEnd_2759069 := by exact prefixLift 2759069
  have htrace : WordTrace (prefixWord ++ tailWord_2759069) baseStart_2759069 baseEnd_2759069 := by
    simpa [prefixWord, tailWord_2759069, baseEnd_2759069] using wordTrace_append hprefix tailTrace_2759069
  have hstable : (prefixWord ++ tailWord_2759069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759069).length < 2 ^ (prefixWord ++ tailWord_2759069).sum := by decide
  have hdescent : baseEnd_2759069 < baseStart_2759069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759075 : List Nat := [1, 1, 1, 4, 1, 4, 2, 4, 5]
def baseStart_2759075 : Nat := 118140960795 + 2759075 * 2 ^ 59
def prefixEnd_2759075 : Nat := 4983230072969 + 3 ^ 40 * 2759075 * 2
def baseEnd_2759075 : Nat := 157414626311544204452639

theorem tailTrace_2759075 : CollatzResearch.WordTrace tailWord_2759075 prefixEnd_2759075 157414626311544204452639 := by
  unfold tailWord_2759075
  simp only [CollatzResearch.WordTrace]
  refine ⟨100631732479349962339966679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67087821652899974893311119 100631732479349962339966679)
  ·
    refine ⟨150947598719024943509950019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100631732479349962339966679 150947598719024943509950019)
    ·
      refine ⟨226421398078537415264925029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150947598719024943509950019 226421398078537415264925029)
      ·
        refine ⟨42454012139725765362173443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226421398078537415264925029 42454012139725765362173443)
        ·
          refine ⟨63681018209588648043260165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42454012139725765362173443 63681018209588648043260165)
          ·
            refine ⟨11940190914297871508111281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63681018209588648043260165 11940190914297871508111281)
            ·
              refine ⟨8955143185723403631083461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11940190914297871508111281 8955143185723403631083461)
              ·
                refine ⟨1679089347323138180828149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8955143185723403631083461 1679089347323138180828149)
                ·
                  refine ⟨157414626311544204452639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1679089347323138180828149 157414626311544204452639)
                  ·
                    rfl

theorem cell23_2759075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 5].length) (baseStart_2759075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759075 prefixEnd_2759075 := by exact prefixLift 2759075
  have htrace : WordTrace (prefixWord ++ tailWord_2759075) baseStart_2759075 baseEnd_2759075 := by
    simpa [prefixWord, tailWord_2759075, baseEnd_2759075] using wordTrace_append hprefix tailTrace_2759075
  have hstable : (prefixWord ++ tailWord_2759075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759075).length < 2 ^ (prefixWord ++ tailWord_2759075).sum := by decide
  have hdescent : baseEnd_2759075 < baseStart_2759075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759125 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_2759125 : Nat := 118140960795 + 2759125 * 2 ^ 59
def prefixEnd_2759125 : Nat := 4983230072969 + 3 ^ 40 * 2759125 * 2
def baseEnd_2759125 : Nat := 1416757310836622644448521

theorem tailTrace_2759125 : CollatzResearch.WordTrace tailWord_2759125 prefixEnd_2759125 1416757310836622644448521 := by
  unfold tailWord_2759125
  simp only [CollatzResearch.WordTrace]
  refine ⟨100633556129168820879286829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67089037419445880586191219 100633556129168820879286829)
  ·
    refine ⟨37737583548438307829732561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100633556129168820879286829 37737583548438307829732561)
    ·
      refine ⟨28303187661328730872299421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37737583548438307829732561 28303187661328730872299421)
      ·
        refine ⟨10613695372998274077112283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28303187661328730872299421 10613695372998274077112283)
        ·
          refine ⟨15920543059497411115668425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10613695372998274077112283 15920543059497411115668425)
          ·
            refine ⟨11940407294623058336751319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15920543059497411115668425 11940407294623058336751319)
            ·
              refine ⟨17910610941934587505126979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11940407294623058336751319 17910610941934587505126979)
              ·
                refine ⟨26865916412901881257690469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17910610941934587505126979 26865916412901881257690469)
                ·
                  refine ⟨5037359327419102735816963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26865916412901881257690469 5037359327419102735816963)
                  ·
                    refine ⟨7556038991128654103725445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5037359327419102735816963 7556038991128654103725445)
                    ·
                      refine ⟨1416757310836622644448521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7556038991128654103725445 1416757310836622644448521)
                      ·
                        rfl

theorem cell23_2759125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_2759125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759125 prefixEnd_2759125 := by exact prefixLift 2759125
  have htrace : WordTrace (prefixWord ++ tailWord_2759125) baseStart_2759125 baseEnd_2759125 := by
    simpa [prefixWord, tailWord_2759125, baseEnd_2759125] using wordTrace_append hprefix tailTrace_2759125
  have hstable : (prefixWord ++ tailWord_2759125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759125).length < 2 ^ (prefixWord ++ tailWord_2759125).sum := by decide
  have hdescent : baseEnd_2759125 < baseStart_2759125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759182 : List Nat := [4, 1, 1, 2, 3, 2, 2, 2, 6]
def baseStart_2759182 : Nat := 118140960795 + 2759182 * 2 ^ 59
def prefixEnd_2759182 : Nat := 4983230072969 + 3 ^ 40 * 2759182 * 2
def baseEnd_2759182 : Nat := 157420731025992102381751

theorem tailTrace_2759182 : CollatzResearch.WordTrace tailWord_2759182 prefixEnd_2759182 157420731025992102381751 := by
  unfold tailWord_2759182
  simp only [CollatzResearch.WordTrace]
  refine ⟨12579454386245289951763975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67090423393308213076074533 12579454386245289951763975)
  ·
    refine ⟨18869181579367934927645963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12579454386245289951763975 18869181579367934927645963)
    ·
      refine ⟨28303772369051902391468945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18869181579367934927645963 28303772369051902391468945)
      ·
        refine ⟨21227829276788926793601709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28303772369051902391468945 21227829276788926793601709)
        ·
          refine ⟨7960435978795847547600641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21227829276788926793601709 7960435978795847547600641)
          ·
            refine ⟨5970326984096885660700481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7960435978795847547600641 5970326984096885660700481)
            ·
              refine ⟨4477745238072664245525361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5970326984096885660700481 4477745238072664245525361)
              ·
                refine ⟨3358308928554498184144021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4477745238072664245525361 3358308928554498184144021)
                ·
                  refine ⟨157420731025992102381751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3358308928554498184144021 157420731025992102381751)
                  ·
                    rfl

theorem cell23_2759182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_2759182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759182 prefixEnd_2759182 := by exact prefixLift 2759182
  have htrace : WordTrace (prefixWord ++ tailWord_2759182) baseStart_2759182 baseEnd_2759182 := by
    simpa [prefixWord, tailWord_2759182, baseEnd_2759182] using wordTrace_append hprefix tailTrace_2759182
  have hstable : (prefixWord ++ tailWord_2759182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759182).length < 2 ^ (prefixWord ++ tailWord_2759182).sum := by decide
  have hdescent : baseEnd_2759182 < baseStart_2759182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759202 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 1, 5, 2]
def baseStart_2759202 : Nat := 118140960795 + 2759202 * 2 ^ 59
def prefixEnd_2759202 : Nat := 4983230072969 + 3 ^ 40 * 2759202 * 2
def baseEnd_2759202 : Nat := 1416796848847018843185667

theorem tailTrace_2759202 : CollatzResearch.WordTrace tailWord_2759202 prefixEnd_2759202 1416796848847018843185667 := by
  unfold tailWord_2759202
  simp only [CollatzResearch.WordTrace]
  refine ⟨25159091137472465757459965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67090909699926575353226573 25159091137472465757459965)
  ·
    refine ⟨9434659176552174659047487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25159091137472465757459965 9434659176552174659047487)
    ·
      refine ⟨14151988764828261988571231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9434659176552174659047487 14151988764828261988571231)
      ·
        refine ⟨21227983147242392982856847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14151988764828261988571231 21227983147242392982856847)
        ·
          refine ⟨31841974720863589474285271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21227983147242392982856847 31841974720863589474285271)
          ·
            refine ⟨47762962081295384211427907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31841974720863589474285271 47762962081295384211427907)
            ·
              refine ⟨71644443121943076317141861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47762962081295384211427907 71644443121943076317141861)
              ·
                refine ⟨13433333085364326809464099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71644443121943076317141861 13433333085364326809464099)
                ·
                  refine ⟨20149999628046490214196149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13433333085364326809464099 20149999628046490214196149)
                  ·
                    refine ⟨1889062465129358457580889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20149999628046490214196149 1889062465129358457580889)
                    ·
                      refine ⟨1416796848847018843185667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1889062465129358457580889 1416796848847018843185667)
                      ·
                        rfl

theorem cell23_2759202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_2759202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759202 prefixEnd_2759202 := by exact prefixLift 2759202
  have htrace : WordTrace (prefixWord ++ tailWord_2759202) baseStart_2759202 baseEnd_2759202 := by
    simpa [prefixWord, tailWord_2759202, baseEnd_2759202] using wordTrace_append hprefix tailTrace_2759202
  have hstable : (prefixWord ++ tailWord_2759202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759202).length < 2 ^ (prefixWord ++ tailWord_2759202).sum := by decide
  have hdescent : baseEnd_2759202 < baseStart_2759202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759225 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 1, 6]
def baseStart_2759225 : Nat := 118140960795 + 2759225 * 2 ^ 59
def prefixEnd_2759225 : Nat := 4983230072969 + 3 ^ 40 * 2759225 * 2
def baseEnd_2759225 : Nat := 472269552967357417732687

theorem tailTrace_2759225 : CollatzResearch.WordTrace tailWord_2759225 prefixEnd_2759225 472269552967357417732687 := by
  unfold tailWord_2759225
  simp only [CollatzResearch.WordTrace]
  refine ⟨100637203428806537957927129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67091468952537691971951419 100637203428806537957927129)
  ·
    refine ⟨75477902571604903468445347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100637203428806537957927129 75477902571604903468445347)
    ·
      refine ⟨113216853857407355202668021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75477902571604903468445347 113216853857407355202668021)
      ·
        refine ⟨10614080049131939550250127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113216853857407355202668021 10614080049131939550250127)
        ·
          refine ⟨15921120073697909325375191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10614080049131939550250127 15921120073697909325375191)
          ·
            refine ⟨23881680110546863988062787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15921120073697909325375191 23881680110546863988062787)
            ·
              refine ⟨35822520165820295982094181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23881680110546863988062787 35822520165820295982094181)
              ·
                refine ⟨6716722531091305496642659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35822520165820295982094181 6716722531091305496642659)
                ·
                  refine ⟨10075083796636958244963989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6716722531091305496642659 10075083796636958244963989)
                  ·
                    refine ⟨472269552967357417732687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10075083796636958244963989 472269552967357417732687)
                    ·
                      rfl

theorem cell23_2759225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 6].length) (baseStart_2759225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759225 prefixEnd_2759225 := by exact prefixLift 2759225
  have htrace : WordTrace (prefixWord ++ tailWord_2759225) baseStart_2759225 baseEnd_2759225 := by
    simpa [prefixWord, tailWord_2759225, baseEnd_2759225] using wordTrace_append hprefix tailTrace_2759225
  have hstable : (prefixWord ++ tailWord_2759225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759225).length < 2 ^ (prefixWord ++ tailWord_2759225).sum := by decide
  have hdescent : baseEnd_2759225 < baseStart_2759225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759226 : List Nat := [3, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3]
def baseStart_2759226 : Nat := 118140960795 + 2759226 * 2 ^ 59
def prefixEnd_2759226 : Nat := 4983230072969 + 3 ^ 40 * 2759226 * 2
def baseEnd_2759226 : Nat := 1416809172382726749285557

theorem tailTrace_2759226 : CollatzResearch.WordTrace tailWord_2759226 prefixEnd_2759226 1416809172382726749285557 := by
  unfold tailWord_2759226
  simp only [CollatzResearch.WordTrace]
  refine ⟨25159309975450728782178383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67091493267868610085809021 25159309975450728782178383)
  ·
    refine ⟨37738964963176093173267575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25159309975450728782178383 37738964963176093173267575)
    ·
      refine ⟨56608447444764139759901363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37738964963176093173267575 56608447444764139759901363)
      ·
        refine ⟨84912671167146209639852045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56608447444764139759901363 84912671167146209639852045)
        ·
          refine ⟨31842251687679828614944517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84912671167146209639852045 31842251687679828614944517)
          ·
            refine ⟨5970422191439967865302097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31842251687679828614944517 5970422191439967865302097)
            ·
              refine ⟨4477816643579975898976573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5970422191439967865302097 4477816643579975898976573)
              ·
                refine ⟨1679181241342490962116215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4477816643579975898976573 1679181241342490962116215)
                ·
                  refine ⟨2518771862013736443174323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1679181241342490962116215 2518771862013736443174323)
                  ·
                    refine ⟨3778157793020604664761485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2518771862013736443174323 3778157793020604664761485)
                    ·
                      refine ⟨1416809172382726749285557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3778157793020604664761485 1416809172382726749285557)
                      ·
                        rfl

theorem cell23_2759226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3].length) (baseStart_2759226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759226 prefixEnd_2759226 := by exact prefixLift 2759226
  have htrace : WordTrace (prefixWord ++ tailWord_2759226) baseStart_2759226 baseEnd_2759226 := by
    simpa [prefixWord, tailWord_2759226, baseEnd_2759226] using wordTrace_append hprefix tailTrace_2759226
  have hstable : (prefixWord ++ tailWord_2759226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759226).length < 2 ^ (prefixWord ++ tailWord_2759226).sum := by decide
  have hdescent : baseEnd_2759226 < baseStart_2759226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759229 : List Nat := [1, 4, 1, 3, 2, 1, 4, 1, 1, 5]
def baseStart_2759229 : Nat := 118140960795 + 2759229 * 2 ^ 59
def prefixEnd_2759229 : Nat := 4983230072969 + 3 ^ 40 * 2759229 * 2
def baseEnd_2759229 : Nat := 472270237608230079182681

theorem tailTrace_2759229 : CollatzResearch.WordTrace tailWord_2759229 prefixEnd_2759229 472270237608230079182681 := by
  unfold tailWord_2759229
  simp only [CollatzResearch.WordTrace]
  refine ⟨100637349320792046641072741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67091566213861364427381827 100637349320792046641072741)
  ·
    refine ⟨18869502997648508745201139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100637349320792046641072741 18869502997648508745201139)
    ·
      refine ⟨28304254496472763117801709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18869502997648508745201139 28304254496472763117801709)
      ·
        refine ⟨10614095436177286169175641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28304254496472763117801709 10614095436177286169175641)
        ·
          refine ⟨7960571577132964626881731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10614095436177286169175641 7960571577132964626881731)
          ·
            refine ⟨11940857365699446940322597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7960571577132964626881731 11940857365699446940322597)
            ·
              refine ⟨2238910756068646301310487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11940857365699446940322597 2238910756068646301310487)
              ·
                refine ⟨3358366134102969451965731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2238910756068646301310487 3358366134102969451965731)
                ·
                  refine ⟨5037549201154454177948597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3358366134102969451965731 5037549201154454177948597)
                  ·
                    refine ⟨472270237608230079182681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5037549201154454177948597 472270237608230079182681)
                    ·
                      rfl

theorem cell23_2759229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_2759229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759229 prefixEnd_2759229 := by exact prefixLift 2759229
  have htrace : WordTrace (prefixWord ++ tailWord_2759229) baseStart_2759229 baseEnd_2759229 := by
    simpa [prefixWord, tailWord_2759229, baseEnd_2759229] using wordTrace_append hprefix tailTrace_2759229
  have hstable : (prefixWord ++ tailWord_2759229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759229).length < 2 ^ (prefixWord ++ tailWord_2759229).sum := by decide
  have hdescent : baseEnd_2759229 < baseStart_2759229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759242 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 4, 4]
def baseStart_2759242 : Nat := 118140960795 + 2759242 * 2 ^ 59
def prefixEnd_2759242 : Nat := 4983230072969 + 3 ^ 40 * 2759242 * 2
def baseEnd_2759242 : Nat := 472272462691066228895161

theorem tailTrace_2759242 : CollatzResearch.WordTrace tailWord_2759242 prefixEnd_2759242 472272462691066228895161 := by
  unfold tailWord_2759242
  simp only [CollatzResearch.WordTrace]
  refine ⟨25159455867436237465323995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67091882313163299907530653 25159455867436237465323995)
  ·
    refine ⟨37739183801154356197985993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25159455867436237465323995 37739183801154356197985993)
    ·
      refine ⟨28304387850865767148489495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37739183801154356197985993 28304387850865767148489495)
      ·
        refine ⟨42456581776298650722734243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28304387850865767148489495 42456581776298650722734243)
        ·
          refine ⟨63684872664447976084101365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42456581776298650722734243 63684872664447976084101365)
          ·
            refine ⟨5970456812291997757884503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63684872664447976084101365 5970456812291997757884503)
            ·
              refine ⟨8955685218437996636826755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5970456812291997757884503 8955685218437996636826755)
              ·
                refine ⟨13433527827656994955240133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8955685218437996636826755 13433527827656994955240133)
                ·
                  refine ⟨2518786467685686554107525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13433527827656994955240133 2518786467685686554107525)
                  ·
                    refine ⟨472272462691066228895161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2518786467685686554107525 472272462691066228895161)
                    ·
                      rfl

theorem cell23_2759242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_2759242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759242 prefixEnd_2759242 := by exact prefixLift 2759242
  have htrace : WordTrace (prefixWord ++ tailWord_2759242) baseStart_2759242 baseEnd_2759242 := by
    simpa [prefixWord, tailWord_2759242, baseEnd_2759242] using wordTrace_append hprefix tailTrace_2759242
  have hstable : (prefixWord ++ tailWord_2759242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759242).length < 2 ^ (prefixWord ++ tailWord_2759242).sum := by decide
  have hdescent : baseEnd_2759242 < baseStart_2759242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759249 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 3, 2, 2]
def baseStart_2759249 : Nat := 118140960795 + 2759249 * 2 ^ 59
def prefixEnd_2759249 : Nat := 4983230072969 + 3 ^ 40 * 2759249 * 2
def baseEnd_2759249 : Nat := 1416820982437780159297951

theorem tailTrace_2759249 : CollatzResearch.WordTrace tailWord_2759249 prefixEnd_2759249 1416820982437780159297951 := by
  unfold tailWord_2759249
  simp only [CollatzResearch.WordTrace]
  refine ⟨100638078780719590056800801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67092052520479726704533867 100638078780719590056800801)
  ·
    refine ⟨75478559085539692542600601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100638078780719590056800801 75478559085539692542600601)
    ·
      refine ⟨56608919314154769406950451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75478559085539692542600601 56608919314154769406950451)
      ·
        refine ⟨84913378971232154110425677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56608919314154769406950451 84913378971232154110425677)
        ·
          refine ⟨31842517114212057791409629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84913378971232154110425677 31842517114212057791409629)
          ·
            refine ⟨11940943917829521671778611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31842517114212057791409629 11940943917829521671778611)
            ·
              refine ⟨17911415876744282507667917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11940943917829521671778611 17911415876744282507667917)
              ·
                refine ⟨6716780953779105940375469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17911415876744282507667917 6716780953779105940375469)
                ·
                  refine ⟨2518792857667164727640801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6716780953779105940375469 2518792857667164727640801)
                  ·
                    refine ⟨1889094643250373545730601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2518792857667164727640801 1889094643250373545730601)
                    ·
                      refine ⟨1416820982437780159297951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1889094643250373545730601 1416820982437780159297951)
                      ·
                        rfl

theorem cell23_2759249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 2, 2].length) (baseStart_2759249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759249 prefixEnd_2759249 := by exact prefixLift 2759249
  have htrace : WordTrace (prefixWord ++ tailWord_2759249) baseStart_2759249 baseEnd_2759249 := by
    simpa [prefixWord, tailWord_2759249, baseEnd_2759249] using wordTrace_append hprefix tailTrace_2759249
  have hstable : (prefixWord ++ tailWord_2759249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759249).length < 2 ^ (prefixWord ++ tailWord_2759249).sum := by decide
  have hdescent : baseEnd_2759249 < baseStart_2759249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759252 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_2759252 : Nat := 118140960795 + 2759252 * 2 ^ 59
def prefixEnd_2759252 : Nat := 4983230072969 + 3 ^ 40 * 2759252 * 2
def baseEnd_2759252 : Nat := 1416822522879743647560437

theorem tailTrace_2759252 : CollatzResearch.WordTrace tailWord_2759252 prefixEnd_2759252 1416822522879743647560437 := by
  unfold tailWord_2759252
  simp only [CollatzResearch.WordTrace]
  refine ⟨50319094099854360784580005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67092125466472481046106673 50319094099854360784580005)
  ·
    refine ⟨9434830143722692647108751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50319094099854360784580005 9434830143722692647108751)
    ·
      refine ⟨14152245215584038970663127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9434830143722692647108751 14152245215584038970663127)
      ·
        refine ⟨21228367823376058455994691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14152245215584038970663127 21228367823376058455994691)
        ·
          refine ⟨31842551735064087683992037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21228367823376058455994691 31842551735064087683992037)
          ·
            refine ⟨5970478450324516440748507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31842551735064087683992037 5970478450324516440748507)
            ·
              refine ⟨8955717675486774661122761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5970478450324516440748507 8955717675486774661122761)
              ·
                refine ⟨6716788256615080995842071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8955717675486774661122761 6716788256615080995842071)
                ·
                  refine ⟨10075182384922621493763107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6716788256615080995842071 10075182384922621493763107)
                  ·
                    refine ⟨15112773577383932240644661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10075182384922621493763107 15112773577383932240644661)
                    ·
                      refine ⟨1416822522879743647560437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15112773577383932240644661 1416822522879743647560437)
                      ·
                        rfl

theorem cell23_2759252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_2759252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759252 prefixEnd_2759252 := by exact prefixLift 2759252
  have htrace : WordTrace (prefixWord ++ tailWord_2759252) baseStart_2759252 baseEnd_2759252 := by
    simpa [prefixWord, tailWord_2759252, baseEnd_2759252] using wordTrace_append hprefix tailTrace_2759252
  have hstable : (prefixWord ++ tailWord_2759252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759252).length < 2 ^ (prefixWord ++ tailWord_2759252).sum := by decide
  have hdescent : baseEnd_2759252 < baseStart_2759252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759272 : List Nat := [2, 1, 4, 3, 2, 1, 1, 9]
def baseStart_2759272 : Nat := 118140960795 + 2759272 * 2 ^ 59
def prefixEnd_2759272 : Nat := 4983230072969 + 3 ^ 40 * 2759272 * 2
def baseEnd_2759272 : Nat := 52475288610845687752235

theorem tailTrace_2759272 : CollatzResearch.WordTrace tailWord_2759272 prefixEnd_2759272 52475288610845687752235 := by
  unfold tailWord_2759272
  simp only [CollatzResearch.WordTrace]
  refine ⟨50319458829818132492444035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67092611773090843323258713 50319458829818132492444035)
  ·
    refine ⟨75479188244727198738666053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50319458829818132492444035 75479188244727198738666053)
    ·
      refine ⟨14152347795886349763499885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75479188244727198738666053 14152347795886349763499885)
      ·
        refine ⟨5307130423457381161312457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14152347795886349763499885 5307130423457381161312457)
        ·
          refine ⟨3980347817593035870984343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5307130423457381161312457 3980347817593035870984343)
          ·
            refine ⟨5970521726389553806476515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3980347817593035870984343 5970521726389553806476515)
            ·
              refine ⟨8955782589584330709714773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5970521726389553806476515 8955782589584330709714773)
              ·
                refine ⟨52475288610845687752235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8955782589584330709714773 52475288610845687752235)
                ·
                  rfl

theorem cell23_2759272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 9].length) (baseStart_2759272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759272 prefixEnd_2759272 := by exact prefixLift 2759272
  have htrace : WordTrace (prefixWord ++ tailWord_2759272) baseStart_2759272 baseEnd_2759272 := by
    simpa [prefixWord, tailWord_2759272, baseEnd_2759272] using wordTrace_append hprefix tailTrace_2759272
  have hstable : (prefixWord ++ tailWord_2759272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759272).length < 2 ^ (prefixWord ++ tailWord_2759272).sum := by decide
  have hdescent : baseEnd_2759272 < baseStart_2759272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759300 : List Nat := [2, 3, 2, 1, 3, 2, 3, 2, 1, 2, 2]
def baseStart_2759300 : Nat := 118140960795 + 2759300 * 2 ^ 59
def prefixEnd_2759300 : Nat := 4983230072969 + 3 ^ 40 * 2759300 * 2
def baseEnd_2759300 : Nat := 1416847169951159459760217

theorem tailTrace_2759300 : CollatzResearch.WordTrace tailWord_2759300 prefixEnd_2759300 1416847169951159459760217 := by
  unfold tailWord_2759300
  simp only [CollatzResearch.WordTrace]
  refine ⟨50319969451767412883453677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67093292602356550511271569 50319969451767412883453677)
  ·
    refine ⟨18869988544412779831295129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50319969451767412883453677 18869988544412779831295129)
    ·
      refine ⟨14152491408309584873471347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18869988544412779831295129 14152491408309584873471347)
      ·
        refine ⟨21228737112464377310207021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14152491408309584873471347 21228737112464377310207021)
        ·
          refine ⟨7960776417174141491327633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21228737112464377310207021 7960776417174141491327633)
          ·
            refine ⟨5970582312880606118495725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7960776417174141491327633 5970582312880606118495725)
            ·
              refine ⟨2238968367330227294435897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5970582312880606118495725 2238968367330227294435897)
              ·
                refine ⟨1679226275497670470826923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2238968367330227294435897 1679226275497670470826923)
                ·
                  refine ⟨2518839413246505706240385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1679226275497670470826923 2518839413246505706240385)
                  ·
                    refine ⟨1889129559934879279680289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2518839413246505706240385 1889129559934879279680289)
                    ·
                      refine ⟨1416847169951159459760217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1889129559934879279680289 1416847169951159459760217)
                      ·
                        rfl

theorem cell23_2759300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_2759300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759300 prefixEnd_2759300 := by exact prefixLift 2759300
  have htrace : WordTrace (prefixWord ++ tailWord_2759300) baseStart_2759300 baseEnd_2759300 := by
    simpa [prefixWord, tailWord_2759300, baseEnd_2759300] using wordTrace_append hprefix tailTrace_2759300
  have hstable : (prefixWord ++ tailWord_2759300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759300).length < 2 ^ (prefixWord ++ tailWord_2759300).sum := by decide
  have hdescent : baseEnd_2759300 < baseStart_2759300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759305 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 2, 3, 4]
def baseStart_2759305 : Nat := 118140960795 + 2759305 * 2 ^ 59
def prefixEnd_2759305 : Nat := 4983230072969 + 3 ^ 40 * 2759305 * 2
def baseEnd_2759305 : Nat := 1416849737354431940197693

theorem tailTrace_2759305 : CollatzResearch.WordTrace tailWord_2759305 prefixEnd_2759305 1416849737354431940197693 := by
  unfold tailWord_2759305
  simp only [CollatzResearch.WordTrace]
  refine ⟨100640121268516711620839369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67093414179011141080559579 100640121268516711620839369)
  ·
    refine ⟨75480090951387533715629527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100640121268516711620839369 75480090951387533715629527)
    ·
      refine ⟨113220136427081300573444291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75480090951387533715629527 113220136427081300573444291)
      ·
        refine ⟨169830204640621950860166437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113220136427081300573444291 169830204640621950860166437)
        ·
          refine ⟨31843163370116615786281207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169830204640621950860166437 31843163370116615786281207)
          ·
            refine ⟨47764745055174923679421811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31843163370116615786281207 47764745055174923679421811)
            ·
              refine ⟨71647117582762385519132717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47764745055174923679421811 71647117582762385519132717)
              ·
                refine ⟨26867669093535894569674769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71647117582762385519132717 26867669093535894569674769)
                ·
                  refine ⟨20150751820151920927256077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26867669093535894569674769 20150751820151920927256077)
                  ·
                    refine ⟨7556531932556970347721029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20150751820151920927256077 7556531932556970347721029)
                    ·
                      refine ⟨1416849737354431940197693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7556531932556970347721029 1416849737354431940197693)
                      ·
                        rfl

theorem cell23_2759305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_2759305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759305 prefixEnd_2759305 := by exact prefixLift 2759305
  have htrace : WordTrace (prefixWord ++ tailWord_2759305) baseStart_2759305 baseEnd_2759305 := by
    simpa [prefixWord, tailWord_2759305, baseEnd_2759305] using wordTrace_append hprefix tailTrace_2759305
  have hstable : (prefixWord ++ tailWord_2759305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759305).length < 2 ^ (prefixWord ++ tailWord_2759305).sum := by decide
  have hdescent : baseEnd_2759305 < baseStart_2759305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759326 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_2759326 : Nat := 118140960795 + 2759326 * 2 ^ 59
def prefixEnd_2759326 : Nat := 4983230072969 + 3 ^ 40 * 2759326 * 2
def baseEnd_2759326 : Nat := 1416860520448176358035097

theorem tailTrace_2759326 : CollatzResearch.WordTrace tailWord_2759326 prefixEnd_2759326 1416860520448176358035097 := by
  unfold tailWord_2759326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12580110900180079025919229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67093924800960421471569221 12580110900180079025919229)
  ·
    refine ⟨4717541587567529634719711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12580110900180079025919229 4717541587567529634719711)
    ·
      refine ⟨7076312381351294452079567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4717541587567529634719711 7076312381351294452079567)
      ·
        refine ⟨10614468572026941678119351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7076312381351294452079567 10614468572026941678119351)
        ·
          refine ⟨15921702858040412517179027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10614468572026941678119351 15921702858040412517179027)
          ·
            refine ⟨23882554287060618775768541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15921702858040412517179027 23882554287060618775768541)
            ·
              refine ⟨8955957857647732040913203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23882554287060618775768541 8955957857647732040913203)
              ·
                refine ⟨13433936786471598061369805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8955957857647732040913203 13433936786471598061369805)
                ·
                  refine ⟨5037726294926849273013677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13433936786471598061369805 5037726294926849273013677)
                  ·
                    refine ⟨1889147360597568477380129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5037726294926849273013677 1889147360597568477380129)
                    ·
                      refine ⟨1416860520448176358035097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1889147360597568477380129 1416860520448176358035097)
                      ·
                        rfl

theorem cell23_2759326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_2759326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759326 prefixEnd_2759326 := by exact prefixLift 2759326
  have htrace : WordTrace (prefixWord ++ tailWord_2759326) baseStart_2759326 baseEnd_2759326 := by
    simpa [prefixWord, tailWord_2759326, baseEnd_2759326] using wordTrace_append hprefix tailTrace_2759326
  have hstable : (prefixWord ++ tailWord_2759326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759326).length < 2 ^ (prefixWord ++ tailWord_2759326).sum := by decide
  have hdescent : baseEnd_2759326 < baseStart_2759326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759350 : List Nat := [5, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_2759350 : Nat := 118140960795 + 2759350 * 2 ^ 59
def prefixEnd_2759350 : Nat := 4983230072969 + 3 ^ 40 * 2759350 * 2
def baseEnd_2759350 : Nat := 1416872843983884264134987

theorem tailTrace_2759350 : CollatzResearch.WordTrace tailWord_2759350 prefixEnd_2759350 1416872843983884264134987 := by
  unfold tailWord_2759350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6290110159584605269139219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67094508368902456204151669 6290110159584605269139219)
  ·
    refine ⟨9435165239376907903708829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6290110159584605269139219 9435165239376907903708829)
    ·
      refine ⟨3538186964766340463890811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9435165239376907903708829 3538186964766340463890811)
      ·
        refine ⟨5307280447149510695836217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3538186964766340463890811 5307280447149510695836217)
        ·
          refine ⟨3980460335362133021877163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5307280447149510695836217 3980460335362133021877163)
          ·
            refine ⟨5970690503043199532815745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3980460335362133021877163 5970690503043199532815745)
            ·
              refine ⟨4478017877282399649611809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5970690503043199532815745 4478017877282399649611809)
              ·
                refine ⟨3358513407961799737208857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4478017877282399649611809 3358513407961799737208857)
                ·
                  refine ⟨2518885055971349802906643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3358513407961799737208857 2518885055971349802906643)
                  ·
                    refine ⟨3778327583957024704359965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2518885055971349802906643 3778327583957024704359965)
                    ·
                      refine ⟨1416872843983884264134987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3778327583957024704359965 1416872843983884264134987)
                      ·
                        rfl

theorem cell23_2759350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_2759350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759350 prefixEnd_2759350 := by exact prefixLift 2759350
  have htrace : WordTrace (prefixWord ++ tailWord_2759350) baseStart_2759350 baseEnd_2759350 := by
    simpa [prefixWord, tailWord_2759350, baseEnd_2759350] using wordTrace_append hprefix tailTrace_2759350
  have hstable : (prefixWord ++ tailWord_2759350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759350).length < 2 ^ (prefixWord ++ tailWord_2759350).sum := by decide
  have hdescent : baseEnd_2759350 < baseStart_2759350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759413 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 7]
def baseStart_2759413 : Nat := 118140960795 + 2759413 * 2 ^ 59
def prefixEnd_2759413 : Nat := 4983230072969 + 3 ^ 40 * 2759413 * 2
def baseEnd_2759413 : Nat := 157433910362790835294133

theorem tailTrace_2759413 : CollatzResearch.WordTrace tailWord_2759413 prefixEnd_2759413 157433910362790835294133 := by
  unfold tailWord_2759413
  simp only [CollatzResearch.WordTrace]
  refine ⟨100644060352125446065770893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67096040234750297377180595 100644060352125446065770893)
  ·
    refine ⟨37741522632047042274664085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100644060352125446065770893 37741522632047042274664085)
    ·
      refine ⟨1769133873377205106624879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37741522632047042274664085 1769133873377205106624879)
      ·
        refine ⟨2653700810065807659937319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1769133873377205106624879 2653700810065807659937319)
        ·
          refine ⟨3980551215098711489905979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653700810065807659937319 3980551215098711489905979)
          ·
            refine ⟨5970826822648067234858969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3980551215098711489905979 5970826822648067234858969)
            ·
              refine ⟨4478120116986050426144227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5970826822648067234858969 4478120116986050426144227)
              ·
                refine ⟨6717180175479075639216341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4478120116986050426144227 6717180175479075639216341)
                ·
                  refine ⟨157433910362790835294133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6717180175479075639216341 157433910362790835294133)
                  ·
                    rfl

theorem cell23_2759413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 7].length) (baseStart_2759413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759413 prefixEnd_2759413 := by exact prefixLift 2759413
  have htrace : WordTrace (prefixWord ++ tailWord_2759413) baseStart_2759413 baseEnd_2759413 := by
    simpa [prefixWord, tailWord_2759413, baseEnd_2759413] using wordTrace_append hprefix tailTrace_2759413
  have hstable : (prefixWord ++ tailWord_2759413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759413).length < 2 ^ (prefixWord ++ tailWord_2759413).sum := by decide
  have hdescent : baseEnd_2759413 < baseStart_2759413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759452 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 8]
def baseStart_2759452 : Nat := 118140960795 + 2759452 * 2 ^ 59
def prefixEnd_2759452 : Nat := 4983230072969 + 3 ^ 40 * 2759452 * 2
def baseEnd_2759452 : Nat := 157436135445626985006613

theorem tailTrace_2759452 : CollatzResearch.WordTrace tailWord_2759452 prefixEnd_2759452 157436135445626985006613 := by
  unfold tailWord_2759452
  simp only [CollatzResearch.WordTrace]
  refine ⟨50322741399492077863220305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67096988532656103817627073 50322741399492077863220305)
  ·
    refine ⟨37742056049619058397415229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50322741399492077863220305 37742056049619058397415229)
    ·
      refine ⟨14153271018607146899030711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37742056049619058397415229 14153271018607146899030711)
      ·
        refine ⟨21229906527910720348546067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14153271018607146899030711 21229906527910720348546067)
        ·
          refine ⟨31844859791866080522819101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21229906527910720348546067 31844859791866080522819101)
          ·
            refine ⟨11941822421949780196057163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31844859791866080522819101 11941822421949780196057163)
            ·
              refine ⟨17912733632924670294085745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11941822421949780196057163 17912733632924670294085745)
              ·
                refine ⟨13434550224693502720564309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17912733632924670294085745 13434550224693502720564309)
                ·
                  refine ⟨157436135445626985006613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13434550224693502720564309 157436135445626985006613)
                  ·
                    rfl

theorem cell23_2759452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 8].length) (baseStart_2759452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759452 prefixEnd_2759452 := by exact prefixLift 2759452
  have htrace : WordTrace (prefixWord ++ tailWord_2759452) baseStart_2759452 baseEnd_2759452 := by
    simpa [prefixWord, tailWord_2759452, baseEnd_2759452] using wordTrace_append hprefix tailTrace_2759452
  have hstable : (prefixWord ++ tailWord_2759452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759452).length < 2 ^ (prefixWord ++ tailWord_2759452).sum := by decide
  have hdescent : baseEnd_2759452 < baseStart_2759452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759473 : List Nat := [1, 2, 2, 3, 2, 1, 5, 2, 1, 4]
def baseStart_2759473 : Nat := 118140960795 + 2759473 * 2 ^ 59
def prefixEnd_2759473 : Nat := 4983230072969 + 3 ^ 40 * 2759473 * 2
def baseEnd_2759473 : Nat := 472312000701462427632307

theorem tailTrace_2759473 : CollatzResearch.WordTrace tailWord_2759473 prefixEnd_2759473 472312000701462427632307 := by
  unfold tailWord_2759473
  simp only [CollatzResearch.WordTrace]
  refine ⟨100646248731908076312955073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67097499154605384208636715 100646248731908076312955073)
  ·
    refine ⟨75484686548931057234716305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100646248731908076312955073 75484686548931057234716305)
    ·
      refine ⟨56613514911698292926037229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75484686548931057234716305 56613514911698292926037229)
      ·
        refine ⟨21230068091886859847263961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56613514911698292926037229 21230068091886859847263961)
        ·
          refine ⟨15922551068915144885447971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21230068091886859847263961 15922551068915144885447971)
          ·
            refine ⟨23883826603372717328171957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15922551068915144885447971 23883826603372717328171957)
            ·
              refine ⟨2239108744066192249516121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23883826603372717328171957 2239108744066192249516121)
              ·
                refine ⟨1679331558049644187137091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2239108744066192249516121 1679331558049644187137091)
                ·
                  refine ⟨2518997337074466280705637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1679331558049644187137091 2518997337074466280705637)
                  ·
                    refine ⟨472312000701462427632307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2518997337074466280705637 472312000701462427632307)
                    ·
                      rfl

theorem cell23_2759473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 1, 4].length) (baseStart_2759473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759473 prefixEnd_2759473 := by exact prefixLift 2759473
  have htrace : WordTrace (prefixWord ++ tailWord_2759473) baseStart_2759473 baseEnd_2759473 := by
    simpa [prefixWord, tailWord_2759473, baseEnd_2759473] using wordTrace_append hprefix tailTrace_2759473
  have hstable : (prefixWord ++ tailWord_2759473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759473).length < 2 ^ (prefixWord ++ tailWord_2759473).sum := by decide
  have hdescent : baseEnd_2759473 < baseStart_2759473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759486 : List Nat := [4, 2, 1, 2, 3, 1, 1, 3, 6]
def baseStart_2759486 : Nat := 118140960795 + 2759486 * 2 ^ 59
def prefixEnd_2759486 : Nat := 4983230072969 + 3 ^ 40 * 2759486 * 2
def baseEnd_2759486 : Nat := 157438075261432859114929

theorem tailTrace_2759486 : CollatzResearch.WordTrace tailWord_2759486 prefixEnd_2759486 157438075261432859114929 := by
  unfold tailWord_2759486
  simp only [CollatzResearch.WordTrace]
  refine ⟨12580840360107622441647289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67097815253907319688785541 12580840360107622441647289)
  ·
    refine ⟨9435630270080716831235467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12580840360107622441647289 9435630270080716831235467)
    ·
      refine ⟨14153445405121075246853201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9435630270080716831235467 14153445405121075246853201)
      ·
        refine ⟨10615084053840806435139901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14153445405121075246853201 10615084053840806435139901)
        ·
          refine ⟨3980656520190302413177463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10615084053840806435139901 3980656520190302413177463)
          ·
            refine ⟨5970984780285453619766195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3980656520190302413177463 5970984780285453619766195)
            ·
              refine ⟨8956477170428180429649293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5970984780285453619766195 8956477170428180429649293)
              ·
                refine ⟨3358678938910567661118485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8956477170428180429649293 3358678938910567661118485)
                ·
                  refine ⟨157438075261432859114929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3358678938910567661118485 157438075261432859114929)
                  ·
                    rfl

theorem cell23_2759486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_2759486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759486 prefixEnd_2759486 := by exact prefixLift 2759486
  have htrace : WordTrace (prefixWord ++ tailWord_2759486) baseStart_2759486 baseEnd_2759486 := by
    simpa [prefixWord, tailWord_2759486, baseEnd_2759486] using wordTrace_append hprefix tailTrace_2759486
  have hstable : (prefixWord ++ tailWord_2759486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759486).length < 2 ^ (prefixWord ++ tailWord_2759486).sum := by decide
  have hdescent : baseEnd_2759486 < baseStart_2759486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759539 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 3]
def baseStart_2759539 : Nat := 118140960795 + 2759539 * 2 ^ 59
def prefixEnd_2759539 : Nat := 4983230072969 + 3 ^ 40 * 2759539 * 2
def baseEnd_2759539 : Nat := 1416969891827584024671617

theorem tailTrace_2759539 : CollatzResearch.WordTrace tailWord_2759539 prefixEnd_2759539 1416969891827584024671617 := by
  unfold tailWord_2759539
  simp only [CollatzResearch.WordTrace]
  refine ⟨100648655949668969584857671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67099103966445979723238447 100648655949668969584857671)
  ·
    refine ⟨150972983924503454377286507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100648655949668969584857671 150972983924503454377286507)
    ·
      refine ⟨226459475886755181565929761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150972983924503454377286507 226459475886755181565929761)
      ·
        refine ⟨169844606915066386174447321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226459475886755181565929761 169844606915066386174447321)
        ·
          refine ⟨127383455186299789630835491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169844606915066386174447321 127383455186299789630835491)
          ·
            refine ⟨191075182779449684446253237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127383455186299789630835491 191075182779449684446253237)
            ·
              refine ⟨17913298385573407916836241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191075182779449684446253237 17913298385573407916836241)
              ·
                refine ⟨13434973789180055937627181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17913298385573407916836241 13434973789180055937627181)
                ·
                  refine ⟨5038115170942520976610193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13434973789180055937627181 5038115170942520976610193)
                  ·
                    refine ⟨3778586378206890732457645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5038115170942520976610193 3778586378206890732457645)
                    ·
                      refine ⟨1416969891827584024671617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3778586378206890732457645 1416969891827584024671617)
                      ·
                        rfl

theorem cell23_2759539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 3].length) (baseStart_2759539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759539 prefixEnd_2759539 := by exact prefixLift 2759539
  have htrace : WordTrace (prefixWord ++ tailWord_2759539) baseStart_2759539 baseEnd_2759539 := by
    simpa [prefixWord, tailWord_2759539, baseEnd_2759539] using wordTrace_append hprefix tailTrace_2759539
  have hstable : (prefixWord ++ tailWord_2759539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759539).length < 2 ^ (prefixWord ++ tailWord_2759539).sum := by decide
  have hdescent : baseEnd_2759539 < baseStart_2759539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759549 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_2759549 : Nat := 118140960795 + 2759549 * 2 ^ 59
def prefixEnd_2759549 : Nat := 4983230072969 + 3 ^ 40 * 2759549 * 2
def baseEnd_2759549 : Nat := 1416975026634128985546571

theorem tailTrace_2759549 : CollatzResearch.WordTrace tailWord_2759549 prefixEnd_2759549 1416975026634128985546571 := by
  unfold tailWord_2759549
  simp only [CollatzResearch.WordTrace]
  refine ⟨100649020679632741292721701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67099347119755160861814467 100649020679632741292721701)
  ·
    refine ⟨18871691377431138992385319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100649020679632741292721701 18871691377431138992385319)
    ·
      refine ⟨28307537066146708488577979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18871691377431138992385319 28307537066146708488577979)
      ·
        refine ⟨42461305599220062732866969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28307537066146708488577979 42461305599220062732866969)
        ·
          refine ⟨31845979199415047049650227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42461305599220062732866969 31845979199415047049650227)
          ·
            refine ⟨47768968799122570574475341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31845979199415047049650227 47768968799122570574475341)
            ·
              refine ⟨17913363299670963965428253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47768968799122570574475341 17913363299670963965428253)
              ·
                refine ⟨6717511237376611487035595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17913363299670963965428253 6717511237376611487035595)
                ·
                  refine ⟨10076266856064917230553393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6717511237376611487035595 10076266856064917230553393)
                  ·
                    refine ⟨7557200142048687922915045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10076266856064917230553393 7557200142048687922915045)
                    ·
                      refine ⟨1416975026634128985546571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7557200142048687922915045 1416975026634128985546571)
                      ·
                        rfl

theorem cell23_2759549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_2759549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759549 prefixEnd_2759549 := by exact prefixLift 2759549
  have htrace : WordTrace (prefixWord ++ tailWord_2759549) baseStart_2759549 baseEnd_2759549 := by
    simpa [prefixWord, tailWord_2759549, baseEnd_2759549] using wordTrace_append hprefix tailTrace_2759549
  have hstable : (prefixWord ++ tailWord_2759549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759549).length < 2 ^ (prefixWord ++ tailWord_2759549).sum := by decide
  have hdescent : baseEnd_2759549 < baseStart_2759549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759556 : List Nat := [2, 3, 2, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_2759556 : Nat := 118140960795 + 2759556 * 2 ^ 59
def prefixEnd_2759556 : Nat := 4983230072969 + 3 ^ 40 * 2759556 * 2
def baseEnd_2759556 : Nat := 1416978620998710458159039

theorem tailTrace_2759556 : CollatzResearch.WordTrace tailWord_2759556 prefixEnd_2759556 1416978620998710458159039 := by
  unfold tailWord_2759556
  simp only [CollatzResearch.WordTrace]
  refine ⟨50324637995303690744113261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67099517327071587658817681 50324637995303690744113261)
  ·
    refine ⟨18871739248238884029042473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50324637995303690744113261 18871739248238884029042473)
    ·
      refine ⟨14153804436179163021781855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18871739248238884029042473 14153804436179163021781855)
      ·
        refine ⟨21230706654268744532672783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14153804436179163021781855 21230706654268744532672783)
        ·
          refine ⟨31846059981403116799009175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21230706654268744532672783 31846059981403116799009175)
          ·
            refine ⟨47769089972104675198513763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31846059981403116799009175 47769089972104675198513763)
            ·
              refine ⟨71653634958157012797770645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47769089972104675198513763 71653634958157012797770645)
              ·
                refine ⟨3358764138663609974895499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71653634958157012797770645 3358764138663609974895499)
                ·
                  refine ⟨5038146207995414962343249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3358764138663609974895499 5038146207995414962343249)
                  ·
                    refine ⟨3778609655996561221757437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5038146207995414962343249 3778609655996561221757437)
                    ·
                      refine ⟨1416978620998710458159039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3778609655996561221757437 1416978620998710458159039)
                      ·
                        rfl

theorem cell23_2759556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_2759556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759556 prefixEnd_2759556 := by exact prefixLift 2759556
  have htrace : WordTrace (prefixWord ++ tailWord_2759556) baseStart_2759556 baseEnd_2759556 := by
    simpa [prefixWord, tailWord_2759556, baseEnd_2759556] using wordTrace_append hprefix tailTrace_2759556
  have hstable : (prefixWord ++ tailWord_2759556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759556).length < 2 ^ (prefixWord ++ tailWord_2759556).sum := by decide
  have hdescent : baseEnd_2759556 < baseStart_2759556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759573 : List Nat := [1, 3, 2, 1, 1, 4, 4, 1, 1, 2, 3]
def baseStart_2759573 : Nat := 118140960795 + 2759573 * 2 ^ 59
def prefixEnd_2759573 : Nat := 4983230072969 + 3 ^ 40 * 2759573 * 2
def baseEnd_2759573 : Nat := 1416987350169836891646461

theorem tailTrace_2759573 : CollatzResearch.WordTrace tailWord_2759573 prefixEnd_2759573 1416987350169836891646461 := by
  unfold tailWord_2759573
  simp only [CollatzResearch.WordTrace]
  refine ⟨100649896031545793391595373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67099930687697195594396915 100649896031545793391595373)
  ·
    refine ⟨37743711011829672521848265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100649896031545793391595373 37743711011829672521848265)
    ·
      refine ⟨28307783258872254391386199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37743711011829672521848265 28307783258872254391386199)
      ·
        refine ⟨42461674888308381587079299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28307783258872254391386199 42461674888308381587079299)
        ·
          refine ⟨63692512332462572380618949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42461674888308381587079299 63692512332462572380618949)
          ·
            refine ⟨11942346062336732321366053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63692512332462572380618949 11942346062336732321366053)
            ·
              refine ⟨2239189886688137310256135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11942346062336732321366053 2239189886688137310256135)
              ·
                refine ⟨3358784830032205965384203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2239189886688137310256135 3358784830032205965384203)
                ·
                  refine ⟨5038177245048308948076305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3358784830032205965384203 5038177245048308948076305)
                  ·
                    refine ⟨3778632933786231711057229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5038177245048308948076305 3778632933786231711057229)
                    ·
                      refine ⟨1416987350169836891646461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3778632933786231711057229 1416987350169836891646461)
                      ·
                        rfl

theorem cell23_2759573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_2759573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759573 prefixEnd_2759573 := by exact prefixLift 2759573
  have htrace : WordTrace (prefixWord ++ tailWord_2759573) baseStart_2759573 baseEnd_2759573 := by
    simpa [prefixWord, tailWord_2759573, baseEnd_2759573] using wordTrace_append hprefix tailTrace_2759573
  have hstable : (prefixWord ++ tailWord_2759573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759573).length < 2 ^ (prefixWord ++ tailWord_2759573).sum := by decide
  have hdescent : baseEnd_2759573 < baseStart_2759573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759580 : List Nat := [2, 2, 3, 3, 2, 2, 1, 2, 2, 4]
def baseStart_2759580 : Nat := 118140960795 + 2759580 * 2 ^ 59
def prefixEnd_2759580 : Nat := 4983230072969 + 3 ^ 40 * 2759580 * 2
def baseEnd_2759580 : Nat := 472330314844806121419643

theorem tailTrace_2759580 : CollatzResearch.WordTrace tailWord_2759580 prefixEnd_2759580 472330314844806121419643 := by
  unfold tailWord_2759580
  simp only [CollatzResearch.WordTrace]
  refine ⟨50325075671260216793550097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67100100895013622391400129 50325075671260216793550097)
  ·
    refine ⟨37743806753445162595162573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50325075671260216793550097 37743806753445162595162573)
    ·
      refine ⟨14153927532541935973185965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37743806753445162595162573 14153927532541935973185965)
      ·
        refine ⟨5307722824703225989944737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14153927532541935973185965 5307722824703225989944737)
        ·
          refine ⟨3980792118527419492458553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5307722824703225989944737 3980792118527419492458553)
          ·
            refine ⟨2985594088895564619343915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3980792118527419492458553 2985594088895564619343915)
            ·
              refine ⟨4478391133343346929015873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2985594088895564619343915 4478391133343346929015873)
              ·
                refine ⟨3358793350007510196761905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4478391133343346929015873 3358793350007510196761905)
                ·
                  refine ⟨2519095012505632647571429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3358793350007510196761905 2519095012505632647571429)
                  ·
                    refine ⟨472330314844806121419643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2519095012505632647571429 472330314844806121419643)
                    ·
                      rfl

theorem cell23_2759580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_2759580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759580 prefixEnd_2759580 := by exact prefixLift 2759580
  have htrace : WordTrace (prefixWord ++ tailWord_2759580) baseStart_2759580 baseEnd_2759580 := by
    simpa [prefixWord, tailWord_2759580, baseEnd_2759580] using wordTrace_append hprefix tailTrace_2759580
  have hstable : (prefixWord ++ tailWord_2759580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759580).length < 2 ^ (prefixWord ++ tailWord_2759580).sum := by decide
  have hdescent : baseEnd_2759580 < baseStart_2759580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759597 : List Nat := [1, 5, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_2759597 : Nat := 118140960795 + 2759597 * 2 ^ 59
def prefixEnd_2759597 : Nat := 4983230072969 + 3 ^ 40 * 2759597 * 2
def baseEnd_2759597 : Nat := 472333224568514932582117

theorem tailTrace_2759597 : CollatzResearch.WordTrace tailWord_2759597 prefixEnd_2759597 472333224568514932582117 := by
  unfold tailWord_2759597
  simp only [CollatzResearch.WordTrace]
  refine ⟨100650771383458845490469045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67100514255639230326979363 100650771383458845490469045)
  ·
    refine ⟨9436009817199266764731473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100650771383458845490469045 9436009817199266764731473)
    ·
      refine ⟨7077007362899450073548605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9436009817199266764731473 7077007362899450073548605)
      ·
        refine ⟨2653877761087293777580727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7077007362899450073548605 2653877761087293777580727)
        ·
          refine ⟨3980816641630940666371091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653877761087293777580727 3980816641630940666371091)
          ·
            refine ⟨5971224962446410999556637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3980816641630940666371091 5971224962446410999556637)
            ·
              refine ⟨2239209360917404124833739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5971224962446410999556637 2239209360917404124833739)
              ·
                refine ⟨3358814041376106187250609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2239209360917404124833739 3358814041376106187250609)
                ·
                  refine ⟨2519110531032079640437957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3358814041376106187250609 2519110531032079640437957)
                  ·
                    refine ⟨472333224568514932582117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2519110531032079640437957 472333224568514932582117)
                    ·
                      rfl

theorem cell23_2759597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_2759597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759597 prefixEnd_2759597 := by exact prefixLift 2759597
  have htrace : WordTrace (prefixWord ++ tailWord_2759597) baseStart_2759597 baseEnd_2759597 := by
    simpa [prefixWord, tailWord_2759597, baseEnd_2759597] using wordTrace_append hprefix tailTrace_2759597
  have hstable : (prefixWord ++ tailWord_2759597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759597).length < 2 ^ (prefixWord ++ tailWord_2759597).sum := by decide
  have hdescent : baseEnd_2759597 < baseStart_2759597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759626 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 3, 4, 2]
def baseStart_2759626 : Nat := 118140960795 + 2759626 * 2 ^ 59
def prefixEnd_2759626 : Nat := 4983230072969 + 3 ^ 40 * 2759626 * 2
def baseEnd_2759626 : Nat := 1417014564644525184283717

theorem tailTrace_2759626 : CollatzResearch.WordTrace tailWord_2759626 prefixEnd_2759626 1417014564644525184283717 := by
  unfold tailWord_2759626
  simp only [CollatzResearch.WordTrace]
  refine ⟨25162957275088445860818683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67101219400235855628849821 25162957275088445860818683)
  ·
    refine ⟨37744435912632668791228025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25162957275088445860818683 37744435912632668791228025)
    ·
      refine ⟨28308326934474501593421019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37744435912632668791228025 28308326934474501593421019)
      ·
        refine ⟨42462490401711752390131529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28308326934474501593421019 42462490401711752390131529)
        ·
          refine ⟨31846867801283814292598647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42462490401711752390131529 31846867801283814292598647)
          ·
            refine ⟨47770301701925721438897971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31846867801283814292598647 47770301701925721438897971)
            ·
              refine ⟨71655452552888582158346957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47770301701925721438897971 71655452552888582158346957)
              ·
                refine ⟨26870794707333218309380109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71655452552888582158346957 26870794707333218309380109)
                ·
                  refine ⟨10076548015249956866017541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26870794707333218309380109 10076548015249956866017541)
                  ·
                    refine ⟨1889352752859366912378289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10076548015249956866017541 1889352752859366912378289)
                    ·
                      refine ⟨1417014564644525184283717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1889352752859366912378289 1417014564644525184283717)
                      ·
                        rfl

theorem cell23_2759626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_2759626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759626 prefixEnd_2759626 := by exact prefixLift 2759626
  have htrace : WordTrace (prefixWord ++ tailWord_2759626) baseStart_2759626 baseEnd_2759626 := by
    simpa [prefixWord, tailWord_2759626, baseEnd_2759626] using wordTrace_append hprefix tailTrace_2759626
  have hstable : (prefixWord ++ tailWord_2759626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759626).length < 2 ^ (prefixWord ++ tailWord_2759626).sum := by decide
  have hdescent : baseEnd_2759626 < baseStart_2759626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759639 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 4]
def baseStart_2759639 : Nat := 118140960795 + 2759639 * 2 ^ 59
def prefixEnd_2759639 : Nat := 4983230072969 + 3 ^ 40 * 2759639 * 2
def baseEnd_2759639 : Nat := 1417021239893033633421157

theorem tailTrace_2759639 : CollatzResearch.WordTrace tailWord_2759639 prefixEnd_2759639 1417021239893033633421157 := by
  unfold tailWord_2759639
  simp only [CollatzResearch.WordTrace]
  refine ⟨100652303249306686663497971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67101535499537791108998647 100652303249306686663497971)
  ·
    refine ⟨150978454873960029995246957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100652303249306686663497971 150978454873960029995246957)
    ·
      refine ⟨56616920577735011248217609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150978454873960029995246957 56616920577735011248217609)
      ·
        refine ⟨42462690433301258436163207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56616920577735011248217609 42462690433301258436163207)
        ·
          refine ⟨63694035649951887654244811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42462690433301258436163207 63694035649951887654244811)
          ·
            refine ⟨95541053474927831481367217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63694035649951887654244811 95541053474927831481367217)
            ·
              refine ⟨71655790106195873611025413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95541053474927831481367217 71655790106195873611025413)
              ·
                refine ⟨13435460644911726302067265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71655790106195873611025413 13435460644911726302067265)
                ·
                  refine ⟨10076595483683794726550449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13435460644911726302067265 10076595483683794726550449)
                  ·
                    refine ⟨7557446612762846044912837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10076595483683794726550449 7557446612762846044912837)
                    ·
                      refine ⟨1417021239893033633421157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7557446612762846044912837 1417021239893033633421157)
                      ·
                        rfl

theorem cell23_2759639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_2759639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759639 prefixEnd_2759639 := by exact prefixLift 2759639
  have htrace : WordTrace (prefixWord ++ tailWord_2759639) baseStart_2759639 baseEnd_2759639 := by
    simpa [prefixWord, tailWord_2759639, baseEnd_2759639] using wordTrace_append hprefix tailTrace_2759639
  have hstable : (prefixWord ++ tailWord_2759639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759639).length < 2 ^ (prefixWord ++ tailWord_2759639).sum := by decide
  have hdescent : baseEnd_2759639 < baseStart_2759639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759699 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 4]
def baseStart_2759699 : Nat := 118140960795 + 2759699 * 2 ^ 59
def prefixEnd_2759699 : Nat := 4983230072969 + 3 ^ 40 * 2759699 * 2
def baseEnd_2759699 : Nat := 1417052048732303398670881

theorem tailTrace_2759699 : CollatzResearch.WordTrace tailWord_2759699 prefixEnd_2759699 1417052048732303398670881 := by
  unfold tailWord_2759699
  simp only [CollatzResearch.WordTrace]
  refine ⟨100654491629089316910682151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67102994419392877940454767 100654491629089316910682151)
  ·
    refine ⟨150981737443633975366023227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100654491629089316910682151 150981737443633975366023227)
    ·
      refine ⟨226472606165450963049034841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150981737443633975366023227 226472606165450963049034841)
      ·
        refine ⟨169854454624088222286776131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226472606165450963049034841 169854454624088222286776131)
        ·
          refine ⟨254781681936132333430164197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169854454624088222286776131 254781681936132333430164197)
          ·
            refine ⟨47771565363024812518155787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 254781681936132333430164197 47771565363024812518155787)
            ·
              refine ⟨71657348044537218777233681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47771565363024812518155787 71657348044537218777233681)
              ·
                refine ⟨53743011033402914082925261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71657348044537218777233681 53743011033402914082925261)
                ·
                  refine ⟨20153629137526092781096973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53743011033402914082925261 20153629137526092781096973)
                  ·
                    refine ⟨7557610926572284792911365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20153629137526092781096973 7557610926572284792911365)
                    ·
                      refine ⟨1417052048732303398670881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7557610926572284792911365 1417052048732303398670881)
                      ·
                        rfl

theorem cell23_2759699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_2759699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759699 prefixEnd_2759699 := by exact prefixLift 2759699
  have htrace : WordTrace (prefixWord ++ tailWord_2759699) baseStart_2759699 baseEnd_2759699 := by
    simpa [prefixWord, tailWord_2759699, baseEnd_2759699] using wordTrace_append hprefix tailTrace_2759699
  have hstable : (prefixWord ++ tailWord_2759699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759699).length < 2 ^ (prefixWord ++ tailWord_2759699).sum := by decide
  have hdescent : baseEnd_2759699 < baseStart_2759699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759703 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 2, 5, 2]
def baseStart_2759703 : Nat := 118140960795 + 2759703 * 2 ^ 59
def prefixEnd_2759703 : Nat := 4983230072969 + 3 ^ 40 * 2759703 * 2
def baseEnd_2759703 : Nat := 1417054102654921383020863

theorem tailTrace_2759703 : CollatzResearch.WordTrace tailWord_2759703 prefixEnd_2759703 1417054102654921383020863 := by
  unfold tailWord_2759703
  simp only [CollatzResearch.WordTrace]
  refine ⟨100654637521074825593827763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67103091680716550395885175 100654637521074825593827763)
  ·
    refine ⟨150981956281612238390741645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100654637521074825593827763 150981956281612238390741645)
    ·
      refine ⟨56618233605604589396528117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150981956281612238390741645 56618233605604589396528117)
      ·
        refine ⟨5307959400525430255924511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56618233605604589396528117 5307959400525430255924511)
        ·
          refine ⟨7961939100788145383886767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5307959400525430255924511 7961939100788145383886767)
          ·
            refine ⟨11942908651182218075830151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7961939100788145383886767 11942908651182218075830151)
            ·
              refine ⟨17914362976773327113745227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11942908651182218075830151 17914362976773327113745227)
              ·
                refine ⟨26871544465159990670617841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17914362976773327113745227 26871544465159990670617841)
                ·
                  refine ⟨20153658348869993002963381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26871544465159990670617841 20153658348869993002963381)
                  ·
                    refine ⟨1889405470206561844027817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20153658348869993002963381 1889405470206561844027817)
                    ·
                      refine ⟨1417054102654921383020863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1889405470206561844027817 1417054102654921383020863)
                      ·
                        rfl

theorem cell23_2759703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_2759703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759703 prefixEnd_2759703 := by exact prefixLift 2759703
  have htrace : WordTrace (prefixWord ++ tailWord_2759703) baseStart_2759703 baseEnd_2759703 := by
    simpa [prefixWord, tailWord_2759703, baseEnd_2759703] using wordTrace_append hprefix tailTrace_2759703
  have hstable : (prefixWord ++ tailWord_2759703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759703).length < 2 ^ (prefixWord ++ tailWord_2759703).sum := by decide
  have hdescent : baseEnd_2759703 < baseStart_2759703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759769 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 2, 9]
def baseStart_2759769 : Nat := 118140960795 + 2759769 * 2 ^ 59
def prefixEnd_2759769 : Nat := 4983230072969 + 3 ^ 40 * 2759769 * 2
def baseEnd_2759769 : Nat := 472362664126039374931853

theorem tailTrace_2759769 : CollatzResearch.WordTrace tailWord_2759769 prefixEnd_2759769 472362664126039374931853 := by
  unfold tailWord_2759769
  simp only [CollatzResearch.WordTrace]
  refine ⟨100657044738835718865730361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67104696492557145910486907 100657044738835718865730361)
  ·
    refine ⟨75492783554126789149297771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100657044738835718865730361 75492783554126789149297771)
    ·
      refine ⟨113239175331190183723946657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75492783554126789149297771 113239175331190183723946657)
      ·
        refine ⟨84929381498392637792959993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113239175331190183723946657 84929381498392637792959993)
        ·
          refine ⟨63697036123794478344719995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84929381498392637792959993 63697036123794478344719995)
          ·
            refine ⟨95545554185691717517079993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63697036123794478344719995 95545554185691717517079993)
            ·
              refine ⟨71659165639268788137809995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95545554185691717517079993 71659165639268788137809995)
              ·
                refine ⟨107488748458903182206714993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71659165639268788137809995 107488748458903182206714993)
                ·
                  refine ⟨80616561344177386655036245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107488748458903182206714993 80616561344177386655036245)
                  ·
                    refine ⟨472362664126039374931853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 80616561344177386655036245 472362664126039374931853)
                    ·
                      rfl

theorem cell23_2759769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 9].length) (baseStart_2759769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759769 prefixEnd_2759769 := by exact prefixLift 2759769
  have htrace : WordTrace (prefixWord ++ tailWord_2759769) baseStart_2759769 baseEnd_2759769 := by
    simpa [prefixWord, tailWord_2759769, baseEnd_2759769] using wordTrace_append hprefix tailTrace_2759769
  have hstable : (prefixWord ++ tailWord_2759769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759769).length < 2 ^ (prefixWord ++ tailWord_2759769).sum := by decide
  have hdescent : baseEnd_2759769 < baseStart_2759769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759840 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 5, 2, 2]
def baseStart_2759840 : Nat := 118140960795 + 2759840 * 2 ^ 59
def prefixEnd_2759840 : Nat := 4983230072969 + 3 ^ 40 * 2759840 * 2
def baseEnd_2759840 : Nat := 1417124449504587347007733

theorem tailTrace_2759840 : CollatzResearch.WordTrace tailWord_2759840 prefixEnd_2759840 1417124449504587347007733 := by
  unfold tailWord_2759840
  simp only [CollatzResearch.WordTrace]
  refine ⟨50329817160789248995782487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67106422881052331994376649 50329817160789248995782487)
  ·
    refine ⟨75494725741183873493673731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50329817160789248995782487 75494725741183873493673731)
    ·
      refine ⟨113242088611775810240510597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75494725741183873493673731 113242088611775810240510597)
      ·
        refine ⟨21232891614707964420095737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113242088611775810240510597 21232891614707964420095737)
        ·
          refine ⟨15924668711030973315071803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21232891614707964420095737 15924668711030973315071803)
          ·
            refine ⟨23887003066546459972607705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15924668711030973315071803 23887003066546459972607705)
            ·
              refine ⟨17915252299909844979455779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23887003066546459972607705 17915252299909844979455779)
              ·
                refine ⟨26872878449864767469183669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17915252299909844979455779 26872878449864767469183669)
                ·
                  refine ⟨2519332354674821950235969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26872878449864767469183669 2519332354674821950235969)
                  ·
                    refine ⟨1889499266006116462676977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2519332354674821950235969 1889499266006116462676977)
                    ·
                      refine ⟨1417124449504587347007733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1889499266006116462676977 1417124449504587347007733)
                      ·
                        rfl

theorem cell23_2759840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_2759840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759840 prefixEnd_2759840 := by exact prefixLift 2759840
  have htrace : WordTrace (prefixWord ++ tailWord_2759840) baseStart_2759840 baseEnd_2759840 := by
    simpa [prefixWord, tailWord_2759840, baseEnd_2759840] using wordTrace_append hprefix tailTrace_2759840
  have hstable : (prefixWord ++ tailWord_2759840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759840).length < 2 ^ (prefixWord ++ tailWord_2759840).sum := by decide
  have hdescent : baseEnd_2759840 < baseStart_2759840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759850 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2759850 : Nat := 118140960795 + 2759850 * 2 ^ 59
def prefixEnd_2759850 : Nat := 4983230072969 + 3 ^ 40 * 2759850 * 2
def baseEnd_2759850 : Nat := 472376528103710769294229

theorem tailTrace_2759850 : CollatzResearch.WordTrace tailWord_2759850 prefixEnd_2759850 472376528103710769294229 := by
  unfold tailWord_2759850
  simp only [CollatzResearch.WordTrace]
  refine ⟨25164999762885567424857251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67106666034361513132952669 25164999762885567424857251)
  ·
    refine ⟨37747499644328351137285877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25164999762885567424857251 37747499644328351137285877)
    ·
      refine ⟨3538828091655782919120551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37747499644328351137285877 3538828091655782919120551)
      ·
        refine ⟨5308242137483674378680827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3538828091655782919120551 5308242137483674378680827)
        ·
          refine ⟨7962363206225511568021241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5308242137483674378680827 7962363206225511568021241)
          ·
            refine ⟨5971772404669133676015931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7962363206225511568021241 5971772404669133676015931)
            ·
              refine ⟨8957658607003700514023897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5971772404669133676015931 8957658607003700514023897)
              ·
                refine ⟨6718243955252775385517923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8957658607003700514023897 6718243955252775385517923)
                ·
                  refine ⟨10077365932879163078276885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6718243955252775385517923 10077365932879163078276885)
                  ·
                    refine ⟨472376528103710769294229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10077365932879163078276885 472376528103710769294229)
                    ·
                      rfl

theorem cell23_2759850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2759850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759850 prefixEnd_2759850 := by exact prefixLift 2759850
  have htrace : WordTrace (prefixWord ++ tailWord_2759850) baseStart_2759850 baseEnd_2759850 := by
    simpa [prefixWord, tailWord_2759850, baseEnd_2759850] using wordTrace_append hprefix tailTrace_2759850
  have hstable : (prefixWord ++ tailWord_2759850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759850).length < 2 ^ (prefixWord ++ tailWord_2759850).sum := by decide
  have hdescent : baseEnd_2759850 < baseStart_2759850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759857 : List Nat := [1, 2, 2, 5, 1, 2, 3, 1, 1, 1, 4]
def baseStart_2759857 : Nat := 118140960795 + 2759857 * 2 ^ 59
def prefixEnd_2759857 : Nat := 4983230072969 + 3 ^ 40 * 2759857 * 2
def baseEnd_2759857 : Nat := 1417133178675713780495155

theorem tailTrace_2759857 : CollatzResearch.WordTrace tailWord_2759857 prefixEnd_2759857 1417133178675713780495155 := by
  unfold tailWord_2759857
  simp only [CollatzResearch.WordTrace]
  refine ⟨100660254362516909894933825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67106836241677939929955883 100660254362516909894933825)
  ·
    refine ⟨75495190771887682421200369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100660254362516909894933825 75495190771887682421200369)
    ·
      refine ⟨56621393078915761815900277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75495190771887682421200369 56621393078915761815900277)
      ·
        refine ⟨5308255601148352670240651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56621393078915761815900277 5308255601148352670240651)
        ·
          refine ⟨7962383401722529005360977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5308255601148352670240651 7962383401722529005360977)
          ·
            refine ⟨5971787551291896754020733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7962383401722529005360977 5971787551291896754020733)
            ·
              refine ⟨2239420331734461282757775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5971787551291896754020733 2239420331734461282757775)
              ·
                refine ⟨3359130497601691924136663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2239420331734461282757775 3359130497601691924136663)
                ·
                  refine ⟨5038695746402537886204995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3359130497601691924136663 5038695746402537886204995)
                  ·
                    refine ⟨7558043619603806829307493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5038695746402537886204995 7558043619603806829307493)
                    ·
                      refine ⟨1417133178675713780495155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7558043619603806829307493 1417133178675713780495155)
                      ·
                        rfl

theorem cell23_2759857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_2759857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759857 prefixEnd_2759857 := by exact prefixLift 2759857
  have htrace : WordTrace (prefixWord ++ tailWord_2759857) baseStart_2759857 baseEnd_2759857 := by
    simpa [prefixWord, tailWord_2759857, baseEnd_2759857] using wordTrace_append hprefix tailTrace_2759857
  have hstable : (prefixWord ++ tailWord_2759857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759857).length < 2 ^ (prefixWord ++ tailWord_2759857).sum := by decide
  have hdescent : baseEnd_2759857 < baseStart_2759857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759890 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_2759890 : Nat := 118140960795 + 2759890 * 2 ^ 59
def prefixEnd_2759890 : Nat := 4983230072969 + 3 ^ 40 * 2759890 * 2
def baseEnd_2759890 : Nat := 1417150123537312151382503

theorem tailTrace_2759890 : CollatzResearch.WordTrace tailWord_2759890 prefixEnd_2759890 1417150123537312151382503 := by
  unfold tailWord_2759890
  simp only [CollatzResearch.WordTrace]
  refine ⟨25165364492849339132721281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67107638647598237687256749 25165364492849339132721281)
  ·
    refine ⟨18874023369637004349540961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25165364492849339132721281 18874023369637004349540961)
    ·
      refine ⟨14155517527227753262155721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18874023369637004349540961 14155517527227753262155721)
      ·
        refine ⟨10616638145420814946616791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14155517527227753262155721 10616638145420814946616791)
        ·
          refine ⟨15924957218131222419925187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10616638145420814946616791 15924957218131222419925187)
          ·
            refine ⟨23887435827196833629887781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15924957218131222419925187 23887435827196833629887781)
            ·
              refine ⟨4478894217599406305603959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23887435827196833629887781 4478894217599406305603959)
              ·
                refine ⟨6718341326399109458405939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4478894217599406305603959 6718341326399109458405939)
                ·
                  refine ⟨10077511989598664187608909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6718341326399109458405939 10077511989598664187608909)
                  ·
                    refine ⟨3779066996099499070353341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10077511989598664187608909 3779066996099499070353341)
                    ·
                      refine ⟨1417150123537312151382503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3779066996099499070353341 1417150123537312151382503)
                      ·
                        rfl

theorem cell23_2759890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_2759890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759890 prefixEnd_2759890 := by exact prefixLift 2759890
  have htrace : WordTrace (prefixWord ++ tailWord_2759890) baseStart_2759890 baseEnd_2759890 := by
    simpa [prefixWord, tailWord_2759890, baseEnd_2759890] using wordTrace_append hprefix tailTrace_2759890
  have hstable : (prefixWord ++ tailWord_2759890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759890).length < 2 ^ (prefixWord ++ tailWord_2759890).sum := by decide
  have hdescent : baseEnd_2759890 < baseStart_2759890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759911 : List Nat := [1, 1, 5, 3, 3, 1, 2, 1, 1, 2, 3]
def baseStart_2759911 : Nat := 118140960795 + 2759911 * 2 ^ 59
def prefixEnd_2759911 : Nat := 4983230072969 + 3 ^ 40 * 2759911 * 2
def baseEnd_2759911 : Nat := 1417160906631056569219907

theorem tailTrace_2759911 : CollatzResearch.WordTrace tailWord_2759911 prefixEnd_2759911 1417160906631056569219907 := by
  unfold tailWord_2759911
  simp only [CollatzResearch.WordTrace]
  refine ⟨100662223904321277117399587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67108149269547518078266391 100662223904321277117399587)
  ·
    refine ⟨150993335856481915676099381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100662223904321277117399587 150993335856481915676099381)
    ·
      refine ⟨14155625236545179594634317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150993335856481915676099381 14155625236545179594634317)
      ·
        refine ⟨5308359463704442347987869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14155625236545179594634317 5308359463704442347987869)
        ·
          refine ⟨1990634798889165880495451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5308359463704442347987869 1990634798889165880495451)
          ·
            refine ⟨2985952198333748820743177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990634798889165880495451 2985952198333748820743177)
            ·
              refine ⟨2239464148750311615557383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2985952198333748820743177 2239464148750311615557383)
              ·
                refine ⟨3359196223125467423336075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2239464148750311615557383 3359196223125467423336075)
                ·
                  refine ⟨5038794334688201135004113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3359196223125467423336075 5038794334688201135004113)
                  ·
                    refine ⟨3779095751016150851253085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5038794334688201135004113 3779095751016150851253085)
                    ·
                      refine ⟨1417160906631056569219907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3779095751016150851253085 1417160906631056569219907)
                      ·
                        rfl

theorem cell23_2759911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_2759911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759911 prefixEnd_2759911 := by exact prefixLift 2759911
  have htrace : WordTrace (prefixWord ++ tailWord_2759911) baseStart_2759911 baseEnd_2759911 := by
    simpa [prefixWord, tailWord_2759911, baseEnd_2759911] using wordTrace_append hprefix tailTrace_2759911
  have hstable : (prefixWord ++ tailWord_2759911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759911).length < 2 ^ (prefixWord ++ tailWord_2759911).sum := by decide
  have hdescent : baseEnd_2759911 < baseStart_2759911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759947 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 1, 4, 2]
def baseStart_2759947 : Nat := 118140960795 + 2759947 * 2 ^ 59
def prefixEnd_2759947 : Nat := 4983230072969 + 3 ^ 40 * 2759947 * 2
def baseEnd_2759947 : Nat := 1417179391934618428369741

theorem tailTrace_2759947 : CollatzResearch.WordTrace tailWord_2759947 prefixEnd_2759947 1417179391934618428369741 := by
  unfold tailWord_2759947
  simp only [CollatzResearch.WordTrace]
  refine ⟨100663536932190855265710095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67109024621460570177140063 100663536932190855265710095)
  ·
    refine ⟨150995305398286282898565143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100663536932190855265710095 150995305398286282898565143)
    ·
      refine ⟨226492958097429424347847715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150995305398286282898565143 226492958097429424347847715)
      ·
        refine ⟨339739437146144136521771573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226492958097429424347847715 339739437146144136521771573)
        ·
          refine ⟨31850572232451012798916085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 339739437146144136521771573 31850572232451012798916085)
          ·
            refine ⟨2985991146792282449898383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31850572232451012798916085 2985991146792282449898383)
            ·
              refine ⟨4478986720188423674847575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2985991146792282449898383 4478986720188423674847575)
              ·
                refine ⟨6718480080282635512271363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4478986720188423674847575 6718480080282635512271363)
                ·
                  refine ⟨10077720120423953268407045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6718480080282635512271363 10077720120423953268407045)
                  ·
                    refine ⟨1889572522579491237826321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10077720120423953268407045 1889572522579491237826321)
                    ·
                      refine ⟨1417179391934618428369741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1889572522579491237826321 1417179391934618428369741)
                      ·
                        rfl

theorem cell23_2759947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 4, 2].length) (baseStart_2759947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759947 prefixEnd_2759947 := by exact prefixLift 2759947
  have htrace : WordTrace (prefixWord ++ tailWord_2759947) baseStart_2759947 baseEnd_2759947 := by
    simpa [prefixWord, tailWord_2759947, baseEnd_2759947] using wordTrace_append hprefix tailTrace_2759947
  have hstable : (prefixWord ++ tailWord_2759947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759947).length < 2 ^ (prefixWord ++ tailWord_2759947).sum := by decide
  have hdescent : baseEnd_2759947 < baseStart_2759947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759987 : List Nat := [1, 1, 1, 2, 5, 3, 3, 2, 5]
def baseStart_2759987 : Nat := 118140960795 + 2759987 * 2 ^ 59
def prefixEnd_2759987 : Nat := 4983230072969 + 3 ^ 40 * 2759987 * 2
def baseEnd_2759987 : Nat := 157466659017866474652173

theorem tailTrace_2759987 : CollatzResearch.WordTrace tailWord_2759987 prefixEnd_2759987 157466659017866474652173 := by
  unfold tailWord_2759987
  simp only [CollatzResearch.WordTrace]
  refine ⟨100664995852045942097166215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67109997234697294731444143 100664995852045942097166215)
  ·
    refine ⟨150997493778068913145749323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100664995852045942097166215 150997493778068913145749323)
    ·
      refine ⟨226496240667103369718623985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150997493778068913145749323 226496240667103369718623985)
      ·
        refine ⟨169872180500327527288967989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226496240667103369718623985 169872180500327527288967989)
        ·
          refine ⟨15925516921905705683340749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169872180500327527288967989 15925516921905705683340749)
          ·
            refine ⟨5972068845714639631252781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15925516921905705683340749 5972068845714639631252781)
            ·
              refine ⟨2239525817142989861719793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5972068845714639631252781 2239525817142989861719793)
              ·
                refine ⟨1679644362857242396289845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2239525817142989861719793 1679644362857242396289845)
                ·
                  refine ⟨157466659017866474652173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1679644362857242396289845 157466659017866474652173)
                  ·
                    rfl

theorem cell23_2759987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 5].length) (baseStart_2759987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2759987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2759987 prefixEnd_2759987 := by exact prefixLift 2759987
  have htrace : WordTrace (prefixWord ++ tailWord_2759987) baseStart_2759987 baseEnd_2759987 := by
    simpa [prefixWord, tailWord_2759987, baseEnd_2759987] using wordTrace_append hprefix tailTrace_2759987
  have hstable : (prefixWord ++ tailWord_2759987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759987).length < 2 ^ (prefixWord ++ tailWord_2759987).sum := by decide
  have hdescent : baseEnd_2759987 < baseStart_2759987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760003 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 4]
def baseStart_2760003 : Nat := 118140960795 + 2760003 * 2 ^ 59
def prefixEnd_2760003 : Nat := 4983230072969 + 3 ^ 40 * 2760003 * 2
def baseEnd_2760003 : Nat := 1417208146851270209269483

theorem tailTrace_2760003 : CollatzResearch.WordTrace tailWord_2760003 prefixEnd_2760003 1417208146851270209269483 := by
  unfold tailWord_2760003
  simp only [CollatzResearch.WordTrace]
  refine ⟨100665579419987976829748663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67110386279991984553165775 100665579419987976829748663)
  ·
    refine ⟨150998369129981965244622995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100665579419987976829748663 150998369129981965244622995)
    ·
      refine ⟨226497553694972947866934493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150998369129981965244622995 226497553694972947866934493)
      ·
        refine ⟨84936582635614855450100435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226497553694972947866934493 84936582635614855450100435)
        ·
          refine ⟨127404873953422283175150653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84936582635614855450100435 127404873953422283175150653)
          ·
            refine ⟨47776827732533356190681495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127404873953422283175150653 47776827732533356190681495)
            ·
              refine ⟨71665241598800034286022243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47776827732533356190681495 71665241598800034286022243)
              ·
                refine ⟨107497862398200051429033365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71665241598800034286022243 107497862398200051429033365)
                ·
                  refine ⟨5038962299915627410735939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107497862398200051429033365 5038962299915627410735939)
                  ·
                    refine ⟨7558443449873441116103909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5038962299915627410735939 7558443449873441116103909)
                    ·
                      refine ⟨1417208146851270209269483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7558443449873441116103909 1417208146851270209269483)
                      ·
                        rfl

theorem cell23_2760003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_2760003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760003 prefixEnd_2760003 := by exact prefixLift 2760003
  have htrace : WordTrace (prefixWord ++ tailWord_2760003) baseStart_2760003 baseEnd_2760003 := by
    simpa [prefixWord, tailWord_2760003, baseEnd_2760003] using wordTrace_append hprefix tailTrace_2760003
  have hstable : (prefixWord ++ tailWord_2760003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760003).length < 2 ^ (prefixWord ++ tailWord_2760003).sum := by decide
  have hdescent : baseEnd_2760003 < baseStart_2760003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760047 : List Nat := [1, 1, 2, 1, 3, 1, 5, 4, 1, 4]
def baseStart_2760047 : Nat := 118140960795 + 2760047 * 2 ^ 59
def prefixEnd_2760047 : Nat := 4983230072969 + 3 ^ 40 * 2760047 * 2
def baseEnd_2760047 : Nat := 472410246666689345706427

theorem tailTrace_2760047 : CollatzResearch.WordTrace tailWord_2760047 prefixEnd_2760047 472410246666689345706427 := by
  unfold tailWord_2760047
  simp only [CollatzResearch.WordTrace]
  refine ⟨100667184231828572344350395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67111456154552381562900263 100667184231828572344350395)
  ·
    refine ⟨151000776347742858516525593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100667184231828572344350395 151000776347742858516525593)
    ·
      refine ⟨113250582260807143887394195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151000776347742858516525593 113250582260807143887394195)
      ·
        refine ⟨169875873391210715831091293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113250582260807143887394195 169875873391210715831091293)
        ·
          refine ⟨63703452521704018436659235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169875873391210715831091293 63703452521704018436659235)
          ·
            refine ⟨95555178782556027654988853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63703452521704018436659235 95555178782556027654988853)
            ·
              refine ⟨8958298010864627592655205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95555178782556027654988853 8958298010864627592655205)
              ·
                refine ⟨1679680877037117673622851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8958298010864627592655205 1679680877037117673622851)
                ·
                  refine ⟨2519521315555676510434277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1679680877037117673622851 2519521315555676510434277)
                  ·
                    refine ⟨472410246666689345706427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2519521315555676510434277 472410246666689345706427)
                    ·
                      rfl

theorem cell23_2760047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 1, 4].length) (baseStart_2760047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760047 prefixEnd_2760047 := by exact prefixLift 2760047
  have htrace : WordTrace (prefixWord ++ tailWord_2760047) baseStart_2760047 baseEnd_2760047 := by
    simpa [prefixWord, tailWord_2760047, baseEnd_2760047] using wordTrace_append hprefix tailTrace_2760047
  have hstable : (prefixWord ++ tailWord_2760047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760047).length < 2 ^ (prefixWord ++ tailWord_2760047).sum := by decide
  have hdescent : baseEnd_2760047 < baseStart_2760047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760120 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 1, 6]
def baseStart_2760120 : Nat := 118140960795 + 2760120 * 2 ^ 59
def prefixEnd_2760120 : Nat := 4983230072969 + 3 ^ 40 * 2760120 * 2
def baseEnd_2760120 : Nat := 472422741362615417168815

theorem tailTrace_2760120 : CollatzResearch.WordTrace tailWord_2760120 prefixEnd_2760120 472422741362615417168815 := by
  unfold tailWord_2760120
  simp only [CollatzResearch.WordTrace]
  refine ⟨50334923380282052905878907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67113231173709403874505209 50334923380282052905878907)
  ·
    refine ⟨75502385070423079358818361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50334923380282052905878907 75502385070423079358818361)
    ·
      refine ⟨56626788802817309519113771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75502385070423079358818361 56626788802817309519113771)
      ·
        refine ⟨84940183204225964278670657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56626788802817309519113771 84940183204225964278670657)
        ·
          refine ⟨63705137403169473209002993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84940183204225964278670657 63705137403169473209002993)
          ·
            refine ⟨47778853052377104906752245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63705137403169473209002993 47778853052377104906752245)
            ·
              refine ⟨4479267473660353585008023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47778853052377104906752245 4479267473660353585008023)
              ·
                refine ⟨6718901210490530377512035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4479267473660353585008023 6718901210490530377512035)
                ·
                  refine ⟨10078351815735795566268053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6718901210490530377512035 10078351815735795566268053)
                  ·
                    refine ⟨472422741362615417168815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10078351815735795566268053 472422741362615417168815)
                    ·
                      rfl

theorem cell23_2760120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_2760120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760120 prefixEnd_2760120 := by exact prefixLift 2760120
  have htrace : WordTrace (prefixWord ++ tailWord_2760120) baseStart_2760120 baseEnd_2760120 := by
    simpa [prefixWord, tailWord_2760120, baseEnd_2760120] using wordTrace_append hprefix tailTrace_2760120
  have hstable : (prefixWord ++ tailWord_2760120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760120).length < 2 ^ (prefixWord ++ tailWord_2760120).sum := by decide
  have hdescent : baseEnd_2760120 < baseStart_2760120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760124 : List Nat := [2, 2, 2, 4, 2, 1, 2, 2, 1, 5]
def baseStart_2760124 : Nat := 118140960795 + 2760124 * 2 ^ 59
def prefixEnd_2760124 : Nat := 4983230072969 + 3 ^ 40 * 2760124 * 2
def baseEnd_2760124 : Nat := 472423426003488078618809

theorem tailTrace_2760124 : CollatzResearch.WordTrace tailWord_2760124 prefixEnd_2760124 472423426003488078618809 := by
  unfold tailWord_2760124
  simp only [CollatzResearch.WordTrace]
  refine ⟨50334996326274807247451713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67113328435033076329935617 50334996326274807247451713)
  ·
    refine ⟨37751247244706105435588785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50334996326274807247451713 37751247244706105435588785)
    ·
      refine ⟨28313435433529579076691589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37751247244706105435588785 28313435433529579076691589)
      ·
        refine ⟨5308769143786796076879673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28313435433529579076691589 5308769143786796076879673)
        ·
          refine ⟨3981576857840097057659755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5308769143786796076879673 3981576857840097057659755)
          ·
            refine ⟨5972365286760145586489633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3981576857840097057659755 5972365286760145586489633)
            ·
              refine ⟨4479273965070109189867225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5972365286760145586489633 4479273965070109189867225)
              ·
                refine ⟨3359455473802581892400419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4479273965070109189867225 3359455473802581892400419)
                ·
                  refine ⟨5039183210703872838600629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3359455473802581892400419 5039183210703872838600629)
                  ·
                    refine ⟨472423426003488078618809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5039183210703872838600629 472423426003488078618809)
                    ·
                      rfl

theorem cell23_2760124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_2760124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760124 prefixEnd_2760124 := by exact prefixLift 2760124
  have htrace : WordTrace (prefixWord ++ tailWord_2760124) baseStart_2760124 baseEnd_2760124 := by
    simpa [prefixWord, tailWord_2760124, baseEnd_2760124] using wordTrace_append hprefix tailTrace_2760124
  have hstable : (prefixWord ++ tailWord_2760124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760124).length < 2 ^ (prefixWord ++ tailWord_2760124).sum := by decide
  have hdescent : baseEnd_2760124 < baseStart_2760124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760160 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 3]
def baseStart_2760160 : Nat := 118140960795 + 2760160 * 2 ^ 59
def prefixEnd_2760160 : Nat := 4983230072969 + 3 ^ 40 * 2760160 * 2
def baseEnd_2760160 : Nat := 1417288763314026095006261

theorem tailTrace_2760160 : CollatzResearch.WordTrace tailWord_2760160 prefixEnd_2760160 1417288763314026095006261 := by
  unfold tailWord_2760160
  simp only [CollatzResearch.WordTrace]
  refine ⟨50335652840209596321606967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67114203786946128428809289 50335652840209596321606967)
  ·
    refine ⟨75503479260314394482410451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50335652840209596321606967 75503479260314394482410451)
    ·
      refine ⟨113255218890471591723615677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75503479260314394482410451 113255218890471591723615677)
      ·
        refine ⟨42470707083926846896355879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113255218890471591723615677 42470707083926846896355879)
        ·
          refine ⟨63706060625890270344533819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42470707083926846896355879 63706060625890270344533819)
          ·
            refine ⟨95559090938835405516800729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63706060625890270344533819 95559090938835405516800729)
            ·
              refine ⟨71669318204126554137600547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95559090938835405516800729 71669318204126554137600547)
              ·
                refine ⟨107503977306189831206400821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71669318204126554137600547 107503977306189831206400821)
                ·
                  refine ⟨10078497872455296675600077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107503977306189831206400821 10078497872455296675600077)
                  ·
                    refine ⟨3779436702170736253350029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10078497872455296675600077 3779436702170736253350029)
                    ·
                      refine ⟨1417288763314026095006261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3779436702170736253350029 1417288763314026095006261)
                      ·
                        rfl

theorem cell23_2760160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_2760160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760160 prefixEnd_2760160 := by exact prefixLift 2760160
  have htrace : WordTrace (prefixWord ++ tailWord_2760160) baseStart_2760160 baseEnd_2760160 := by
    simpa [prefixWord, tailWord_2760160, baseEnd_2760160] using wordTrace_append hprefix tailTrace_2760160
  have hstable : (prefixWord ++ tailWord_2760160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760160).length < 2 ^ (prefixWord ++ tailWord_2760160).sum := by decide
  have hdescent : baseEnd_2760160 < baseStart_2760160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760161 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 3, 2, 2]
def baseStart_2760161 : Nat := 118140960795 + 2760161 * 2 ^ 59
def prefixEnd_2760161 : Nat := 4983230072969 + 3 ^ 40 * 2760161 * 2
def baseEnd_2760161 : Nat := 1417289276794680591093757

theorem tailTrace_2760161 : CollatzResearch.WordTrace tailWord_2760161 prefixEnd_2760161 1417289276794680591093757 := by
  unfold tailWord_2760161
  simp only [CollatzResearch.WordTrace]
  refine ⟨100671342153415569814000337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67114228102277046542666891 100671342153415569814000337)
  ·
    refine ⟨75503506615061677360500253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100671342153415569814000337 75503506615061677360500253)
    ·
      refine ⟨28313814980648129010187595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75503506615061677360500253 28313814980648129010187595)
      ·
        refine ⟨42470722470972193515281393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28313814980648129010187595 42470722470972193515281393)
        ·
          refine ⟨31853041853229145136461045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42470722470972193515281393 31853041853229145136461045)
          ·
            refine ⟨2986222673740232356543223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31853041853229145136461045 2986222673740232356543223)
            ·
              refine ⟨4479334010610348534814835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2986222673740232356543223 4479334010610348534814835)
              ·
                refine ⟨6719001015915522802222253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4479334010610348534814835 6719001015915522802222253)
                ·
                  refine ⟨2519625380968321050833345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6719001015915522802222253 2519625380968321050833345)
                  ·
                    refine ⟨1889719035726240788125009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2519625380968321050833345 1889719035726240788125009)
                    ·
                      refine ⟨1417289276794680591093757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1889719035726240788125009 1417289276794680591093757)
                      ·
                        rfl

theorem cell23_2760161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_2760161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760161 prefixEnd_2760161 := by exact prefixLift 2760161
  have htrace : WordTrace (prefixWord ++ tailWord_2760161) baseStart_2760161 baseEnd_2760161 := by
    simpa [prefixWord, tailWord_2760161, baseEnd_2760161] using wordTrace_append hprefix tailTrace_2760161
  have hstable : (prefixWord ++ tailWord_2760161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760161).length < 2 ^ (prefixWord ++ tailWord_2760161).sum := by decide
  have hdescent : baseEnd_2760161 < baseStart_2760161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760181 : List Nat := [1, 3, 5, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_2760181 : Nat := 118140960795 + 2760181 * 2 ^ 59
def prefixEnd_2760181 : Nat := 4983230072969 + 3 ^ 40 * 2760181 * 2
def baseEnd_2760181 : Nat := 1417299546407770512843665

theorem tailTrace_2760181 : CollatzResearch.WordTrace tailWord_2760181 prefixEnd_2760181 1417299546407770512843665 := by
  unfold tailWord_2760181
  simp only [CollatzResearch.WordTrace]
  refine ⟨100672071613343113229728397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67114714408895408819818931 100672071613343113229728397)
  ·
    refine ⟨37752026855003667461148149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100672071613343113229728397 37752026855003667461148149)
    ·
      refine ⟨3539252517656593824482639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37752026855003667461148149 3539252517656593824482639)
      ·
        refine ⟨5308878776484890736723959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3539252517656593824482639 5308878776484890736723959)
        ·
          refine ⟨7963318164727336105085939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5308878776484890736723959 7963318164727336105085939)
          ·
            refine ⟨11944977247091004157628909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7963318164727336105085939 11944977247091004157628909)
            ·
              refine ⟨4479366467659126559110841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11944977247091004157628909 4479366467659126559110841)
              ·
                refine ⟨3359524850744344919333131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4479366467659126559110841 3359524850744344919333131)
                ·
                  refine ⟨5039287276116517378999697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3359524850744344919333131 5039287276116517378999697)
                  ·
                    refine ⟨3779465457087388034249773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5039287276116517378999697 3779465457087388034249773)
                    ·
                      refine ⟨1417299546407770512843665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3779465457087388034249773 1417299546407770512843665)
                      ·
                        rfl

theorem cell23_2760181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_2760181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760181 prefixEnd_2760181 := by exact prefixLift 2760181
  have htrace : WordTrace (prefixWord ++ tailWord_2760181) baseStart_2760181 baseEnd_2760181 := by
    simpa [prefixWord, tailWord_2760181, baseEnd_2760181] using wordTrace_append hprefix tailTrace_2760181
  have hstable : (prefixWord ++ tailWord_2760181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760181).length < 2 ^ (prefixWord ++ tailWord_2760181).sum := by decide
  have hdescent : baseEnd_2760181 < baseStart_2760181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760187 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 3, 3, 2]
def baseStart_2760187 : Nat := 118140960795 + 2760187 * 2 ^ 59
def prefixEnd_2760187 : Nat := 4983230072969 + 3 ^ 40 * 2760187 * 2
def baseEnd_2760187 : Nat := 1417302627291697489368637

theorem tailTrace_2760187 : CollatzResearch.WordTrace tailWord_2760187 prefixEnd_2760187 1417302627291697489368637 := by
  unfold tailWord_2760187
  simp only [CollatzResearch.WordTrace]
  refine ⟨100672290451321376254446815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67114860300880917502964543 100672290451321376254446815)
  ·
    refine ⟨151008435676982064381670223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100672290451321376254446815 151008435676982064381670223)
    ·
      refine ⟨226512653515473096572505335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151008435676982064381670223 226512653515473096572505335)
      ·
        refine ⟨339768980273209644858758003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226512653515473096572505335 339768980273209644858758003)
        ·
          refine ⟨509653470409814467288137005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339768980273209644858758003 509653470409814467288137005)
          ·
            refine ⟨191120051403680425233051377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 509653470409814467288137005 191120051403680425233051377)
            ·
              refine ⟨143340038552760318924788533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191120051403680425233051377 143340038552760318924788533)
              ·
                refine ⟨13438128614321279899198925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143340038552760318924788533 13438128614321279899198925)
                ·
                  refine ⟨5039298230370479962199597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13438128614321279899198925 5039298230370479962199597)
                  ·
                    refine ⟨1889736836388929985824849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5039298230370479962199597 1889736836388929985824849)
                    ·
                      refine ⟨1417302627291697489368637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1889736836388929985824849 1417302627291697489368637)
                      ·
                        rfl

theorem cell23_2760187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 3, 2].length) (baseStart_2760187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760187 prefixEnd_2760187 := by exact prefixLift 2760187
  have htrace : WordTrace (prefixWord ++ tailWord_2760187) baseStart_2760187 baseEnd_2760187 := by
    simpa [prefixWord, tailWord_2760187, baseEnd_2760187] using wordTrace_append hprefix tailTrace_2760187
  have hstable : (prefixWord ++ tailWord_2760187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760187).length < 2 ^ (prefixWord ++ tailWord_2760187).sum := by decide
  have hdescent : baseEnd_2760187 < baseStart_2760187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760194 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_2760194 : Nat := 118140960795 + 2760194 * 2 ^ 59
def prefixEnd_2760194 : Nat := 4983230072969 + 3 ^ 40 * 2760194 * 2
def baseEnd_2760194 : Nat := 1417306221656278961981105

theorem tailTrace_2760194 : CollatzResearch.WordTrace tailWord_2760194 prefixEnd_2760194 1417306221656278961981105 := by
  unfold tailWord_2760194
  simp only [CollatzResearch.WordTrace]
  refine ⟨25168136440574004112487909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67115030508197344299967757 25168136440574004112487909)
  ·
    refine ⟨4719025582607625771091483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25168136440574004112487909 4719025582607625771091483)
    ·
      refine ⟨7078538373911438656637225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4719025582607625771091483 7078538373911438656637225)
      ·
        refine ⟨5308903780433578992477919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7078538373911438656637225 5308903780433578992477919)
        ·
          refine ⟨7963355670650368488716879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5308903780433578992477919 7963355670650368488716879)
          ·
            refine ⟨11945033505975552733075319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7963355670650368488716879 11945033505975552733075319)
            ·
              refine ⟨17917550258963329099612979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11945033505975552733075319 17917550258963329099612979)
              ·
                refine ⟨26876325388444993649419469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17917550258963329099612979 26876325388444993649419469)
                ·
                  refine ⟨10078622020666872618532301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26876325388444993649419469 10078622020666872618532301)
                  ·
                    refine ⟨3779483257750077231949613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10078622020666872618532301 3779483257750077231949613)
                    ·
                      refine ⟨1417306221656278961981105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3779483257750077231949613 1417306221656278961981105)
                      ·
                        rfl

theorem cell23_2760194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_2760194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760194 prefixEnd_2760194 := by exact prefixLift 2760194
  have htrace : WordTrace (prefixWord ++ tailWord_2760194) baseStart_2760194 baseEnd_2760194 := by
    simpa [prefixWord, tailWord_2760194, baseEnd_2760194] using wordTrace_append hprefix tailTrace_2760194
  have hstable : (prefixWord ++ tailWord_2760194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760194).length < 2 ^ (prefixWord ++ tailWord_2760194).sum := by decide
  have hdescent : baseEnd_2760194 < baseStart_2760194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760227 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 2, 6]
def baseStart_2760227 : Nat := 118140960795 + 2760227 * 2 ^ 59
def prefixEnd_2760227 : Nat := 4983230072969 + 3 ^ 40 * 2760227 * 2
def baseEnd_2760227 : Nat := 472441055505959110956151

theorem tailTrace_2760227 : CollatzResearch.WordTrace tailWord_2760227 prefixEnd_2760227 472441055505959110956151 := by
  unfold tailWord_2760227
  simp only [CollatzResearch.WordTrace]
  refine ⟨100673749371176463085902935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67115832914117642057268623 100673749371176463085902935)
  ·
    refine ⟨151010624056764694628854403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100673749371176463085902935 151010624056764694628854403)
    ·
      refine ⟨226515936085147041943281605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151010624056764694628854403 226515936085147041943281605)
      ·
        refine ⟨42471738015965070364365301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226515936085147041943281605 42471738015965070364365301)
        ·
          refine ⟨3981725438996725346659247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42471738015965070364365301 3981725438996725346659247)
          ·
            refine ⟨5972588158495088019988871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3981725438996725346659247 5972588158495088019988871)
            ·
              refine ⟨8958882237742632029983307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5972588158495088019988871 8958882237742632029983307)
              ·
                refine ⟨13438323356613948044974961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8958882237742632029983307 13438323356613948044974961)
                ·
                  refine ⟨10078742517460461033731221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13438323356613948044974961 10078742517460461033731221)
                  ·
                    refine ⟨472441055505959110956151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10078742517460461033731221 472441055505959110956151)
                    ·
                      rfl

theorem cell23_2760227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 6].length) (baseStart_2760227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760227 prefixEnd_2760227 := by exact prefixLift 2760227
  have htrace : WordTrace (prefixWord ++ tailWord_2760227) baseStart_2760227 baseEnd_2760227 := by
    simpa [prefixWord, tailWord_2760227, baseEnd_2760227] using wordTrace_append hprefix tailTrace_2760227
  have hstable : (prefixWord ++ tailWord_2760227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760227).length < 2 ^ (prefixWord ++ tailWord_2760227).sum := by decide
  have hdescent : baseEnd_2760227 < baseStart_2760227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760262 : List Nat := [6, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_2760262 : Nat := 118140960795 + 2760262 * 2 ^ 59
def prefixEnd_2760262 : Nat := 4983230072969 + 3 ^ 40 * 2760262 * 2
def baseEnd_2760262 : Nat := 1417341138340784695930793

theorem tailTrace_2760262 : CollatzResearch.WordTrace tailWord_2760262 prefixEnd_2760262 1417341138340784695930793 := by
  unfold tailWord_2760262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3146094560189052001982095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67116683950699776042284693 3146094560189052001982095)
  ·
    refine ⟨4719141840283578002973143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3146094560189052001982095 4719141840283578002973143)
    ·
      refine ⟨7078712760425367004459715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4719141840283578002973143 7078712760425367004459715)
      ·
        refine ⟨10618069140638050506689573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7078712760425367004459715 10618069140638050506689573)
        ·
          refine ⟨1990887963869634470004295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10618069140638050506689573 1990887963869634470004295)
          ·
            refine ⟨2986331945804451705006443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990887963869634470004295 2986331945804451705006443)
            ·
              refine ⟨4479497918706677557509665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2986331945804451705006443 4479497918706677557509665)
              ·
                refine ⟨3359623439030008168132249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4479497918706677557509665 3359623439030008168132249)
                ·
                  refine ⟨2519717579272506126099187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3359623439030008168132249 2519717579272506126099187)
                  ·
                    refine ⟨3779576368908759189148781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2519717579272506126099187 3779576368908759189148781)
                    ·
                      refine ⟨1417341138340784695930793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3779576368908759189148781 1417341138340784695930793)
                      ·
                        rfl

theorem cell23_2760262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_2760262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760262 prefixEnd_2760262 := by exact prefixLift 2760262
  have htrace : WordTrace (prefixWord ++ tailWord_2760262) baseStart_2760262 baseEnd_2760262 := by
    simpa [prefixWord, tailWord_2760262, baseEnd_2760262] using wordTrace_append hprefix tailTrace_2760262
  have hstable : (prefixWord ++ tailWord_2760262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760262).length < 2 ^ (prefixWord ++ tailWord_2760262).sum := by decide
  have hdescent : baseEnd_2760262 < baseStart_2760262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760268 : List Nat := [2, 2, 1, 3, 1, 5, 1, 2, 2, 2, 2]
def baseStart_2760268 : Nat := 118140960795 + 2760268 * 2 ^ 59
def prefixEnd_2760268 : Nat := 4983230072969 + 3 ^ 40 * 2760268 * 2
def baseEnd_2760268 : Nat := 1417344219224711672455765

theorem tailTrace_2760268 : CollatzResearch.WordTrace tailWord_2760268 prefixEnd_2760268 1417344219224711672455765 := by
  unfold tailWord_2760268
  simp only [CollatzResearch.WordTrace]
  refine ⟨50337622382013963544072729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67116829842685284725430305 50337622382013963544072729)
  ·
    refine ⟨37753216786510472658054547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50337622382013963544072729 37753216786510472658054547)
    ·
      refine ⟨56629825179765708987081821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37753216786510472658054547 56629825179765708987081821)
      ·
        refine ⟨21236184442412140870155683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56629825179765708987081821 21236184442412140870155683)
        ·
          refine ⟨31854276663618211305233525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21236184442412140870155683 31854276663618211305233525)
          ·
            refine ⟨2986338437214207309865643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31854276663618211305233525 2986338437214207309865643)
            ·
              refine ⟨4479507655821310964798465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2986338437214207309865643 4479507655821310964798465)
              ·
                refine ⟨3359630741865983223598849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4479507655821310964798465 3359630741865983223598849)
                ·
                  refine ⟨2519723056399487417699137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3359630741865983223598849 2519723056399487417699137)
                  ·
                    refine ⟨1889792292299615563274353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2519723056399487417699137 1889792292299615563274353)
                    ·
                      refine ⟨1417344219224711672455765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1889792292299615563274353 1417344219224711672455765)
                      ·
                        rfl

theorem cell23_2760268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_2760268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760268 prefixEnd_2760268 := by exact prefixLift 2760268
  have htrace : WordTrace (prefixWord ++ tailWord_2760268) baseStart_2760268 baseEnd_2760268 := by
    simpa [prefixWord, tailWord_2760268, baseEnd_2760268] using wordTrace_append hprefix tailTrace_2760268
  have hstable : (prefixWord ++ tailWord_2760268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760268).length < 2 ^ (prefixWord ++ tailWord_2760268).sum := by decide
  have hdescent : baseEnd_2760268 < baseStart_2760268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760274 : List Nat := [3, 2, 2, 1, 2, 2, 2, 4, 5]
def baseStart_2760274 : Nat := 118140960795 + 2760274 * 2 ^ 59
def prefixEnd_2760274 : Nat := 4983230072969 + 3 ^ 40 * 2760274 * 2
def baseEnd_2760274 : Nat := 157483033345404294331193

theorem tailTrace_2760274 : CollatzResearch.WordTrace tailWord_2760274 prefixEnd_2760274 157483033345404294331193 := by
  unfold tailWord_2760274
  simp only [CollatzResearch.WordTrace]
  refine ⟨25168865900501547528215969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67116975734670793408575917 25168865900501547528215969)
  ·
    refine ⟨18876649425376160646161977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25168865900501547528215969 18876649425376160646161977)
    ·
      refine ⟨14157487069032120484621483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18876649425376160646161977 14157487069032120484621483)
      ·
        refine ⟨21236230603548180726932225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14157487069032120484621483 21236230603548180726932225)
        ·
          refine ⟨15927172952661135545199169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21236230603548180726932225 15927172952661135545199169)
          ·
            refine ⟨11945379714495851658899377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15927172952661135545199169 11945379714495851658899377)
            ·
              refine ⟨8959034785871888744174533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11945379714495851658899377 8959034785871888744174533)
              ·
                refine ⟨1679819022350979139532725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8959034785871888744174533 1679819022350979139532725)
                ·
                  refine ⟨157483033345404294331193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1679819022350979139532725 157483033345404294331193)
                  ·
                    rfl

theorem cell23_2760274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_2760274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760274 prefixEnd_2760274 := by exact prefixLift 2760274
  have htrace : WordTrace (prefixWord ++ tailWord_2760274) baseStart_2760274 baseEnd_2760274 := by
    simpa [prefixWord, tailWord_2760274, baseEnd_2760274] using wordTrace_append hprefix tailTrace_2760274
  have hstable : (prefixWord ++ tailWord_2760274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760274).length < 2 ^ (prefixWord ++ tailWord_2760274).sum := by decide
  have hdescent : baseEnd_2760274 < baseStart_2760274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760280 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 1, 1, 7]
def baseStart_2760280 : Nat := 118140960795 + 2760280 * 2 ^ 59
def prefixEnd_2760280 : Nat := 4983230072969 + 3 ^ 40 * 2760280 * 2
def baseEnd_2760280 : Nat := 1417350380992565625505709

theorem tailTrace_2760280 : CollatzResearch.WordTrace tailWord_2760280 prefixEnd_2760280 1417350380992565625505709 := by
  unfold tailWord_2760280
  simp only [CollatzResearch.WordTrace]
  refine ⟨50337841219992226568791147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67117121626656302091721529 50337841219992226568791147)
  ·
    refine ⟨75506761829988339853186721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50337841219992226568791147 75506761829988339853186721)
    ·
      refine ⟨56630071372491254889890041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75506761829988339853186721 56630071372491254889890041)
      ·
        refine ⟨42472553529368441167417531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56630071372491254889890041 42472553529368441167417531)
        ·
          refine ⟨63708830294052661751126297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42472553529368441167417531 63708830294052661751126297)
          ·
            refine ⟨47781622720539496313344723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63708830294052661751126297 47781622720539496313344723)
            ·
              refine ⟨71672434080809244470017085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47781622720539496313344723 71672434080809244470017085)
              ·
                refine ⟨26877162780303466676256407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71672434080809244470017085 26877162780303466676256407)
                ·
                  refine ⟨40315744170455200014384611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26877162780303466676256407 40315744170455200014384611)
                  ·
                    refine ⟨60473616255682800021576917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40315744170455200014384611 60473616255682800021576917)
                    ·
                      refine ⟨1417350380992565625505709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60473616255682800021576917 1417350380992565625505709)
                      ·
                        rfl

theorem cell23_2760280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_2760280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760280 prefixEnd_2760280 := by exact prefixLift 2760280
  have htrace : WordTrace (prefixWord ++ tailWord_2760280) baseStart_2760280 baseEnd_2760280 := by
    simpa [prefixWord, tailWord_2760280, baseEnd_2760280] using wordTrace_append hprefix tailTrace_2760280
  have hstable : (prefixWord ++ tailWord_2760280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760280).length < 2 ^ (prefixWord ++ tailWord_2760280).sum := by decide
  have hdescent : baseEnd_2760280 < baseStart_2760280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760284 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_2760284 : Nat := 118140960795 + 2760284 * 2 ^ 59
def prefixEnd_2760284 : Nat := 4983230072969 + 3 ^ 40 * 2760284 * 2
def baseEnd_2760284 : Nat := 1417352434915183609855691

theorem tailTrace_2760284 : CollatzResearch.WordTrace tailWord_2760284 prefixEnd_2760284 1417352434915183609855691 := by
  unfold tailWord_2760284
  simp only [CollatzResearch.WordTrace]
  refine ⟨50337914165984980910363953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67117218887979974547151937 50337914165984980910363953)
  ·
    refine ⟨37753435624488735682772965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50337914165984980910363953 37753435624488735682772965)
    ·
      refine ⟨7078769179591637940519931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37753435624488735682772965 7078769179591637940519931)
      ·
        refine ⟨10618153769387456910779897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7078769179591637940519931 10618153769387456910779897)
        ·
          refine ⟨7963615327040592683084923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10618153769387456910779897 7963615327040592683084923)
          ·
            refine ⟨11945422990560889024627385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7963615327040592683084923 11945422990560889024627385)
            ·
              refine ⟨8959067242920666768470539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11945422990560889024627385 8959067242920666768470539)
              ·
                refine ⟨13438600864381000152705809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8959067242920666768470539 13438600864381000152705809)
                ·
                  refine ⟨10078950648285750114529357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13438600864381000152705809 10078950648285750114529357)
                  ·
                    refine ⟨3779606493107156292948509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10078950648285750114529357 3779606493107156292948509)
                    ·
                      refine ⟨1417352434915183609855691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3779606493107156292948509 1417352434915183609855691)
                      ·
                        rfl

theorem cell23_2760284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_2760284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760284 prefixEnd_2760284 := by exact prefixLift 2760284
  have htrace : WordTrace (prefixWord ++ tailWord_2760284) baseStart_2760284 baseEnd_2760284 := by
    simpa [prefixWord, tailWord_2760284, baseEnd_2760284] using wordTrace_append hprefix tailTrace_2760284
  have hstable : (prefixWord ++ tailWord_2760284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760284).length < 2 ^ (prefixWord ++ tailWord_2760284).sum := by decide
  have hdescent : baseEnd_2760284 < baseStart_2760284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760285 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_2760285 : Nat := 118140960795 + 2760285 * 2 ^ 59
def prefixEnd_2760285 : Nat := 4983230072969 + 3 ^ 40 * 2760285 * 2
def baseEnd_2760285 : Nat := 1417352948395838105943187

theorem tailTrace_2760285 : CollatzResearch.WordTrace tailWord_2760285 prefixEnd_2760285 1417352948395838105943187 := by
  unfold tailWord_2760285
  simp only [CollatzResearch.WordTrace]
  refine ⟨100675864804966338991514309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67117243203310892661009539 100675864804966338991514309)
  ·
    refine ⟨18876724650931188560908933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100675864804966338991514309 18876724650931188560908933)
    ·
      refine ⟨3539385872049597855170425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18876724650931188560908933 3539385872049597855170425)
      ·
        refine ⟨2654539404037198391377819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3539385872049597855170425 2654539404037198391377819)
        ·
          refine ⟨3981809106055797587066729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2654539404037198391377819 3981809106055797587066729)
          ·
            refine ⟨2986356829541848190300047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3981809106055797587066729 2986356829541848190300047)
            ·
              refine ⟨4479535244312772285450071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2986356829541848190300047 4479535244312772285450071)
              ·
                refine ⟨6719302866469158428175107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4479535244312772285450071 6719302866469158428175107)
                ·
                  refine ⟨10078954299703737642262661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6719302866469158428175107 10078954299703737642262661)
                  ·
                    refine ⟨1889803931194450807924249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10078954299703737642262661 1889803931194450807924249)
                    ·
                      refine ⟨1417352948395838105943187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1889803931194450807924249 1417352948395838105943187)
                      ·
                        rfl

theorem cell23_2760285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_2760285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760285 prefixEnd_2760285 := by exact prefixLift 2760285
  have htrace : WordTrace (prefixWord ++ tailWord_2760285) baseStart_2760285 baseEnd_2760285 := by
    simpa [prefixWord, tailWord_2760285, baseEnd_2760285] using wordTrace_append hprefix tailTrace_2760285
  have hstable : (prefixWord ++ tailWord_2760285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760285).length < 2 ^ (prefixWord ++ tailWord_2760285).sum := by decide
  have hdescent : baseEnd_2760285 < baseStart_2760285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760300 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 1, 10]
def baseStart_2760300 : Nat := 118140960795 + 2760300 * 2 ^ 59
def prefixEnd_2760300 : Nat := 4983230072969 + 3 ^ 40 * 2760300 * 2
def baseEnd_2760300 : Nat := 472453550201885182418539

theorem tailTrace_2760300 : CollatzResearch.WordTrace tailWord_2760300 prefixEnd_2760300 472453550201885182418539 := by
  unfold tailWord_2760300
  simp only [CollatzResearch.WordTrace]
  refine ⟨50338205949955998276655177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67117607933274664368873569 50338205949955998276655177)
  ·
    refine ⟨37753654462466998707491383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50338205949955998276655177 37753654462466998707491383)
    ·
      refine ⟨56630481693700498061237075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37753654462466998707491383 56630481693700498061237075)
      ·
        refine ⟨84945722540550747091855613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56630481693700498061237075 84945722540550747091855613)
        ·
          refine ⟨31854645952706530159445855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84945722540550747091855613 31854645952706530159445855)
          ·
            refine ⟨47781968929059795239168783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31854645952706530159445855 47781968929059795239168783)
            ·
              refine ⟨71672953393589692858753175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47781968929059795239168783 71672953393589692858753175)
              ·
                refine ⟨107509430090384539288129763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71672953393589692858753175 107509430090384539288129763)
                ·
                  refine ⟨161264145135576808932194645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107509430090384539288129763 161264145135576808932194645)
                  ·
                    refine ⟨472453550201885182418539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 161264145135576808932194645 472453550201885182418539)
                    ·
                      rfl

theorem cell23_2760300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_2760300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760300 prefixEnd_2760300 := by exact prefixLift 2760300
  have htrace : WordTrace (prefixWord ++ tailWord_2760300) baseStart_2760300 baseEnd_2760300 := by
    simpa [prefixWord, tailWord_2760300, baseEnd_2760300] using wordTrace_append hprefix tailTrace_2760300
  have hstable : (prefixWord ++ tailWord_2760300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760300).length < 2 ^ (prefixWord ++ tailWord_2760300).sum := by decide
  have hdescent : baseEnd_2760300 < baseStart_2760300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760357 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 2, 5, 3]
def baseStart_2760357 : Nat := 118140960795 + 2760357 * 2 ^ 59
def prefixEnd_2760357 : Nat := 4983230072969 + 3 ^ 40 * 2760357 * 2
def baseEnd_2760357 : Nat := 1417389919002961824242855

theorem tailTrace_2760357 : CollatzResearch.WordTrace tailWord_2760357 prefixEnd_2760357 1417389919002961824242855 := by
  unfold tailWord_2760357
  simp only [CollatzResearch.WordTrace]
  refine ⟨100678490860705495288135325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67118993907136996858756883 100678490860705495288135325)
  ·
    refine ⟨37754434072764560733050747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100678490860705495288135325 37754434072764560733050747)
    ·
      refine ⟨56631651109146841099576121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37754434072764560733050747 56631651109146841099576121)
      ·
        refine ⟨42473738331860130824682091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56631651109146841099576121 42473738331860130824682091)
        ·
          refine ⟨63710607497790196237023137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42473738331860130824682091 63710607497790196237023137)
          ·
            refine ⟨47782955623342647177767353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63710607497790196237023137 47782955623342647177767353)
            ·
              refine ⟨35837216717506985383325515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47782955623342647177767353 35837216717506985383325515)
              ·
                refine ⟨53755825076260478074988273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35837216717506985383325515 53755825076260478074988273)
                ·
                  refine ⟨40316868807195358556241205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53755825076260478074988273 40316868807195358556241205)
                  ·
                    refine ⟨3779706450674564864647613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40316868807195358556241205 3779706450674564864647613)
                    ·
                      refine ⟨1417389919002961824242855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3779706450674564864647613 1417389919002961824242855)
                      ·
                        rfl

theorem cell23_2760357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_2760357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760357 prefixEnd_2760357 := by exact prefixLift 2760357
  have htrace : WordTrace (prefixWord ++ tailWord_2760357) baseStart_2760357 baseEnd_2760357 := by
    simpa [prefixWord, tailWord_2760357, baseEnd_2760357] using wordTrace_append hprefix tailTrace_2760357
  have hstable : (prefixWord ++ tailWord_2760357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760357).length < 2 ^ (prefixWord ++ tailWord_2760357).sum := by decide
  have hdescent : baseEnd_2760357 < baseStart_2760357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760424 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 1, 6]
def baseStart_2760424 : Nat := 118140960795 + 2760424 * 2 ^ 59
def prefixEnd_2760424 : Nat := 4983230072969 + 3 ^ 40 * 2760424 * 2
def baseEnd_2760424 : Nat := 472474774068937687368349

theorem tailTrace_2760424 : CollatzResearch.WordTrace tailWord_2760424 prefixEnd_2760424 472474774068937687368349 := by
  unfold tailWord_2760424
  simp only [CollatzResearch.WordTrace]
  refine ⟨50340467275731382865412163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67120623034308510487216217 50340467275731382865412163)
  ·
    refine ⟨75510700913597074298118245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50340467275731382865412163 75510700913597074298118245)
    ·
      refine ⟨14158256421299451430897171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75510700913597074298118245 14158256421299451430897171)
      ·
        refine ⟨21237384631949177146345757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14158256421299451430897171 21237384631949177146345757)
        ·
          refine ⟨7964019236980941429879659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21237384631949177146345757 7964019236980941429879659)
          ·
            refine ⟨11946028855471412144819489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7964019236980941429879659 11946028855471412144819489)
            ·
              refine ⟨8959521641603559108614617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11946028855471412144819489 8959521641603559108614617)
              ·
                refine ⟨6719641231202669331460963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8959521641603559108614617 6719641231202669331460963)
                ·
                  refine ⟨10079461846804003997191445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6719641231202669331460963 10079461846804003997191445)
                  ·
                    refine ⟨472474774068937687368349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10079461846804003997191445 472474774068937687368349)
                    ·
                      rfl

theorem cell23_2760424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_2760424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760424 prefixEnd_2760424 := by exact prefixLift 2760424
  have htrace : WordTrace (prefixWord ++ tailWord_2760424) baseStart_2760424 baseEnd_2760424 := by
    simpa [prefixWord, tailWord_2760424, baseEnd_2760424] using wordTrace_append hprefix tailTrace_2760424
  have hstable : (prefixWord ++ tailWord_2760424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760424).length < 2 ^ (prefixWord ++ tailWord_2760424).sum := by decide
  have hdescent : baseEnd_2760424 < baseStart_2760424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760431 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 5, 2, 2]
def baseStart_2760431 : Nat := 118140960795 + 2760431 * 2 ^ 59
def prefixEnd_2760431 : Nat := 4983230072969 + 3 ^ 40 * 2760431 * 2
def baseEnd_2760431 : Nat := 1417427916571394534717515

theorem tailTrace_2760431 : CollatzResearch.WordTrace tailWord_2760431 prefixEnd_2760431 1417427916571394534717515 := by
  unfold tailWord_2760431
  simp only [CollatzResearch.WordTrace]
  refine ⟨100681189862437405926329147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67120793241624937284219431 100681189862437405926329147)
  ·
    refine ⟨151021784793656108889493721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100681189862437405926329147 151021784793656108889493721)
    ·
      refine ⟨113266338595242081667120291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151021784793656108889493721 113266338595242081667120291)
      ·
        refine ⟨169899507892863122500680437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113266338595242081667120291 169899507892863122500680437)
        ·
          refine ⟨15928078864955917734438791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169899507892863122500680437 15928078864955917734438791)
          ·
            refine ⟨23892118297433876601658187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15928078864955917734438791 23892118297433876601658187)
            ·
              refine ⟨35838177446150814902487281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23892118297433876601658187 35838177446150814902487281)
              ·
                refine ⟨26878633084613111176865461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35838177446150814902487281 26878633084613111176865461)
                ·
                  refine ⟨2519871851682479172831137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26878633084613111176865461 2519871851682479172831137)
                  ·
                    refine ⟨1889903888761859379623353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2519871851682479172831137 1889903888761859379623353)
                    ·
                      refine ⟨1417427916571394534717515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1889903888761859379623353 1417427916571394534717515)
                      ·
                        rfl

theorem cell23_2760431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 2, 2].length) (baseStart_2760431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760431 prefixEnd_2760431 := by exact prefixLift 2760431
  have htrace : WordTrace (prefixWord ++ tailWord_2760431) baseStart_2760431 baseEnd_2760431 := by
    simpa [prefixWord, tailWord_2760431, baseEnd_2760431] using wordTrace_append hprefix tailTrace_2760431
  have hstable : (prefixWord ++ tailWord_2760431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760431).length < 2 ^ (prefixWord ++ tailWord_2760431).sum := by decide
  have hdescent : baseEnd_2760431 < baseStart_2760431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760434 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_2760434 : Nat := 118140960795 + 2760434 * 2 ^ 59
def prefixEnd_2760434 : Nat := 4983230072969 + 3 ^ 40 * 2760434 * 2
def baseEnd_2760434 : Nat := 1417429457013358022980001

theorem tailTrace_2760434 : CollatzResearch.WordTrace tailWord_2760434 prefixEnd_2760434 1417429457013358022980001 := by
  unfold tailWord_2760434
  simp only [CollatzResearch.WordTrace]
  refine ⟨25170324820356634359672089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67120866187617691625792237 25170324820356634359672089)
  ·
    refine ⟨18877743615267475769754067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25170324820356634359672089 18877743615267475769754067)
    ·
      refine ⟨28316615422901213654631101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18877743615267475769754067 28316615422901213654631101)
      ·
        refine ⟨10618730783587955120486663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28316615422901213654631101 10618730783587955120486663)
        ·
          refine ⟨15928096175381932680729995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10618730783587955120486663 15928096175381932680729995)
          ·
            refine ⟨23892144263072899021094993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15928096175381932680729995 23892144263072899021094993)
            ·
              refine ⟨17919108197304674265821245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23892144263072899021094993 17919108197304674265821245)
              ·
                refine ⟨6719665573989252849682967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17919108197304674265821245 6719665573989252849682967)
                ·
                  refine ⟨10079498360983879274524451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6719665573989252849682967 10079498360983879274524451)
                  ·
                    refine ⟨15119247541475818911786677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10079498360983879274524451 15119247541475818911786677)
                    ·
                      refine ⟨1417429457013358022980001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15119247541475818911786677 1417429457013358022980001)
                      ·
                        rfl

theorem cell23_2760434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_2760434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760434 prefixEnd_2760434 := by exact prefixLift 2760434
  have htrace : WordTrace (prefixWord ++ tailWord_2760434) baseStart_2760434 baseEnd_2760434 := by
    simpa [prefixWord, tailWord_2760434, baseEnd_2760434] using wordTrace_append hprefix tailTrace_2760434
  have hstable : (prefixWord ++ tailWord_2760434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760434).length < 2 ^ (prefixWord ++ tailWord_2760434).sum := by decide
  have hdescent : baseEnd_2760434 < baseStart_2760434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760458 : List Nat := [3, 1, 2, 2, 1, 4, 3, 1, 2, 4]
def baseStart_2760458 : Nat := 118140960795 + 2760458 * 2 ^ 59
def prefixEnd_2760458 : Nat := 4983230072969 + 3 ^ 40 * 2760458 * 2
def baseEnd_2760458 : Nat := 472480593516355309693297

theorem tailTrace_2760458 : CollatzResearch.WordTrace tailWord_2760458 prefixEnd_2760458 472480593516355309693297 := by
  unfold tailWord_2760458
  simp only [CollatzResearch.WordTrace]
  refine ⟨25170543658334897384390507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67121449755559726358374685 25170543658334897384390507)
  ·
    refine ⟨37755815487502346076585761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25170543658334897384390507 37755815487502346076585761)
    ·
      refine ⟨28316861615626759557439321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37755815487502346076585761 28316861615626759557439321)
      ·
        refine ⟨21237646211720069668079491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28316861615626759557439321 21237646211720069668079491)
        ·
          refine ⟨31856469317580104502119237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21237646211720069668079491 31856469317580104502119237)
          ·
            refine ⟨5973087997046269594147357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31856469317580104502119237 5973087997046269594147357)
            ·
              refine ⟨2239907998892351097805259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5973087997046269594147357 2239907998892351097805259)
              ·
                refine ⟨3359861998338526646707889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2239907998892351097805259 3359861998338526646707889)
                ·
                  refine ⟨2519896498753894985030917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3359861998338526646707889 2519896498753894985030917)
                  ·
                    refine ⟨472480593516355309693297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2519896498753894985030917 472480593516355309693297)
                    ·
                      rfl

theorem cell23_2760458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_2760458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760458 prefixEnd_2760458 := by exact prefixLift 2760458
  have htrace : WordTrace (prefixWord ++ tailWord_2760458) baseStart_2760458 baseEnd_2760458 := by
    simpa [prefixWord, tailWord_2760458, baseEnd_2760458] using wordTrace_append hprefix tailTrace_2760458
  have hstable : (prefixWord ++ tailWord_2760458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760458).length < 2 ^ (prefixWord ++ tailWord_2760458).sum := by decide
  have hdescent : baseEnd_2760458 < baseStart_2760458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760471 : List Nat := [1, 1, 3, 4, 2, 3, 2, 7]
def baseStart_2760471 : Nat := 118140960795 + 2760471 * 2 ^ 59
def prefixEnd_2760471 : Nat := 4983230072969 + 3 ^ 40 * 2760471 * 2
def baseEnd_2760471 : Nat := 52498090955465717711753

theorem tailTrace_2760471 : CollatzResearch.WordTrace tailWord_2760471 prefixEnd_2760471 52498090955465717711753 := by
  unfold tailWord_2760471
  simp only [CollatzResearch.WordTrace]
  refine ⟨100682648782292492757785267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67121765854861661838523511 100682648782292492757785267)
  ·
    refine ⟨151023973173438739136677901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100682648782292492757785267 151023973173438739136677901)
    ·
      refine ⟨56633989940039527176254213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151023973173438739136677901 56633989940039527176254213)
      ·
        refine ⟨10618873113757411345547665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56633989940039527176254213 10618873113757411345547665)
        ·
          refine ⟨7964154835318058509160749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10618873113757411345547665 7964154835318058509160749)
          ·
            refine ⟨2986558063244271940935281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7964154835318058509160749 2986558063244271940935281)
            ·
              refine ⟨2239918547433203955701461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2986558063244271940935281 2239918547433203955701461)
              ·
                refine ⟨52498090955465717711753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2239918547433203955701461 52498090955465717711753)
                ·
                  rfl

theorem cell23_2760471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 7].length) (baseStart_2760471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760471 prefixEnd_2760471 := by exact prefixLift 2760471
  have htrace : WordTrace (prefixWord ++ tailWord_2760471) baseStart_2760471 baseEnd_2760471 := by
    simpa [prefixWord, tailWord_2760471, baseEnd_2760471] using wordTrace_append hprefix tailTrace_2760471
  have hstable : (prefixWord ++ tailWord_2760471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760471).length < 2 ^ (prefixWord ++ tailWord_2760471).sum := by decide
  have hdescent : baseEnd_2760471 < baseStart_2760471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760481 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 4, 1, 3]
def baseStart_2760481 : Nat := 118140960795 + 2760481 * 2 ^ 59
def prefixEnd_2760481 : Nat := 4983230072969 + 3 ^ 40 * 2760481 * 2
def baseEnd_2760481 : Nat := 1417453590604119339092285

theorem tailTrace_2760481 : CollatzResearch.WordTrace tailWord_2760481 prefixEnd_2760481 1417453590604119339092285 := by
  unfold tailWord_2760481
  simp only [CollatzResearch.WordTrace]
  refine ⟨100683013512256264465649297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67122009008170842977099531 100683013512256264465649297)
  ·
    refine ⟨75512260134192198349236973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100683013512256264465649297 75512260134192198349236973)
    ·
      refine ⟨28317097550322074380963865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75512260134192198349236973 28317097550322074380963865)
      ·
        refine ⟨21237823162741555785722899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28317097550322074380963865 21237823162741555785722899)
        ·
          refine ⟨31856734744112333678584349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21237823162741555785722899 31856734744112333678584349)
          ·
            refine ⟨11946275529042125129469131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31856734744112333678584349 11946275529042125129469131)
            ·
              refine ⟨17919413293563187694203697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11946275529042125129469131 17919413293563187694203697)
              ·
                refine ⟨13439559970172390770652773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17919413293563187694203697 13439559970172390770652773)
                ·
                  refine ⟨2519917494407323269497395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13439559970172390770652773 2519917494407323269497395)
                  ·
                    refine ⟨3779876241610984904246093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2519917494407323269497395 3779876241610984904246093)
                    ·
                      refine ⟨1417453590604119339092285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3779876241610984904246093 1417453590604119339092285)
                      ·
                        rfl

theorem cell23_2760481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_2760481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760481 prefixEnd_2760481 := by exact prefixLift 2760481
  have htrace : WordTrace (prefixWord ++ tailWord_2760481) baseStart_2760481 baseEnd_2760481 := by
    simpa [prefixWord, tailWord_2760481, baseEnd_2760481] using wordTrace_append hprefix tailTrace_2760481
  have hstable : (prefixWord ++ tailWord_2760481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760481).length < 2 ^ (prefixWord ++ tailWord_2760481).sum := by decide
  have hdescent : baseEnd_2760481 < baseStart_2760481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760515 : List Nat := [1, 1, 1, 3, 1, 7, 2, 1, 2, 1, 3]
def baseStart_2760515 : Nat := 118140960795 + 2760515 * 2 ^ 59
def prefixEnd_2760515 : Nat := 4983230072969 + 3 ^ 40 * 2760515 * 2
def baseEnd_2760515 : Nat := 1417471048946372206067129

theorem tailTrace_2760515 : CollatzResearch.WordTrace tailWord_2760515 prefixEnd_2760515 1417471048946372206067129 := by
  unfold tailWord_2760515
  simp only [CollatzResearch.WordTrace]
  refine ⟨100684253594133088272386999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67122835729422058848257999 100684253594133088272386999)
  ·
    refine ⟨151026380391199632408580499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100684253594133088272386999 151026380391199632408580499)
    ·
      refine ⟨226539570586799448612870749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151026380391199632408580499 226539570586799448612870749)
      ·
        refine ⟨84952338970049793229826531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226539570586799448612870749 84952338970049793229826531)
        ·
          refine ⟨127428508455074689844739797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84952338970049793229826531 127428508455074689844739797)
          ·
            refine ⟨2986605666915813043236089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 127428508455074689844739797 2986605666915813043236089)
            ·
              refine ⟨2239954250186859782427067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2986605666915813043236089 2239954250186859782427067)
              ·
                refine ⟨3359931375280289673640601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2239954250186859782427067 3359931375280289673640601)
                ·
                  refine ⟨2519948531460217255230451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3359931375280289673640601 2519948531460217255230451)
                  ·
                    refine ⟨3779922797190325882845677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2519948531460217255230451 3779922797190325882845677)
                    ·
                      refine ⟨1417471048946372206067129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3779922797190325882845677 1417471048946372206067129)
                      ·
                        rfl

theorem cell23_2760515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 2, 1, 3].length) (baseStart_2760515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760515 prefixEnd_2760515 := by exact prefixLift 2760515
  have htrace : WordTrace (prefixWord ++ tailWord_2760515) baseStart_2760515 baseEnd_2760515 := by
    simpa [prefixWord, tailWord_2760515, baseEnd_2760515] using wordTrace_append hprefix tailTrace_2760515
  have hstable : (prefixWord ++ tailWord_2760515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760515).length < 2 ^ (prefixWord ++ tailWord_2760515).sum := by decide
  have hdescent : baseEnd_2760515 < baseStart_2760515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760521 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 1, 4, 2]
def baseStart_2760521 : Nat := 118140960795 + 2760521 * 2 ^ 59
def prefixEnd_2760521 : Nat := 4983230072969 + 3 ^ 40 * 2760521 * 2
def baseEnd_2760521 : Nat := 1417474129830299182592101

theorem tailTrace_2760521 : CollatzResearch.WordTrace tailWord_2760521 prefixEnd_2760521 1417474129830299182592101 := by
  unfold tailWord_2760521
  simp only [CollatzResearch.WordTrace]
  refine ⟨100684472432111351297105417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67122981621407567531403611 100684472432111351297105417)
  ·
    refine ⟨75513354324083513472829063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100684472432111351297105417 75513354324083513472829063)
    ·
      refine ⟨113270031486125270209243595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75513354324083513472829063 113270031486125270209243595)
      ·
        refine ⟨169905047229187905313865393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113270031486125270209243595 169905047229187905313865393)
        ·
          refine ⟨127428785421890928985399045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169905047229187905313865393 127428785421890928985399045)
          ·
            refine ⟨23892897266604549184762321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127428785421890928985399045 23892897266604549184762321)
            ·
              refine ⟨17919672949953411888571741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23892897266604549184762321 17919672949953411888571741)
              ·
                refine ⟨6719877356232529458214403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17919672949953411888571741 6719877356232529458214403)
                ·
                  refine ⟨10079816034348794187321605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6719877356232529458214403 10079816034348794187321605)
                  ·
                    refine ⟨1889965506440398910122801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10079816034348794187321605 1889965506440398910122801)
                    ·
                      refine ⟨1417474129830299182592101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1889965506440398910122801 1417474129830299182592101)
                      ·
                        rfl

theorem cell23_2760521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 4, 2].length) (baseStart_2760521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760521 prefixEnd_2760521 := by exact prefixLift 2760521
  have htrace : WordTrace (prefixWord ++ tailWord_2760521) baseStart_2760521 baseEnd_2760521 := by
    simpa [prefixWord, tailWord_2760521, baseEnd_2760521] using wordTrace_append hprefix tailTrace_2760521
  have hstable : (prefixWord ++ tailWord_2760521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760521).length < 2 ^ (prefixWord ++ tailWord_2760521).sum := by decide
  have hdescent : baseEnd_2760521 < baseStart_2760521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760525 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_2760525 : Nat := 118140960795 + 2760525 * 2 ^ 59
def prefixEnd_2760525 : Nat := 4983230072969 + 3 ^ 40 * 2760525 * 2
def baseEnd_2760525 : Nat := 1417476183752917166942083

theorem tailTrace_2760525 : CollatzResearch.WordTrace tailWord_2760525 prefixEnd_2760525 1417476183752917166942083 := by
  unfold tailWord_2760525
  simp only [CollatzResearch.WordTrace]
  refine ⟨100684618324096859980251029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67123078882731239986834019 100684618324096859980251029)
  ·
    refine ⟨4719591483942040311574267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 100684618324096859980251029 4719591483942040311574267)
    ·
      refine ⟨7079387225913060467361401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4719591483942040311574267 7079387225913060467361401)
      ·
        refine ⟨5309540419434795350521051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7079387225913060467361401 5309540419434795350521051)
        ·
          refine ⟨7964310629152193025781577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5309540419434795350521051 7964310629152193025781577)
          ·
            refine ⟨5973232971864144769336183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7964310629152193025781577 5973232971864144769336183)
            ·
              refine ⟨8959849457796217154004275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5973232971864144769336183 8959849457796217154004275)
              ·
                refine ⟨13439774186694325731006413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8959849457796217154004275 13439774186694325731006413)
                ·
                  refine ⟨5039915320010372149127405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13439774186694325731006413 5039915320010372149127405)
                  ·
                    refine ⟨1889968245003889555922777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5039915320010372149127405 1889968245003889555922777)
                    ·
                      refine ⟨1417476183752917166942083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1889968245003889555922777 1417476183752917166942083)
                      ·
                        rfl

theorem cell23_2760525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_2760525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760525 prefixEnd_2760525 := by exact prefixLift 2760525
  have htrace : WordTrace (prefixWord ++ tailWord_2760525) baseStart_2760525 baseEnd_2760525 := by
    simpa [prefixWord, tailWord_2760525, baseEnd_2760525] using wordTrace_append hprefix tailTrace_2760525
  have hstable : (prefixWord ++ tailWord_2760525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760525).length < 2 ^ (prefixWord ++ tailWord_2760525).sum := by decide
  have hdescent : baseEnd_2760525 < baseStart_2760525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760561 : List Nat := [1, 2, 2, 2, 1, 3, 3, 4, 5]
def baseStart_2760561 : Nat := 118140960795 + 2760561 * 2 ^ 59
def prefixEnd_2760561 : Nat := 4983230072969 + 3 ^ 40 * 2760561 * 2
def baseEnd_2760561 : Nat := 157499407672942114010213

theorem tailTrace_2760561 : CollatzResearch.WordTrace tailWord_2760561 prefixEnd_2760561 157499407672942114010213 := by
  unfold tailWord_2760561
  simp only [CollatzResearch.WordTrace]
  refine ⟨100685931351966438128561537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67123954234644292085707691 100685931351966438128561537)
  ·
    refine ⟨75514448513974828596421153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100685931351966438128561537 75514448513974828596421153)
    ·
      refine ⟨56635836385481121447315865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75514448513974828596421153 56635836385481121447315865)
      ·
        refine ⟨42476877289110841085486899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56635836385481121447315865 42476877289110841085486899)
        ·
          refine ⟨63715315933666261628230349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42476877289110841085486899 63715315933666261628230349)
          ·
            refine ⟨23893243475124848110586381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63715315933666261628230349 23893243475124848110586381)
            ·
              refine ⟨8959966303171818041469893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23893243475124848110586381 8959966303171818041469893)
              ·
                refine ⟨1679993681844715882775605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8959966303171818041469893 1679993681844715882775605)
                ·
                  refine ⟨157499407672942114010213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1679993681844715882775605 157499407672942114010213)
                  ·
                    rfl

theorem cell23_2760561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 5].length) (baseStart_2760561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760561 prefixEnd_2760561 := by exact prefixLift 2760561
  have htrace : WordTrace (prefixWord ++ tailWord_2760561) baseStart_2760561 baseEnd_2760561 := by
    simpa [prefixWord, tailWord_2760561, baseEnd_2760561] using wordTrace_append hprefix tailTrace_2760561
  have hstable : (prefixWord ++ tailWord_2760561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760561).length < 2 ^ (prefixWord ++ tailWord_2760561).sum := by decide
  have hdescent : baseEnd_2760561 < baseStart_2760561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760581 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 2, 5, 2]
def baseStart_2760581 : Nat := 118140960795 + 2760581 * 2 ^ 59
def prefixEnd_2760581 : Nat := 4983230072969 + 3 ^ 40 * 2760581 * 2
def baseEnd_2760581 : Nat := 1417504938669568947841825

theorem tailTrace_2760581 : CollatzResearch.WordTrace tailWord_2760581 prefixEnd_2760581 1417504938669568947841825 := by
  unfold tailWord_2760581
  simp only [CollatzResearch.WordTrace]
  refine ⟨100686660811893981544289597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67124440541262654362859731 100686660811893981544289597)
  ·
    refine ⟨37757497804460243079108599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100686660811893981544289597 37757497804460243079108599)
    ·
      refine ⟨56636246706690364618662899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37757497804460243079108599 56636246706690364618662899)
      ·
        refine ⟨84954370060035546927994349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56636246706690364618662899 84954370060035546927994349)
        ·
          refine ⟨31857888772513330097997881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84954370060035546927994349 31857888772513330097997881)
          ·
            refine ⟨23893416579384997573498411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31857888772513330097997881 23893416579384997573498411)
            ·
              refine ⟨35840124869077496360247617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23893416579384997573498411 35840124869077496360247617)
              ·
                refine ⟨26880093651808122270185713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35840124869077496360247617 26880093651808122270185713)
                ·
                  refine ⟨20160070238856091702639285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26880093651808122270185713 20160070238856091702639285)
                  ·
                    refine ⟨1890006584892758597122433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20160070238856091702639285 1890006584892758597122433)
                    ·
                      refine ⟨1417504938669568947841825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1890006584892758597122433 1417504938669568947841825)
                      ·
                        rfl

theorem cell23_2760581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 5, 2].length) (baseStart_2760581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760581 prefixEnd_2760581 := by exact prefixLift 2760581
  have htrace : WordTrace (prefixWord ++ tailWord_2760581) baseStart_2760581 baseEnd_2760581 := by
    simpa [prefixWord, tailWord_2760581, baseEnd_2760581] using wordTrace_append hprefix tailTrace_2760581
  have hstable : (prefixWord ++ tailWord_2760581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760581).length < 2 ^ (prefixWord ++ tailWord_2760581).sum := by decide
  have hdescent : baseEnd_2760581 < baseStart_2760581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760606 : List Nat := [4, 3, 1, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_2760606 : Nat := 118140960795 + 2760606 * 2 ^ 59
def prefixEnd_2760606 : Nat := 4983230072969 + 3 ^ 40 * 2760606 * 2
def baseEnd_2760606 : Nat := 1417517775685931350029211

theorem tailTrace_2760606 : CollatzResearch.WordTrace tailWord_2760606 prefixEnd_2760606 1417517775685931350029211 := by
  unfold tailWord_2760606
  simp only [CollatzResearch.WordTrace]
  refine ⟨12585946579600426351743709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67125048424535607209299781 12585946579600426351743709)
  ·
    refine ⟨4719729967350159881903891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12585946579600426351743709 4719729967350159881903891)
    ·
      refine ⟨7079594951025239822855837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4719729967350159881903891 7079594951025239822855837)
      ·
        refine ⟨2654848106634464933570939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7079594951025239822855837 2654848106634464933570939)
        ·
          refine ⟨3982272159951697400356409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2654848106634464933570939 3982272159951697400356409)
          ·
            refine ⟨2986704119963773050267307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3982272159951697400356409 2986704119963773050267307)
            ·
              refine ⟨4480056179945659575400961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2986704119963773050267307 4480056179945659575400961)
              ·
                refine ⟨3360042134959244681550721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4480056179945659575400961 3360042134959244681550721)
                ·
                  refine ⟨2520031601219433511163041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3360042134959244681550721 2520031601219433511163041)
                  ·
                    refine ⟨1890023700914575133372281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2520031601219433511163041 1890023700914575133372281)
                    ·
                      refine ⟨1417517775685931350029211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1890023700914575133372281 1417517775685931350029211)
                      ·
                        rfl

theorem cell23_2760606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_2760606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760606 prefixEnd_2760606 := by exact prefixLift 2760606
  have htrace : WordTrace (prefixWord ++ tailWord_2760606) baseStart_2760606 baseEnd_2760606 := by
    simpa [prefixWord, tailWord_2760606, baseEnd_2760606] using wordTrace_append hprefix tailTrace_2760606
  have hstable : (prefixWord ++ tailWord_2760606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760606).length < 2 ^ (prefixWord ++ tailWord_2760606).sum := by decide
  have hdescent : baseEnd_2760606 < baseStart_2760606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760638 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_2760638 : Nat := 118140960795 + 2760638 * 2 ^ 59
def prefixEnd_2760638 : Nat := 4983230072969 + 3 ^ 40 * 2760638 * 2
def baseEnd_2760638 : Nat := 472511402355625074943021

theorem tailTrace_2760638 : CollatzResearch.WordTrace tailWord_2760638 prefixEnd_2760638 472511402355625074943021 := by
  unfold tailWord_2760638
  simp only [CollatzResearch.WordTrace]
  refine ⟨12586092471585935034889321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67125826515124986852743045 12586092471585935034889321)
  ·
    refine ⟨9439569353689451276166991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12586092471585935034889321 9439569353689451276166991)
    ·
      refine ⟨14159354030534176914250487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9439569353689451276166991 14159354030534176914250487)
      ·
        refine ⟨21239031045801265371375731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14159354030534176914250487 21239031045801265371375731)
        ·
          refine ⟨31858546568701898057063597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21239031045801265371375731 31858546568701898057063597)
          ·
            refine ⟨11946954963263211771398849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31858546568701898057063597 11946954963263211771398849)
            ·
              refine ⟨8960216222447408828549137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11946954963263211771398849 8960216222447408828549137)
              ·
                refine ⟨6720162166835556621411853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8960216222447408828549137 6720162166835556621411853)
                ·
                  refine ⟨2520060812563333733029445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6720162166835556621411853 2520060812563333733029445)
                  ·
                    refine ⟨472511402355625074943021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2520060812563333733029445 472511402355625074943021)
                    ·
                      rfl

theorem cell23_2760638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_2760638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760638 prefixEnd_2760638 := by exact prefixLift 2760638
  have htrace : WordTrace (prefixWord ++ tailWord_2760638) baseStart_2760638 baseEnd_2760638 := by
    simpa [prefixWord, tailWord_2760638, baseEnd_2760638] using wordTrace_append hprefix tailTrace_2760638
  have hstable : (prefixWord ++ tailWord_2760638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760638).length < 2 ^ (prefixWord ++ tailWord_2760638).sum := by decide
  have hdescent : baseEnd_2760638 < baseStart_2760638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760685 : List Nat := [1, 5, 1, 4, 1, 1, 1, 3, 6]
def baseStart_2760685 : Nat := 118140960795 + 2760685 * 2 ^ 59
def prefixEnd_2760685 : Nat := 4983230072969 + 3 ^ 40 * 2760685 * 2
def baseEnd_2760685 : Nat := 157506482295292948993483

theorem tailTrace_2760685 : CollatzResearch.WordTrace tailWord_2760685 prefixEnd_2760685 157506482295292948993483 := by
  unfold tailWord_2760685
  simp only [CollatzResearch.WordTrace]
  refine ⟨100690454003517207306075509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67126969335678138204050339 100690454003517207306075509)
  ·
    refine ⟨9439730062829738184944579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100690454003517207306075509 9439730062829738184944579)
    ·
      refine ⟨14159595094244607277416869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9439730062829738184944579 14159595094244607277416869)
      ·
        refine ⟨2654924080170863864515663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14159595094244607277416869 2654924080170863864515663)
        ·
          refine ⟨3982386120256295796773495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2654924080170863864515663 3982386120256295796773495)
          ·
            refine ⟨5973579180384443695160243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3982386120256295796773495 5973579180384443695160243)
            ·
              refine ⟨8960368770576665542740365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5973579180384443695160243 8960368770576665542740365)
              ·
                refine ⟨3360138288966249578527637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8960368770576665542740365 3360138288966249578527637)
                ·
                  refine ⟨157506482295292948993483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3360138288966249578527637 157506482295292948993483)
                  ·
                    rfl

theorem cell23_2760685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_2760685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760685 prefixEnd_2760685 := by exact prefixLift 2760685
  have htrace : WordTrace (prefixWord ++ tailWord_2760685) baseStart_2760685 baseEnd_2760685 := by
    simpa [prefixWord, tailWord_2760685, baseEnd_2760685] using wordTrace_append hprefix tailTrace_2760685
  have hstable : (prefixWord ++ tailWord_2760685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760685).length < 2 ^ (prefixWord ++ tailWord_2760685).sum := by decide
  have hdescent : baseEnd_2760685 < baseStart_2760685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760705 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 2, 3, 2]
def baseStart_2760705 : Nat := 118140960795 + 2760705 * 2 ^ 59
def prefixEnd_2760705 : Nat := 4983230072969 + 3 ^ 40 * 2760705 * 2
def baseEnd_2760705 : Nat := 1417568610270726462691255

theorem tailTrace_2760705 : CollatzResearch.WordTrace tailWord_2760705 prefixEnd_2760705 1417568610270726462691255 := by
  unfold tailWord_2760705
  simp only [CollatzResearch.WordTrace]
  refine ⟨100691183463444750721803569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67127455642296500481202379 100691183463444750721803569)
  ·
    refine ⟨75518387597583563041352677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100691183463444750721803569 75518387597583563041352677)
    ·
      refine ⟨14159697674546918070253627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75518387597583563041352677 14159697674546918070253627)
      ·
        refine ⟨21239546511820377105380441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14159697674546918070253627 21239546511820377105380441)
        ·
          refine ⟨15929659883865282829035331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21239546511820377105380441 15929659883865282829035331)
          ·
            refine ⟨23894489825797924243552997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15929659883865282829035331 23894489825797924243552997)
            ·
              refine ⟨4480216842337110795666187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23894489825797924243552997 4480216842337110795666187)
              ·
                refine ⟨6720325263505666193499281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4480216842337110795666187 6720325263505666193499281)
                ·
                  refine ⟨5040243947629249645124461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6720325263505666193499281 5040243947629249645124461)
                  ·
                    refine ⟨1890091480360968616921673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5040243947629249645124461 1890091480360968616921673)
                    ·
                      refine ⟨1417568610270726462691255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1890091480360968616921673 1417568610270726462691255)
                      ·
                        rfl

theorem cell23_2760705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_2760705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760705 prefixEnd_2760705 := by exact prefixLift 2760705
  have htrace : WordTrace (prefixWord ++ tailWord_2760705) baseStart_2760705 baseEnd_2760705 := by
    simpa [prefixWord, tailWord_2760705, baseEnd_2760705] using wordTrace_append hprefix tailTrace_2760705
  have hstable : (prefixWord ++ tailWord_2760705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760705).length < 2 ^ (prefixWord ++ tailWord_2760705).sum := by decide
  have hdescent : baseEnd_2760705 < baseStart_2760705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760711 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 3, 6]
def baseStart_2760711 : Nat := 118140960795 + 2760711 * 2 ^ 59
def prefixEnd_2760711 : Nat := 4983230072969 + 3 ^ 40 * 2760711 * 2
def baseEnd_2760711 : Nat := 472523897051551146405409

theorem tailTrace_2760711 : CollatzResearch.WordTrace tailWord_2760711 prefixEnd_2760711 472523897051551146405409 := by
  unfold tailWord_2760711
  simp only [CollatzResearch.WordTrace]
  refine ⟨100691402301423013746521987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67127601534282009164347991 100691402301423013746521987)
  ·
    refine ⟨151037103452134520619782981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100691402301423013746521987 151037103452134520619782981)
    ·
      refine ⟨28319456897275222616209309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151037103452134520619782981 28319456897275222616209309)
      ·
        refine ⟨10619796336478208481078491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28319456897275222616209309 10619796336478208481078491)
        ·
          refine ⟨15929694504717312721617737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10619796336478208481078491 15929694504717312721617737)
          ·
            refine ⟨11947270878537984541213303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15929694504717312721617737 11947270878537984541213303)
            ·
              refine ⟨17920906317806976811819955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11947270878537984541213303 17920906317806976811819955)
              ·
                refine ⟨26881359476710465217729933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17920906317806976811819955 26881359476710465217729933)
                ·
                  refine ⟨10080509803766424456648725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26881359476710465217729933 10080509803766424456648725)
                  ·
                    refine ⟨472523897051551146405409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10080509803766424456648725 472523897051551146405409)
                    ·
                      rfl

theorem cell23_2760711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_2760711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760711 prefixEnd_2760711 := by exact prefixLift 2760711
  have htrace : WordTrace (prefixWord ++ tailWord_2760711) baseStart_2760711 baseEnd_2760711 := by
    simpa [prefixWord, tailWord_2760711, baseEnd_2760711] using wordTrace_append hprefix tailTrace_2760711
  have hstable : (prefixWord ++ tailWord_2760711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760711).length < 2 ^ (prefixWord ++ tailWord_2760711).sum := by decide
  have hdescent : baseEnd_2760711 < baseStart_2760711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760735 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 3, 2, 2]
def baseStart_2760735 : Nat := 118140960795 + 2760735 * 2 ^ 59
def prefixEnd_2760735 : Nat := 4983230072969 + 3 ^ 40 * 2760735 * 2
def baseEnd_2760735 : Nat := 1417584014690361345316117

theorem tailTrace_2760735 : CollatzResearch.WordTrace tailWord_2760735 prefixEnd_2760735 1417584014690361345316117 := by
  unfold tailWord_2760735
  simp only [CollatzResearch.WordTrace]
  refine ⟨100692277653336065845395659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67128185102224043896930439 100692277653336065845395659)
  ·
    refine ⟨151038416480004098768093489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100692277653336065845395659 151038416480004098768093489)
    ·
      refine ⟨113278812360003074076070117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151038416480004098768093489 113278812360003074076070117)
      ·
        refine ⟨21239777317500576389263147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113278812360003074076070117 21239777317500576389263147)
        ·
          refine ⟨31859665976250864583894721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21239777317500576389263147 31859665976250864583894721)
          ·
            refine ⟨23894749482188148437921041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31859665976250864583894721 23894749482188148437921041)
            ·
              refine ⟨17921062111641111328440781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23894749482188148437921041 17921062111641111328440781)
              ·
                refine ⟨6720398291865416748165293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17921062111641111328440781 6720398291865416748165293)
                ·
                  refine ⟨2520149359449531280561985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6720398291865416748165293 2520149359449531280561985)
                  ·
                    refine ⟨1890112019587148460421489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2520149359449531280561985 1890112019587148460421489)
                    ·
                      refine ⟨1417584014690361345316117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1890112019587148460421489 1417584014690361345316117)
                      ·
                        rfl

theorem cell23_2760735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_2760735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760735 prefixEnd_2760735 := by exact prefixLift 2760735
  have htrace : WordTrace (prefixWord ++ tailWord_2760735) baseStart_2760735 baseEnd_2760735 := by
    simpa [prefixWord, tailWord_2760735, baseEnd_2760735] using wordTrace_append hprefix tailTrace_2760735
  have hstable : (prefixWord ++ tailWord_2760735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760735).length < 2 ^ (prefixWord ++ tailWord_2760735).sum := by decide
  have hdescent : baseEnd_2760735 < baseStart_2760735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760738 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_2760738 : Nat := 118140960795 + 2760738 * 2 ^ 59
def prefixEnd_2760738 : Nat := 4983230072969 + 3 ^ 40 * 2760738 * 2
def baseEnd_2760738 : Nat := 1417585555132324833578603

theorem tailTrace_2760738 : CollatzResearch.WordTrace tailWord_2760738 prefixEnd_2760738 1417585555132324833578603 := by
  unfold tailWord_2760738
  simp only [CollatzResearch.WordTrace]
  refine ⟨25173096768081299339438717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67128258048216798238503245 25173096768081299339438717)
  ·
    refine ⟨9439911288030487252289519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25173096768081299339438717 9439911288030487252289519)
    ·
      refine ⟨14159866932045730878434279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9439911288030487252289519 14159866932045730878434279)
      ·
        refine ⟨21239800398068596317651419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14159866932045730878434279 21239800398068596317651419)
        ·
          refine ⟨31859700597102894476477129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21239800398068596317651419 31859700597102894476477129)
          ·
            refine ⟨23894775447827170857357847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31859700597102894476477129 23894775447827170857357847)
            ·
              refine ⟨35842163171740756286036771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23894775447827170857357847 35842163171740756286036771)
              ·
                refine ⟨53763244757611134429055157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35842163171740756286036771 53763244757611134429055157)
                ·
                  refine ⟨5040304196026043852723921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53763244757611134429055157 5040304196026043852723921)
                  ·
                    refine ⟨3780228147019532889542941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5040304196026043852723921 3780228147019532889542941)
                    ·
                      refine ⟨1417585555132324833578603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3780228147019532889542941 1417585555132324833578603)
                      ·
                        rfl

theorem cell23_2760738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_2760738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760738 prefixEnd_2760738 := by exact prefixLift 2760738
  have htrace : WordTrace (prefixWord ++ tailWord_2760738) baseStart_2760738 baseEnd_2760738 := by
    simpa [prefixWord, tailWord_2760738, baseEnd_2760738] using wordTrace_append hprefix tailTrace_2760738
  have hstable : (prefixWord ++ tailWord_2760738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760738).length < 2 ^ (prefixWord ++ tailWord_2760738).sum := by decide
  have hdescent : baseEnd_2760738 < baseStart_2760738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760741 : List Nat := [1, 3, 1, 2, 2, 3, 3, 8]
def baseStart_2760741 : Nat := 118140960795 + 2760741 * 2 ^ 59
def prefixEnd_2760741 : Nat := 4983230072969 + 3 ^ 40 * 2760741 * 2
def baseEnd_2760741 : Nat := 52503225762010678586707

theorem tailTrace_2760741 : CollatzResearch.WordTrace tailWord_2760741 prefixEnd_2760741 52503225762010678586707 := by
  unfold tailWord_2760741
  simp only [CollatzResearch.WordTrace]
  refine ⟨100692496491314328870114077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67128330994209552580076051 100692496491314328870114077)
  ·
    refine ⟨37759686184242873326292779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100692496491314328870114077 37759686184242873326292779)
    ·
      refine ⟨56639529276364309989439169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37759686184242873326292779 56639529276364309989439169)
      ·
        refine ⟨42479646957273232492079377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56639529276364309989439169 42479646957273232492079377)
        ·
          refine ⟨31859735217954924369059533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42479646957273232492079377 31859735217954924369059533)
          ·
            refine ⟨11947400706733096638397325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31859735217954924369059533 11947400706733096638397325)
            ·
              refine ⟨4480275265024911239398997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11947400706733096638397325 4480275265024911239398997)
              ·
                refine ⟨52503225762010678586707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4480275265024911239398997 52503225762010678586707)
                ·
                  rfl

theorem cell23_2760741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 8].length) (baseStart_2760741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760741 prefixEnd_2760741 := by exact prefixLift 2760741
  have htrace : WordTrace (prefixWord ++ tailWord_2760741) baseStart_2760741 baseEnd_2760741 := by
    simpa [prefixWord, tailWord_2760741, baseEnd_2760741] using wordTrace_append hprefix tailTrace_2760741
  have hstable : (prefixWord ++ tailWord_2760741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760741).length < 2 ^ (prefixWord ++ tailWord_2760741).sum := by decide
  have hdescent : baseEnd_2760741 < baseStart_2760741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760756 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_2760756 : Nat := 118140960795 + 2760756 * 2 ^ 59
def prefixEnd_2760756 : Nat := 4983230072969 + 3 ^ 40 * 2760756 * 2
def baseEnd_2760756 : Nat := 1417594797784105763153521

theorem tailTrace_2760756 : CollatzResearch.WordTrace tailWord_2760756 prefixEnd_2760756 1417594797784105763153521 := by
  unfold tailWord_2760756
  simp only [CollatzResearch.WordTrace]
  refine ⟨50346521793129993215955061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67128695724173324287940081 50346521793129993215955061)
  ·
    refine ⟨4719986418105936863995787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50346521793129993215955061 4719986418105936863995787)
    ·
      refine ⟨7079979627158905295993681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4719986418105936863995787 7079979627158905295993681)
      ·
        refine ⟨5309984720369178971995261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7079979627158905295993681 5309984720369178971995261)
        ·
          refine ⟨1991244270138442114498223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5309984720369178971995261 1991244270138442114498223)
          ·
            refine ⟨2986866405207663171747335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991244270138442114498223 2986866405207663171747335)
            ·
              refine ⟨4480299607811494757621003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2986866405207663171747335 4480299607811494757621003)
              ·
                refine ⟨6720449411717242136431505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4480299607811494757621003 6720449411717242136431505)
                ·
                  refine ⟨5040337058787931602323629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6720449411717242136431505 5040337058787931602323629)
                  ·
                    refine ⟨1890126397045474350871361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5040337058787931602323629 1890126397045474350871361)
                    ·
                      refine ⟨1417594797784105763153521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1890126397045474350871361 1417594797784105763153521)
                      ·
                        rfl

theorem cell23_2760756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_2760756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760756 prefixEnd_2760756 := by exact prefixLift 2760756
  have htrace : WordTrace (prefixWord ++ tailWord_2760756) baseStart_2760756 baseEnd_2760756 := by
    simpa [prefixWord, tailWord_2760756, baseEnd_2760756] using wordTrace_append hprefix tailTrace_2760756
  have hstable : (prefixWord ++ tailWord_2760756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760756).length < 2 ^ (prefixWord ++ tailWord_2760756).sum := by decide
  have hdescent : baseEnd_2760756 < baseStart_2760756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760768 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 3]
def baseStart_2760768 : Nat := 118140960795 + 2760768 * 2 ^ 59
def prefixEnd_2760768 : Nat := 4983230072969 + 3 ^ 40 * 2760768 * 2
def baseEnd_2760768 : Nat := 1417600959551959716203465

theorem tailTrace_2760768 : CollatzResearch.WordTrace tailWord_2760768 prefixEnd_2760768 1417600959551959716203465 := by
  unfold tailWord_2760768
  simp only [CollatzResearch.WordTrace]
  refine ⟨50346740631108256240673479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67128987508144341654231305 50346740631108256240673479)
  ·
    refine ⟨75520110946662384361010219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50346740631108256240673479 75520110946662384361010219)
    ·
      refine ⟨113280166419993576541515329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75520110946662384361010219 113280166419993576541515329)
      ·
        refine ⟨84960124814995182406136497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113280166419993576541515329 84960124814995182406136497)
        ·
          refine ⟨63720093611246386804602373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84960124814995182406136497 63720093611246386804602373)
          ·
            refine ⟨11947517552108697525862945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63720093611246386804602373 11947517552108697525862945)
            ·
              refine ⟨8960638164081523144397209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11947517552108697525862945 8960638164081523144397209)
              ·
                refine ⟨6720478623061142358297907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8960638164081523144397209 6720478623061142358297907)
                ·
                  refine ⟨10080717934591713537446861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6720478623061142358297907 10080717934591713537446861)
                  ·
                    refine ⟨3780269225471892576542573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10080717934591713537446861 3780269225471892576542573)
                    ·
                      refine ⟨1417600959551959716203465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3780269225471892576542573 1417600959551959716203465)
                      ·
                        rfl

theorem cell23_2760768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_2760768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760768 prefixEnd_2760768 := by exact prefixLift 2760768
  have htrace : WordTrace (prefixWord ++ tailWord_2760768) baseStart_2760768 baseEnd_2760768 := by
    simpa [prefixWord, tailWord_2760768, baseEnd_2760768] using wordTrace_append hprefix tailTrace_2760768
  have hstable : (prefixWord ++ tailWord_2760768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760768).length < 2 ^ (prefixWord ++ tailWord_2760768).sum := by decide
  have hdescent : baseEnd_2760768 < baseStart_2760768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760769 : List Nat := [1, 2, 5, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_2760769 : Nat := 118140960795 + 2760769 * 2 ^ 59
def prefixEnd_2760769 : Nat := 4983230072969 + 3 ^ 40 * 2760769 * 2
def baseEnd_2760769 : Nat := 1417601473032614212290961

theorem tailTrace_2760769 : CollatzResearch.WordTrace tailWord_2760769 prefixEnd_2760769 1417601473032614212290961 := by
  unfold tailWord_2760769
  simp only [CollatzResearch.WordTrace]
  refine ⟨100693517735212889652133361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67129011823475259768088907 100693517735212889652133361)
  ·
    refine ⟨75520138301409667239100021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100693517735212889652133361 75520138301409667239100021)
    ·
      refine ⟨7080012965757156303665627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75520138301409667239100021 7080012965757156303665627)
      ·
        refine ⟨10620019448635734455498441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7080012965757156303665627 10620019448635734455498441)
        ·
          refine ⟨7965014586476800841623831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10620019448635734455498441 7965014586476800841623831)
          ·
            refine ⟨11947521879715201262435747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7965014586476800841623831 11947521879715201262435747)
            ·
              refine ⟨17921282819572801893653621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11947521879715201262435747 17921282819572801893653621)
              ·
                refine ⟨1680120264334950177530027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17921282819572801893653621 1680120264334950177530027)
                ·
                  refine ⟨2520180396502425266295041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1680120264334950177530027 2520180396502425266295041)
                  ·
                    refine ⟨1890135297376818949721281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2520180396502425266295041 1890135297376818949721281)
                    ·
                      refine ⟨1417601473032614212290961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1890135297376818949721281 1417601473032614212290961)
                      ·
                        rfl

theorem cell23_2760769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_2760769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760769 prefixEnd_2760769 := by exact prefixLift 2760769
  have htrace : WordTrace (prefixWord ++ tailWord_2760769) baseStart_2760769 baseEnd_2760769 := by
    simpa [prefixWord, tailWord_2760769, baseEnd_2760769] using wordTrace_append hprefix tailTrace_2760769
  have hstable : (prefixWord ++ tailWord_2760769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760769).length < 2 ^ (prefixWord ++ tailWord_2760769).sum := by decide
  have hdescent : baseEnd_2760769 < baseStart_2760769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760791 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 4]
def baseStart_2760791 : Nat := 118140960795 + 2760791 * 2 ^ 59
def prefixEnd_2760791 : Nat := 4983230072969 + 3 ^ 40 * 2760791 * 2
def baseEnd_2760791 : Nat := 1417612769607013126215859

theorem tailTrace_2760791 : CollatzResearch.WordTrace tailWord_2760791 prefixEnd_2760791 1417612769607013126215859 := by
  unfold tailWord_2760791
  simp only [CollatzResearch.WordTrace]
  refine ⟨100694320141133187409434227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67129546760755458272956151 100694320141133187409434227)
  ·
    refine ⟨151041480211699781114151341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100694320141133187409434227 151041480211699781114151341)
    ·
      refine ⟨56640555079387417917806753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151041480211699781114151341 56640555079387417917806753)
      ·
        refine ⟨42480416309540563438355065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56640555079387417917806753 42480416309540563438355065)
        ·
          refine ⟨31860312232155422578766299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42480416309540563438355065 31860312232155422578766299)
          ·
            refine ⟨47790468348233133868149449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31860312232155422578766299 47790468348233133868149449)
            ·
              refine ⟨35842851261174850401112087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47790468348233133868149449 35842851261174850401112087)
              ·
                refine ⟨53764276891762275601668131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35842851261174850401112087 53764276891762275601668131)
                ·
                  refine ⟨80646415337643413402502197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53764276891762275601668131 80646415337643413402502197)
                  ·
                    refine ⟨7560601437904070006484581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80646415337643413402502197 7560601437904070006484581)
                    ·
                      refine ⟨1417612769607013126215859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7560601437904070006484581 1417612769607013126215859)
                      ·
                        rfl

theorem cell23_2760791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_2760791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760791 prefixEnd_2760791 := by exact prefixLift 2760791
  have htrace : WordTrace (prefixWord ++ tailWord_2760791) baseStart_2760791 baseEnd_2760791 := by
    simpa [prefixWord, tailWord_2760791, baseEnd_2760791] using wordTrace_append hprefix tailTrace_2760791
  have hstable : (prefixWord ++ tailWord_2760791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760791).length < 2 ^ (prefixWord ++ tailWord_2760791).sum := by decide
  have hdescent : baseEnd_2760791 < baseStart_2760791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760812 : List Nat := [2, 2, 1, 1, 3, 4, 2, 2, 1, 3, 2]
def baseStart_2760812 : Nat := 118140960795 + 2760812 * 2 ^ 59
def prefixEnd_2760812 : Nat := 4983230072969 + 3 ^ 40 * 2760812 * 2
def baseEnd_2760812 : Nat := 1417623552700757544053263

theorem tailTrace_2760812 : CollatzResearch.WordTrace tailWord_2760812 prefixEnd_2760812 1417623552700757544053263 := by
  unfold tailWord_2760812
  simp only [CollatzResearch.WordTrace]
  refine ⟨50347543037028553997974345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67130057382704738663965793 50347543037028553997974345)
  ·
    refine ⟨37760657277771415498480759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50347543037028553997974345 37760657277771415498480759)
    ·
      refine ⟨56640985916657123247721139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37760657277771415498480759 56640985916657123247721139)
      ·
        refine ⟨84961478874985684871581709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56640985916657123247721139 84961478874985684871581709)
        ·
          refine ⟨31860554578119631826843141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84961478874985684871581709 31860554578119631826843141)
          ·
            refine ⟨5973853983397430967533089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31860554578119631826843141 5973853983397430967533089)
            ·
              refine ⟨4480390487548073225649817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5973853983397430967533089 4480390487548073225649817)
              ·
                refine ⟨3360292865661054919237363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4480390487548073225649817 3360292865661054919237363)
                ·
                  refine ⟨5040439298491582378856045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3360292865661054919237363 5040439298491582378856045)
                  ·
                    refine ⟨1890164736934343392071017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5040439298491582378856045 1890164736934343392071017)
                    ·
                      refine ⟨1417623552700757544053263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1890164736934343392071017 1417623552700757544053263)
                      ·
                        rfl

theorem cell23_2760812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 3, 2].length) (baseStart_2760812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760812 prefixEnd_2760812 := by exact prefixLift 2760812
  have htrace : WordTrace (prefixWord ++ tailWord_2760812) baseStart_2760812 baseEnd_2760812 := by
    simpa [prefixWord, tailWord_2760812, baseEnd_2760812] using wordTrace_append hprefix tailTrace_2760812
  have hstable : (prefixWord ++ tailWord_2760812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760812).length < 2 ^ (prefixWord ++ tailWord_2760812).sum := by decide
  have hdescent : baseEnd_2760812 < baseStart_2760812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760828 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_2760828 : Nat := 118140960795 + 2760828 * 2 ^ 59
def prefixEnd_2760828 : Nat := 4983230072969 + 3 ^ 40 * 2760828 * 2
def baseEnd_2760828 : Nat := 1417631768391229481453189

theorem tailTrace_2760828 : CollatzResearch.WordTrace tailWord_2760828 prefixEnd_2760828 1417631768391229481453189 := by
  unfold tailWord_2760828
  simp only [CollatzResearch.WordTrace]
  refine ⟨50347834820999571364265569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67130446427999428485687425 50347834820999571364265569)
  ·
    refine ⟨37760876115749678523199177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50347834820999571364265569 37760876115749678523199177)
    ·
      refine ⟨28320657086812258892399383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37760876115749678523199177 28320657086812258892399383)
      ·
        refine ⟨42480985630218388338599075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28320657086812258892399383 42480985630218388338599075)
        ·
          refine ⟨63721478445327582507898613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42480985630218388338599075 63721478445327582507898613)
          ·
            refine ⟨5973888604249460860115495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63721478445327582507898613 5973888604249460860115495)
            ·
              refine ⟨8960832906374191290173243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5973888604249460860115495 8960832906374191290173243)
              ·
                refine ⟨13441249359561286935259865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8960832906374191290173243 13441249359561286935259865)
                ·
                  refine ⟨10080937019670965201444899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13441249359561286935259865 10080937019670965201444899)
                  ·
                    refine ⟨15121405529506447802167349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10080937019670965201444899 15121405529506447802167349)
                    ·
                      refine ⟨1417631768391229481453189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15121405529506447802167349 1417631768391229481453189)
                      ·
                        rfl

theorem cell23_2760828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_2760828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760828 prefixEnd_2760828 := by exact prefixLift 2760828
  have htrace : WordTrace (prefixWord ++ tailWord_2760828) baseStart_2760828 baseEnd_2760828 := by
    simpa [prefixWord, tailWord_2760828, baseEnd_2760828] using wordTrace_append hprefix tailTrace_2760828
  have hstable : (prefixWord ++ tailWord_2760828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760828).length < 2 ^ (prefixWord ++ tailWord_2760828).sum := by decide
  have hdescent : baseEnd_2760828 < baseStart_2760828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760841 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 7]
def baseStart_2760841 : Nat := 118140960795 + 2760841 * 2 ^ 59
def prefixEnd_2760841 : Nat := 4983230072969 + 3 ^ 40 * 2760841 * 2
def baseEnd_2760841 : Nat := 1417638443639737930590629

theorem tailTrace_2760841 : CollatzResearch.WordTrace tailWord_2760841 prefixEnd_2760841 1417638443639737930590629 := by
  unfold tailWord_2760841
  simp only [CollatzResearch.WordTrace]
  refine ⟨100696143790952045948754377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67130762527301363965836251 100696143790952045948754377)
  ·
    refine ⟨75522107843214034461565783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100696143790952045948754377 75522107843214034461565783)
    ·
      refine ⟨113283161764821051692348675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75522107843214034461565783 113283161764821051692348675)
      ·
        refine ⟨169924742647231577538523013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113283161764821051692348675 169924742647231577538523013)
        ·
          refine ⟨31860889246355920788473065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169924742647231577538523013 31860889246355920788473065)
          ·
            refine ⟨23895666934766940591354799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31860889246355920788473065 23895666934766940591354799)
            ·
              refine ⟨35843500402150410887032199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23895666934766940591354799 35843500402150410887032199)
              ·
                refine ⟨53765250603225616330548299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35843500402150410887032199 53765250603225616330548299)
                ·
                  refine ⟨80647875904838424495822449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53765250603225616330548299 80647875904838424495822449)
                  ·
                    refine ⟨60485906928628818371866837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80647875904838424495822449 60485906928628818371866837)
                    ·
                      refine ⟨1417638443639737930590629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60485906928628818371866837 1417638443639737930590629)
                      ·
                        rfl

theorem cell23_2760841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_2760841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760841 prefixEnd_2760841 := by exact prefixLift 2760841
  have htrace : WordTrace (prefixWord ++ tailWord_2760841) baseStart_2760841 baseEnd_2760841 := by
    simpa [prefixWord, tailWord_2760841, baseEnd_2760841] using wordTrace_append hprefix tailTrace_2760841
  have hstable : (prefixWord ++ tailWord_2760841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760841).length < 2 ^ (prefixWord ++ tailWord_2760841).sum := by decide
  have hdescent : baseEnd_2760841 < baseStart_2760841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760842 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 4, 2, 2]
def baseStart_2760842 : Nat := 118140960795 + 2760842 * 2 ^ 59
def prefixEnd_2760842 : Nat := 4983230072969 + 3 ^ 40 * 2760842 * 2
def baseEnd_2760842 : Nat := 1417638957120392426678125

theorem tailTrace_2760842 : CollatzResearch.WordTrace tailWord_2760842 prefixEnd_2760842 1417638957120392426678125 := by
  unfold tailWord_2760842
  simp only [CollatzResearch.WordTrace]
  refine ⟨25174045065987105779885195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67130786842632282079693853 25174045065987105779885195)
  ·
    refine ⟨37761067598980658669827793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25174045065987105779885195 37761067598980658669827793)
    ·
      refine ⟨28320800699235494002370845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37761067598980658669827793 28320800699235494002370845)
      ·
        refine ⟨10620300262213310250889067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28320800699235494002370845 10620300262213310250889067)
        ·
          refine ⟨15930450393319965376333601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10620300262213310250889067 15930450393319965376333601)
          ·
            refine ⟨11947837794989974032250201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15930450393319965376333601 11947837794989974032250201)
            ·
              refine ⟨8960878346242480524187651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11947837794989974032250201 8960878346242480524187651)
              ·
                refine ⟨13441317519363720786281477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8960878346242480524187651 13441317519363720786281477)
                ·
                  refine ⟨2520247034880697647427777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13441317519363720786281477 2520247034880697647427777)
                  ·
                    refine ⟨1890185276160523235570833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2520247034880697647427777 1890185276160523235570833)
                    ·
                      refine ⟨1417638957120392426678125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1890185276160523235570833 1417638957120392426678125)
                      ·
                        rfl

theorem cell23_2760842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_2760842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760842 prefixEnd_2760842 := by exact prefixLift 2760842
  have htrace : WordTrace (prefixWord ++ tailWord_2760842) baseStart_2760842 baseEnd_2760842 := by
    simpa [prefixWord, tailWord_2760842, baseEnd_2760842] using wordTrace_append hprefix tailTrace_2760842
  have hstable : (prefixWord ++ tailWord_2760842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760842).length < 2 ^ (prefixWord ++ tailWord_2760842).sum := by decide
  have hdescent : baseEnd_2760842 < baseStart_2760842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760938 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 8]
def baseStart_2760938 : Nat := 118140960795 + 2760938 * 2 ^ 59
def prefixEnd_2760938 : Nat := 4983230072969 + 3 ^ 40 * 2760938 * 2
def baseEnd_2760938 : Nat := 157520916807024894564187

theorem tailTrace_2760938 : CollatzResearch.WordTrace tailWord_2760938 prefixEnd_2760938 157520916807024894564187 := by
  unfold tailWord_2760938
  simp only [CollatzResearch.WordTrace]
  refine ⟨25174920417900157878758867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67133121114400421010023645 25174920417900157878758867)
  ·
    refine ⟨37762380626850236818138301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25174920417900157878758867 37762380626850236818138301)
    ·
      refine ⟨14160892735068838806801863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37762380626850236818138301 14160892735068838806801863)
      ·
        refine ⟨21241339102603258210202795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14160892735068838806801863 21241339102603258210202795)
        ·
          refine ⟨31862008653904887315304193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21241339102603258210202795 31862008653904887315304193)
          ·
            refine ⟨23896506490428665486478145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31862008653904887315304193 23896506490428665486478145)
            ·
              refine ⟨17922379867821499114858609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23896506490428665486478145 17922379867821499114858609)
              ·
                refine ⟨13441784900866124336143957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17922379867821499114858609 13441784900866124336143957)
                ·
                  refine ⟨157520916807024894564187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13441784900866124336143957 157520916807024894564187)
                  ·
                    rfl

theorem cell23_2760938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 8].length) (baseStart_2760938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760938 prefixEnd_2760938 := by exact prefixLift 2760938
  have htrace : WordTrace (prefixWord ++ tailWord_2760938) baseStart_2760938 baseEnd_2760938 := by
    simpa [prefixWord, tailWord_2760938, baseEnd_2760938] using wordTrace_append hprefix tailTrace_2760938
  have hstable : (prefixWord ++ tailWord_2760938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760938).length < 2 ^ (prefixWord ++ tailWord_2760938).sum := by decide
  have hdescent : baseEnd_2760938 < baseStart_2760938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760992 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 1, 5, 2]
def baseStart_2760992 : Nat := 118140960795 + 2760992 * 2 ^ 59
def prefixEnd_2760992 : Nat := 4983230072969 + 3 ^ 40 * 2760992 * 2
def baseEnd_2760992 : Nat := 1417715979218566839802435

theorem tailTrace_2760992 : CollatzResearch.WordTrace tailWord_2760992 prefixEnd_2760992 1417715979218566839802435 := by
  unfold tailWord_2760992
  simp only [CollatzResearch.WordTrace]
  refine ⟨50350825606702499368750615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67134434142269999158334153 50350825606702499368750615)
  ·
    refine ⟨75526238410053749053125923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50350825606702499368750615 75526238410053749053125923)
    ·
      refine ⟨113289357615080623579688885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75526238410053749053125923 113289357615080623579688885)
      ·
        refine ⟨10620877276413808460595833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113289357615080623579688885 10620877276413808460595833)
        ·
          refine ⟨7965657957310356345446875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10620877276413808460595833 7965657957310356345446875)
          ·
            refine ⟨11948486935965534518170313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7965657957310356345446875 11948486935965534518170313)
            ·
              refine ⟨8961365201974150888627735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11948486935965534518170313 8961365201974150888627735)
              ·
                refine ⟨13442047802961226332941603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8961365201974150888627735 13442047802961226332941603)
                ·
                  refine ⟨20163071704441839499412405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13442047802961226332941603 20163071704441839499412405)
                  ·
                    refine ⟨1890287972291422453069913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20163071704441839499412405 1890287972291422453069913)
                    ·
                      refine ⟨1417715979218566839802435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1890287972291422453069913 1417715979218566839802435)
                      ·
                        rfl

theorem cell23_2760992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_2760992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2760992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2760992 prefixEnd_2760992 := by exact prefixLift 2760992
  have htrace : WordTrace (prefixWord ++ tailWord_2760992) baseStart_2760992 baseEnd_2760992 := by
    simpa [prefixWord, tailWord_2760992, baseEnd_2760992] using wordTrace_append hprefix tailTrace_2760992
  have hstable : (prefixWord ++ tailWord_2760992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760992).length < 2 ^ (prefixWord ++ tailWord_2760992).sum := by decide
  have hdescent : baseEnd_2760992 < baseStart_2760992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761009 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 2, 3, 2]
def baseStart_2761009 : Nat := 118140960795 + 2761009 * 2 ^ 59
def prefixEnd_2761009 : Nat := 4983230072969 + 3 ^ 40 * 2761009 * 2
def baseEnd_2761009 : Nat := 1417724708389693273289857

theorem tailTrace_2761009 : CollatzResearch.WordTrace tailWord_2761009 prefixEnd_2761009 1417724708389693273289857 := by
  unfold tailWord_2761009
  simp only [CollatzResearch.WordTrace]
  refine ⟨100702271254343410640870081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67134847502895607093913387 100702271254343410640870081)
  ·
    refine ⟨75526703440757557980652561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100702271254343410640870081 75526703440757557980652561)
    ·
      refine ⟨56645027580568168485489421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75526703440757557980652561 56645027580568168485489421)
      ·
        refine ⟨21241885342713063182058533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56645027580568168485489421 21241885342713063182058533)
        ·
          refine ⟨3982853501758699346635975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21241885342713063182058533 3982853501758699346635975)
          ·
            refine ⟨5974280252638049019953963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3982853501758699346635975 5974280252638049019953963)
            ·
              refine ⟨8961420378957073529930945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5974280252638049019953963 8961420378957073529930945)
              ·
                refine ⟨6721065284217805147448209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8961420378957073529930945 6721065284217805147448209)
                ·
                  refine ⟨5040798963163353860586157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6721065284217805147448209 5040798963163353860586157)
                  ·
                    refine ⟨1890299611186257697719809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5040798963163353860586157 1890299611186257697719809)
                    ·
                      refine ⟨1417724708389693273289857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1890299611186257697719809 1417724708389693273289857)
                      ·
                        rfl

theorem cell23_2761009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_2761009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761009 prefixEnd_2761009 := by exact prefixLift 2761009
  have htrace : WordTrace (prefixWord ++ tailWord_2761009) baseStart_2761009 baseEnd_2761009 := by
    simpa [prefixWord, tailWord_2761009, baseEnd_2761009] using wordTrace_append hprefix tailTrace_2761009
  have hstable : (prefixWord ++ tailWord_2761009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761009).length < 2 ^ (prefixWord ++ tailWord_2761009).sum := by decide
  have hdescent : baseEnd_2761009 < baseStart_2761009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761055 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 3]
def baseStart_2761055 : Nat := 118140960795 + 2761055 * 2 ^ 59
def prefixEnd_2761055 : Nat := 4983230072969 + 3 ^ 40 * 2761055 * 2
def baseEnd_2761055 : Nat := 1417748328499800093314645

theorem tailTrace_2761055 : CollatzResearch.WordTrace tailWord_2761055 prefixEnd_2761055 1417748328499800093314645 := by
  unfold tailWord_2761055
  simp only [CollatzResearch.WordTrace]
  refine ⟨100703949012176760497044619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67135966008117840331363079 100703949012176760497044619)
  ·
    refine ⟨151055923518265140745566929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100703949012176760497044619 151055923518265140745566929)
    ·
      refine ⟨113291942638698855559175197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151055923518265140745566929 113291942638698855559175197)
      ·
        refine ⟨42484478489512070834690699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113291942638698855559175197 42484478489512070834690699)
        ·
          refine ⟨63726717734268106252036049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42484478489512070834690699 63726717734268106252036049)
          ·
            refine ⟨47795038300701079689027037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63726717734268106252036049 47795038300701079689027037)
            ·
              refine ⟨17923139362762904883385139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47795038300701079689027037 17923139362762904883385139)
              ·
                refine ⟨26884709044144357325077709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17923139362762904883385139 26884709044144357325077709)
                ·
                  refine ⟨10081765891554133996904141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26884709044144357325077709 10081765891554133996904141)
                  ·
                    refine ⟨3780662209332800248839053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10081765891554133996904141 3780662209332800248839053)
                    ·
                      refine ⟨1417748328499800093314645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3780662209332800248839053 1417748328499800093314645)
                      ·
                        rfl

theorem cell23_2761055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_2761055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761055 prefixEnd_2761055 := by exact prefixLift 2761055
  have htrace : WordTrace (prefixWord ++ tailWord_2761055) baseStart_2761055 baseEnd_2761055 := by
    simpa [prefixWord, tailWord_2761055, baseEnd_2761055] using wordTrace_append hprefix tailTrace_2761055
  have hstable : (prefixWord ++ tailWord_2761055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761055).length < 2 ^ (prefixWord ++ tailWord_2761055).sum := by decide
  have hdescent : baseEnd_2761055 < baseStart_2761055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761059 : List Nat := [1, 1, 1, 5, 2, 1, 5, 1, 1, 2, 3]
def baseStart_2761059 : Nat := 118140960795 + 2761059 * 2 ^ 59
def prefixEnd_2761059 : Nat := 4983230072969 + 3 ^ 40 * 2761059 * 2
def baseEnd_2761059 : Nat := 1417750382422418077664627

theorem tailTrace_2761059 : CollatzResearch.WordTrace tailWord_2761059 prefixEnd_2761059 1417750382422418077664627 := by
  unfold tailWord_2761059
  simp only [CollatzResearch.WordTrace]
  refine ⟨100704094904162269180190231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67136063269441512786793487 100704094904162269180190231)
  ·
    refine ⟨151056142356243403770285347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100704094904162269180190231 151056142356243403770285347)
    ·
      refine ⟨226584213534365105655428021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151056142356243403770285347 226584213534365105655428021)
      ·
        refine ⟨21242270018846728655196377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226584213534365105655428021 21242270018846728655196377)
        ·
          refine ⟨15931702514135046491397283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21242270018846728655196377 15931702514135046491397283)
          ·
            refine ⟨23897553771202569737095925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15931702514135046491397283 23897553771202569737095925)
            ·
              refine ⟨2240395666050240912852743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23897553771202569737095925 2240395666050240912852743)
              ·
                refine ⟨3360593499075361369279115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2240395666050240912852743 3360593499075361369279115)
                ·
                  refine ⟨5040890248613042053918673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3360593499075361369279115 5040890248613042053918673)
                  ·
                    refine ⟨3780667686459781540439005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5040890248613042053918673 3780667686459781540439005)
                    ·
                      refine ⟨1417750382422418077664627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3780667686459781540439005 1417750382422418077664627)
                      ·
                        rfl

theorem cell23_2761059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_2761059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761059 prefixEnd_2761059 := by exact prefixLift 2761059
  have htrace : WordTrace (prefixWord ++ tailWord_2761059) baseStart_2761059 baseEnd_2761059 := by
    simpa [prefixWord, tailWord_2761059, baseEnd_2761059] using wordTrace_append hprefix tailTrace_2761059
  have hstable : (prefixWord ++ tailWord_2761059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761059).length < 2 ^ (prefixWord ++ tailWord_2761059).sum := by decide
  have hdescent : baseEnd_2761059 < baseStart_2761059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761089 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_2761089 : Nat := 118140960795 + 2761089 * 2 ^ 59
def prefixEnd_2761089 : Nat := 4983230072969 + 3 ^ 40 * 2761089 * 2
def baseEnd_2761089 : Nat := 1417765786842052960289489

theorem tailTrace_2761089 : CollatzResearch.WordTrace tailWord_2761089 prefixEnd_2761089 1417765786842052960289489 := by
  unfold tailWord_2761089
  simp only [CollatzResearch.WordTrace]
  refine ⟨100705189094053584303782321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67136792729369056202521547 100705189094053584303782321)
  ·
    refine ⟨75528891820540188227836741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100705189094053584303782321 75528891820540188227836741)
    ·
      refine ⟨14161667216351285292719389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75528891820540188227836741 14161667216351285292719389)
      ·
        refine ⟨5310625206131731984769771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14161667216351285292719389 5310625206131731984769771)
        ·
          refine ⟨7965937809197597977154657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5310625206131731984769771 7965937809197597977154657)
          ·
            refine ⟨5974453356898198482865993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7965937809197597977154657 5974453356898198482865993)
            ·
              refine ⟨4480840017673648862149495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5974453356898198482865993 4480840017673648862149495)
              ·
                refine ⟨6721260026510473293224243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4480840017673648862149495 6721260026510473293224243)
                ·
                  refine ⟨10081890039765709939836365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6721260026510473293224243 10081890039765709939836365)
                  ·
                    refine ⟨3780708764912141227438637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10081890039765709939836365 3780708764912141227438637)
                    ·
                      refine ⟨1417765786842052960289489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3780708764912141227438637 1417765786842052960289489)
                      ·
                        rfl

theorem cell23_2761089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_2761089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761089 prefixEnd_2761089 := by exact prefixLift 2761089
  have htrace : WordTrace (prefixWord ++ tailWord_2761089) baseStart_2761089 baseEnd_2761089 := by
    simpa [prefixWord, tailWord_2761089, baseEnd_2761089] using wordTrace_append hprefix tailTrace_2761089
  have hstable : (prefixWord ++ tailWord_2761089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761089).length < 2 ^ (prefixWord ++ tailWord_2761089).sum := by decide
  have hdescent : baseEnd_2761089 < baseStart_2761089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761095 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_2761095 : Nat := 118140960795 + 2761095 * 2 ^ 59
def prefixEnd_2761095 : Nat := 4983230072969 + 3 ^ 40 * 2761095 * 2
def baseEnd_2761095 : Nat := 1417768867725979936814461

theorem tailTrace_2761095 : CollatzResearch.WordTrace tailWord_2761095 prefixEnd_2761095 1417768867725979936814461 := by
  unfold tailWord_2761095
  simp only [CollatzResearch.WordTrace]
  refine ⟨100705407932031847328500739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67136938621354564885667159 100705407932031847328500739)
  ·
    refine ⟨151058111898047770992751109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100705407932031847328500739 151058111898047770992751109)
    ·
      refine ⟨28323395980883957061140833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151058111898047770992751109 28323395980883957061140833)
      ·
        refine ⟨21242546985662967795855625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28323395980883957061140833 21242546985662967795855625)
        ·
          refine ⟨15931910239247225846891719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21242546985662967795855625 15931910239247225846891719)
          ·
            refine ⟨23897865358870838770337579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15931910239247225846891719 23897865358870838770337579)
            ·
              refine ⟨35846798038306258155506369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23897865358870838770337579 35846798038306258155506369)
              ·
                refine ⟨26885098528729693616629777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35846798038306258155506369 26885098528729693616629777)
                ·
                  refine ⟨20163823896547270212472333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26885098528729693616629777 20163823896547270212472333)
                  ·
                    refine ⟨7561433961205226329677125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20163823896547270212472333 7561433961205226329677125)
                    ·
                      refine ⟨1417768867725979936814461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7561433961205226329677125 1417768867725979936814461)
                      ·
                        rfl

theorem cell23_2761095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_2761095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761095 prefixEnd_2761095 := by exact prefixLift 2761095
  have htrace : WordTrace (prefixWord ++ tailWord_2761095) baseStart_2761095 baseEnd_2761095 := by
    simpa [prefixWord, tailWord_2761095, baseEnd_2761095] using wordTrace_append hprefix tailTrace_2761095
  have hstable : (prefixWord ++ tailWord_2761095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761095).length < 2 ^ (prefixWord ++ tailWord_2761095).sum := by decide
  have hdescent : baseEnd_2761095 < baseStart_2761095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761110 : List Nat := [5, 3, 1, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2761110 : Nat := 118140960795 + 2761110 * 2 ^ 59
def prefixEnd_2761110 : Nat := 4983230072969 + 3 ^ 40 * 2761110 * 2
def baseEnd_2761110 : Nat := 1417776569935797378126893

theorem tailTrace_2761110 : CollatzResearch.WordTrace tailWord_2761110 prefixEnd_2761110 1417776569935797378126893 := by
  unfold tailWord_2761110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6294122189186094055643549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67137303351318336593531189 6294122189186094055643549)
  ·
    refine ⟨2360295820944785270866331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6294122189186094055643549 2360295820944785270866331)
    ·
      refine ⟨3540443731417177906299497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2360295820944785270866331 3540443731417177906299497)
      ·
        refine ⟨2655332798562883429724623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3540443731417177906299497 2655332798562883429724623)
        ·
          refine ⟨3982999197844325144586935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2655332798562883429724623 3982999197844325144586935)
          ·
            refine ⟨5974498796766487716880403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3982999197844325144586935 5974498796766487716880403)
            ·
              refine ⟨8961748195149731575320605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5974498796766487716880403 8961748195149731575320605)
              ·
                refine ⟨3360655573181149340745227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8961748195149731575320605 3360655573181149340745227)
                ·
                  refine ⟨5040983359771724011117841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3360655573181149340745227 5040983359771724011117841)
                  ·
                    refine ⟨3780737519828793008338381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5040983359771724011117841 3780737519828793008338381)
                    ·
                      refine ⟨1417776569935797378126893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3780737519828793008338381 1417776569935797378126893)
                      ·
                        rfl

theorem cell23_2761110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2761110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761110 prefixEnd_2761110 := by exact prefixLift 2761110
  have htrace : WordTrace (prefixWord ++ tailWord_2761110) baseStart_2761110 baseEnd_2761110 := by
    simpa [prefixWord, tailWord_2761110, baseEnd_2761110] using wordTrace_append hprefix tailTrace_2761110
  have hstable : (prefixWord ++ tailWord_2761110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761110).length < 2 ^ (prefixWord ++ tailWord_2761110).sum := by decide
  have hdescent : baseEnd_2761110 < baseStart_2761110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761125 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 4, 2, 4]
def baseStart_2761125 : Nat := 118140960795 + 2761125 * 2 ^ 59
def prefixEnd_2761125 : Nat := 4983230072969 + 3 ^ 40 * 2761125 * 2
def baseEnd_2761125 : Nat := 1417784272145614819439323

theorem tailTrace_2761125 : CollatzResearch.WordTrace tailWord_2761125 prefixEnd_2761125 1417784272145614819439323 := by
  unfold tailWord_2761125
  simp only [CollatzResearch.WordTrace]
  refine ⟨100706502121923162452092829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67137668081282108301395219 100706502121923162452092829)
  ·
    refine ⟨37764938295721185919534811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100706502121923162452092829 37764938295721185919534811)
    ·
      refine ⟨56647407443581778879302217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37764938295721185919534811 56647407443581778879302217)
      ·
        refine ⟨42485555582686334159476663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56647407443581778879302217 42485555582686334159476663)
        ·
          refine ⟨63728333374029501239214995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42485555582686334159476663 63728333374029501239214995)
          ·
            refine ⟨95592500061044251858822493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63728333374029501239214995 95592500061044251858822493)
            ·
              refine ⟨35847187522891594447058435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95592500061044251858822493 35847187522891594447058435)
              ·
                refine ⟨53770781284337391670587653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35847187522891594447058435 53770781284337391670587653)
                ·
                  refine ⟨10082021490813260938235185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53770781284337391670587653 10082021490813260938235185)
                  ·
                    refine ⟨7561516118109945703676389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10082021490813260938235185 7561516118109945703676389)
                    ·
                      refine ⟨1417784272145614819439323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7561516118109945703676389 1417784272145614819439323)
                      ·
                        rfl

theorem cell23_2761125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_2761125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761125 prefixEnd_2761125 := by exact prefixLift 2761125
  have htrace : WordTrace (prefixWord ++ tailWord_2761125) baseStart_2761125 baseEnd_2761125 := by
    simpa [prefixWord, tailWord_2761125, baseEnd_2761125] using wordTrace_append hprefix tailTrace_2761125
  have hstable : (prefixWord ++ tailWord_2761125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761125).length < 2 ^ (prefixWord ++ tailWord_2761125).sum := by decide
  have hdescent : baseEnd_2761125 < baseStart_2761125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761140 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_2761140 : Nat := 118140960795 + 2761140 * 2 ^ 59
def prefixEnd_2761140 : Nat := 4983230072969 + 3 ^ 40 * 2761140 * 2
def baseEnd_2761140 : Nat := 1417791974355432260751755

theorem tailTrace_2761140 : CollatzResearch.WordTrace tailWord_2761140 prefixEnd_2761140 1417791974355432260751755 := by
  unfold tailWord_2761140
  simp only [CollatzResearch.WordTrace]
  refine ⟨50353524608434410006944437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67138032811245880009259249 50353524608434410006944437)
  ·
    refine ⟨4720642932040725938151041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50353524608434410006944437 4720642932040725938151041)
    ·
      refine ⟨3540482199030544453613281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4720642932040725938151041 3540482199030544453613281)
      ·
        refine ⟨2655361649272908340209961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3540482199030544453613281 2655361649272908340209961)
        ·
          refine ⟨1991521236954681255157471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2655361649272908340209961 1991521236954681255157471)
          ·
            refine ⟨2987281855432021882736207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991521236954681255157471 2987281855432021882736207)
            ·
              refine ⟨4480922783148032824104311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2987281855432021882736207 4480922783148032824104311)
              ·
                refine ⟨6721384174722049236156467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4480922783148032824104311 6721384174722049236156467)
                ·
                  refine ⟨10082076262083073854234701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6721384174722049236156467 10082076262083073854234701)
                  ·
                    refine ⟨3780778598281152695338013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10082076262083073854234701 3780778598281152695338013)
                    ·
                      refine ⟨1417791974355432260751755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3780778598281152695338013 1417791974355432260751755)
                      ·
                        rfl

theorem cell23_2761140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_2761140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761140 prefixEnd_2761140 := by exact prefixLift 2761140
  have htrace : WordTrace (prefixWord ++ tailWord_2761140) baseStart_2761140 baseEnd_2761140 := by
    simpa [prefixWord, tailWord_2761140, baseEnd_2761140] using wordTrace_append hprefix tailTrace_2761140
  have hstable : (prefixWord ++ tailWord_2761140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761140).length < 2 ^ (prefixWord ++ tailWord_2761140).sum := by decide
  have hdescent : baseEnd_2761140 < baseStart_2761140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761192 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_2761192 : Nat := 118140960795 + 2761192 * 2 ^ 59
def prefixEnd_2761192 : Nat := 4983230072969 + 3 ^ 40 * 2761192 * 2
def baseEnd_2761192 : Nat := 1417818675349466057301515

theorem tailTrace_2761192 : CollatzResearch.WordTrace tailWord_2761192 prefixEnd_2761192 1417818675349466057301515 := by
  unfold tailWord_2761192
  simp only [CollatzResearch.WordTrace]
  refine ⟨50354472906340216447390915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67139297208453621929854553 50354472906340216447390915)
  ·
    refine ⟨75531709359510324671086373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50354472906340216447390915 75531709359510324671086373)
    ·
      refine ⟨14162195504908185875828695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75531709359510324671086373 14162195504908185875828695)
      ·
        refine ⟨21243293257362278813743043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14162195504908185875828695 21243293257362278813743043)
        ·
          refine ⟨31864939886043418220614565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21243293257362278813743043 31864939886043418220614565)
          ·
            refine ⟨5974676228633140916365231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31864939886043418220614565 5974676228633140916365231)
            ·
              refine ⟨8962014342949711374547847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5974676228633140916365231 8962014342949711374547847)
              ·
                refine ⟨13443021514424567061821771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8962014342949711374547847 13443021514424567061821771)
                ·
                  refine ⟨20164532271636850592732657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13443021514424567061821771 20164532271636850592732657)
                  ·
                    refine ⟨15123399203727637944549493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20164532271636850592732657 15123399203727637944549493)
                    ·
                      refine ⟨1417818675349466057301515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15123399203727637944549493 1417818675349466057301515)
                      ·
                        rfl

theorem cell23_2761192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_2761192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761192 prefixEnd_2761192 := by exact prefixLift 2761192
  have htrace : WordTrace (prefixWord ++ tailWord_2761192) baseStart_2761192 baseEnd_2761192 := by
    simpa [prefixWord, tailWord_2761192, baseEnd_2761192] using wordTrace_append hprefix tailTrace_2761192
  have hstable : (prefixWord ++ tailWord_2761192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761192).length < 2 ^ (prefixWord ++ tailWord_2761192).sum := by decide
  have hdescent : baseEnd_2761192 < baseStart_2761192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761212 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 5, 4]
def baseStart_2761212 : Nat := 118140960795 + 2761212 * 2 ^ 59
def prefixEnd_2761212 : Nat := 4983230072969 + 3 ^ 40 * 2761212 * 2
def baseEnd_2761212 : Nat := 472609648320851993017141

theorem tailTrace_2761212 : CollatzResearch.WordTrace tailWord_2761212 prefixEnd_2761212 472609648320851993017141 := by
  unfold tailWord_2761212
  simp only [CollatzResearch.WordTrace]
  refine ⟨50354837636303988155254945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67139783515071984207006593 50354837636303988155254945)
  ·
    refine ⟨37766128227227991116441209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50354837636303988155254945 37766128227227991116441209)
    ·
      refine ⟨28324596170420993337330907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37766128227227991116441209 28324596170420993337330907)
      ·
        refine ⟨42486894255631490005996361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28324596170420993337330907 42486894255631490005996361)
        ·
          refine ⟨31865170691723617504497271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42486894255631490005996361 31865170691723617504497271)
          ·
            refine ⟨47797756037585426256745907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31865170691723617504497271 47797756037585426256745907)
            ·
              refine ⟨71696634056378139385118861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47797756037585426256745907 71696634056378139385118861)
              ·
                refine ⟨26886237771141802269419573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71696634056378139385118861 26886237771141802269419573)
                ·
                  refine ⟨2520584791044543962758085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26886237771141802269419573 2520584791044543962758085)
                  ·
                    refine ⟨472609648320851993017141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2520584791044543962758085 472609648320851993017141)
                    ·
                      rfl

theorem cell23_2761212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_2761212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761212 prefixEnd_2761212 := by exact prefixLift 2761212
  have htrace : WordTrace (prefixWord ++ tailWord_2761212) baseStart_2761212 baseEnd_2761212 := by
    simpa [prefixWord, tailWord_2761212, baseEnd_2761212] using wordTrace_append hprefix tailTrace_2761212
  have hstable : (prefixWord ++ tailWord_2761212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761212).length < 2 ^ (prefixWord ++ tailWord_2761212).sum := by decide
  have hdescent : baseEnd_2761212 < baseStart_2761212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761225 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 8]
def baseStart_2761225 : Nat := 118140960795 + 2761225 * 2 ^ 59
def prefixEnd_2761225 : Nat := 4983230072969 + 3 ^ 40 * 2761225 * 2
def baseEnd_2761225 : Nat := 157537291134562714243207

theorem tailTrace_2761225 : CollatzResearch.WordTrace tailWord_2761225 prefixEnd_2761225 157537291134562714243207 := by
  unfold tailWord_2761225
  simp only [CollatzResearch.WordTrace]
  refine ⟨100710149421560879530733129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67140099614373919687155419 100710149421560879530733129)
  ·
    refine ⟨75532612066170659648049847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100710149421560879530733129 75532612066170659648049847)
    ·
      refine ⟨113298918099255989472074771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75532612066170659648049847 113298918099255989472074771)
      ·
        refine ⟨169948377148883984208112157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113298918099255989472074771 169948377148883984208112157)
        ·
          refine ⟨63730641430831494078042059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169948377148883984208112157 63730641430831494078042059)
          ·
            refine ⟨95595962146247241117063089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63730641430831494078042059 95595962146247241117063089)
            ·
              refine ⟨71696971609685430837797317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95595962146247241117063089 71696971609685430837797317)
              ·
                refine ⟨13443182176816018282086997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71696971609685430837797317 13443182176816018282086997)
                ·
                  refine ⟨157537291134562714243207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13443182176816018282086997 157537291134562714243207)
                  ·
                    rfl

theorem cell23_2761225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 8].length) (baseStart_2761225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761225 prefixEnd_2761225 := by exact prefixLift 2761225
  have htrace : WordTrace (prefixWord ++ tailWord_2761225) baseStart_2761225 baseEnd_2761225 := by
    simpa [prefixWord, tailWord_2761225, baseEnd_2761225] using wordTrace_append hprefix tailTrace_2761225
  have hstable : (prefixWord ++ tailWord_2761225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761225).length < 2 ^ (prefixWord ++ tailWord_2761225).sum := by decide
  have hdescent : baseEnd_2761225 < baseStart_2761225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761236 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2761236 : Nat := 118140960795 + 2761236 * 2 ^ 59
def prefixEnd_2761236 : Nat := 4983230072969 + 3 ^ 40 * 2761236 * 2
def baseEnd_2761236 : Nat := 1417841268498263885151313

theorem tailTrace_2761236 : CollatzResearch.WordTrace tailWord_2761236 prefixEnd_2761236 1417841268498263885151313 := by
  unfold tailWord_2761236
  simp only [CollatzResearch.WordTrace]
  refine ⟨50355275312260514204691781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67140367083014018939589041 50355275312260514204691781)
  ·
    refine ⟨9441614121048846413379709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50355275312260514204691781 9441614121048846413379709)
    ·
      refine ⟨3540605295393317405017391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9441614121048846413379709 3540605295393317405017391)
      ·
        refine ⟨5310907943089976107526087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3540605295393317405017391 5310907943089976107526087)
        ·
          refine ⟨7966361914634964161289131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5310907943089976107526087 7966361914634964161289131)
          ·
            refine ⟨11949542871952446241933697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7966361914634964161289131 11949542871952446241933697)
            ·
              refine ⟨8962157153964334681450273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11949542871952446241933697 8962157153964334681450273)
              ·
                refine ⟨6721617865473251011087705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8962157153964334681450273 6721617865473251011087705)
                ·
                  refine ⟨5041213399104938258315779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6721617865473251011087705 5041213399104938258315779)
                  ·
                    refine ⟨7561820098657407387473669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5041213399104938258315779 7561820098657407387473669)
                    ·
                      refine ⟨1417841268498263885151313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7561820098657407387473669 1417841268498263885151313)
                      ·
                        rfl

theorem cell23_2761236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2761236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761236 prefixEnd_2761236 := by exact prefixLift 2761236
  have htrace : WordTrace (prefixWord ++ tailWord_2761236) baseStart_2761236 baseEnd_2761236 := by
    simpa [prefixWord, tailWord_2761236, baseEnd_2761236] using wordTrace_append hprefix tailTrace_2761236
  have hstable : (prefixWord ++ tailWord_2761236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761236).length < 2 ^ (prefixWord ++ tailWord_2761236).sum := by decide
  have hdescent : baseEnd_2761236 < baseStart_2761236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761242 : List Nat := [3, 1, 1, 3, 1, 1, 3, 4, 6]
def baseStart_2761242 : Nat := 118140960795 + 2761242 * 2 ^ 59
def prefixEnd_2761242 : Nat := 4983230072969 + 3 ^ 40 * 2761242 * 2
def baseEnd_2761242 : Nat := 157538261042465651297365

theorem tailTrace_2761242 : CollatzResearch.WordTrace tailWord_2761242 prefixEnd_2761242 157538261042465651297365 := by
  unfold tailWord_2761242
  simp only [CollatzResearch.WordTrace]
  refine ⟨25177692365624822858525495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67140512974999527622734653 25177692365624822858525495)
  ·
    refine ⟨37766538548437234287788243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25177692365624822858525495 37766538548437234287788243)
    ·
      refine ⟨56649807822655851431682365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37766538548437234287788243 56649807822655851431682365)
      ·
        refine ⟨21243677933495944286880887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56649807822655851431682365 21243677933495944286880887)
        ·
          refine ⟨31865516900243916430321331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21243677933495944286880887 31865516900243916430321331)
          ·
            refine ⟨47798275350365874645481997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31865516900243916430321331 47798275350365874645481997)
            ·
              refine ⟨17924353256387202992055749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47798275350365874645481997 17924353256387202992055749)
              ·
                refine ⟨3360816235572600561010453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17924353256387202992055749 3360816235572600561010453)
                ·
                  refine ⟨157538261042465651297365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3360816235572600561010453 157538261042465651297365)
                  ·
                    rfl

theorem cell23_2761242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 6].length) (baseStart_2761242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761242 prefixEnd_2761242 := by exact prefixLift 2761242
  have htrace : WordTrace (prefixWord ++ tailWord_2761242) baseStart_2761242 baseEnd_2761242 := by
    simpa [prefixWord, tailWord_2761242, baseEnd_2761242] using wordTrace_append hprefix tailTrace_2761242
  have hstable : (prefixWord ++ tailWord_2761242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761242).length < 2 ^ (prefixWord ++ tailWord_2761242).sum := by decide
  have hdescent : baseEnd_2761242 < baseStart_2761242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761272 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 3, 5]
def baseStart_2761272 : Nat := 118140960795 + 2761272 * 2 ^ 59
def prefixEnd_2761272 : Nat := 4983230072969 + 3 ^ 40 * 2761272 * 2
def baseEnd_2761272 : Nat := 472619917933941914767049

theorem tailTrace_2761272 : CollatzResearch.WordTrace tailWord_2761272 prefixEnd_2761272 472619917933941914767049 := by
  unfold tailWord_2761272
  simp only [CollatzResearch.WordTrace]
  refine ⟨50355931826195303278847035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67141242434927071038462713 50355931826195303278847035)
  ·
    refine ⟨75533897739292954918270553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50355931826195303278847035 75533897739292954918270553)
    ·
      refine ⟨56650423304469716188702915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75533897739292954918270553 56650423304469716188702915)
      ·
        refine ⟨84975634956704574283054373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56650423304469716188702915 84975634956704574283054373)
        ·
          refine ⟨15932931554382107678072695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84975634956704574283054373 15932931554382107678072695)
          ·
            refine ⟨23899397331573161517109043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15932931554382107678072695 23899397331573161517109043)
            ·
              refine ⟨35849095997359742275663565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23899397331573161517109043 35849095997359742275663565)
              ·
                refine ⟨13443410999009903353373837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35849095997359742275663565 13443410999009903353373837)
                ·
                  refine ⟨5041279124628713757515189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13443410999009903353373837 5041279124628713757515189)
                  ·
                    refine ⟨472619917933941914767049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5041279124628713757515189 472619917933941914767049)
                    ·
                      rfl

theorem cell23_2761272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_2761272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761272 prefixEnd_2761272 := by exact prefixLift 2761272
  have htrace : WordTrace (prefixWord ++ tailWord_2761272) baseStart_2761272 baseEnd_2761272 := by
    simpa [prefixWord, tailWord_2761272, baseEnd_2761272] using wordTrace_append hprefix tailTrace_2761272
  have hstable : (prefixWord ++ tailWord_2761272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761272).length < 2 ^ (prefixWord ++ tailWord_2761272).sum := by decide
  have hdescent : baseEnd_2761272 < baseStart_2761272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761275 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 10]
def baseStart_2761275 : Nat := 118140960795 + 2761275 * 2 ^ 59
def prefixEnd_2761275 : Nat := 4983230072969 + 3 ^ 40 * 2761275 * 2
def baseEnd_2761275 : Nat := 1417861294243789232563633

theorem tailTrace_2761275 : CollatzResearch.WordTrace tailWord_2761275 prefixEnd_2761275 1417861294243789232563633 := by
  unfold tailWord_2761275
  simp only [CollatzResearch.WordTrace]
  refine ⟨100711973071379738070053279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67141315380919825380035519 100711973071379738070053279)
  ·
    refine ⟨151067959607069607105079919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100711973071379738070053279 151067959607069607105079919)
    ·
      refine ⟨226601939410604410657619879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151067959607069607105079919 226601939410604410657619879)
      ·
        refine ⟨339902909115906615986429819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226601939410604410657619879 339902909115906615986429819)
        ·
          refine ⟨509854363673859923979644729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339902909115906615986429819 509854363673859923979644729)
          ·
            refine ⟨382390772755394942984733547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509854363673859923979644729 382390772755394942984733547)
            ·
              refine ⟨573586159133092414477100321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382390772755394942984733547 573586159133092414477100321)
              ·
                refine ⟨430189619349819310857825241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 573586159133092414477100321 430189619349819310857825241)
                ·
                  refine ⟨322642214512364483143368931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430189619349819310857825241 322642214512364483143368931)
                  ·
                    refine ⟨483963321768546724715053397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 322642214512364483143368931 483963321768546724715053397)
                    ·
                      refine ⟨1417861294243789232563633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 483963321768546724715053397 1417861294243789232563633)
                      ·
                        rfl

theorem cell23_2761275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 10].length) (baseStart_2761275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761275 prefixEnd_2761275 := by exact prefixLift 2761275
  have htrace : WordTrace (prefixWord ++ tailWord_2761275) baseStart_2761275 baseEnd_2761275 := by
    simpa [prefixWord, tailWord_2761275, baseEnd_2761275] using wordTrace_append hprefix tailTrace_2761275
  have hstable : (prefixWord ++ tailWord_2761275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761275).length < 2 ^ (prefixWord ++ tailWord_2761275).sum := by decide
  have hdescent : baseEnd_2761275 < baseStart_2761275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761279 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 1, 5, 2]
def baseStart_2761279 : Nat := 118140960795 + 2761279 * 2 ^ 59
def prefixEnd_2761279 : Nat := 4983230072969 + 3 ^ 40 * 2761279 * 2
def baseEnd_2761279 : Nat := 1417863348166407216913615

theorem tailTrace_2761279 : CollatzResearch.WordTrace tailWord_2761279 prefixEnd_2761279 1417863348166407216913615 := by
  unfold tailWord_2761279
  simp only [CollatzResearch.WordTrace]
  refine ⟨100712118963365246753198891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67141412642243497835465927 100712118963365246753198891)
  ·
    refine ⟨151068178445047870129798337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100712118963365246753198891 151068178445047870129798337)
    ·
      refine ⟨113301133833785902597348753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151068178445047870129798337 113301133833785902597348753)
      ·
        refine ⟨84975850375339426948011565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113301133833785902597348753 84975850375339426948011565)
        ·
          refine ⟨31865943890752285105504337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84975850375339426948011565 31865943890752285105504337)
          ·
            refine ⟨23899457918064213829128253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31865943890752285105504337 23899457918064213829128253)
            ·
              refine ⟨8962296719274080185923095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23899457918064213829128253 8962296719274080185923095)
              ·
                refine ⟨13443445078911120278884643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8962296719274080185923095 13443445078911120278884643)
                ·
                  refine ⟨20165167618366680418326965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13443445078911120278884643 20165167618366680418326965)
                  ·
                    refine ⟨1890484464221876289218153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20165167618366680418326965 1890484464221876289218153)
                    ·
                      refine ⟨1417863348166407216913615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1890484464221876289218153 1417863348166407216913615)
                      ·
                        rfl

theorem cell23_2761279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 5, 2].length) (baseStart_2761279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761279 prefixEnd_2761279 := by exact prefixLift 2761279
  have htrace : WordTrace (prefixWord ++ tailWord_2761279) baseStart_2761279 baseEnd_2761279 := by
    simpa [prefixWord, tailWord_2761279, baseEnd_2761279] using wordTrace_append hprefix tailTrace_2761279
  have hstable : (prefixWord ++ tailWord_2761279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761279).length < 2 ^ (prefixWord ++ tailWord_2761279).sum := by decide
  have hdescent : baseEnd_2761279 < baseStart_2761279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761312 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 5]
def baseStart_2761312 : Nat := 118140960795 + 2761312 * 2 ^ 59
def prefixEnd_2761312 : Nat := 4983230072969 + 3 ^ 40 * 2761312 * 2
def baseEnd_2761312 : Nat := 1417880293028005587800963

theorem tailTrace_2761312 : CollatzResearch.WordTrace tailWord_2761312 prefixEnd_2761312 1417880293028005587800963 := by
  unfold tailWord_2761312
  simp only [CollatzResearch.WordTrace]
  refine ⟨50356661286122846694575095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67142215048163795592766793 50356661286122846694575095)
  ·
    refine ⟨75534991929184270041862643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50356661286122846694575095 75534991929184270041862643)
    ·
      refine ⟨113302487893776405062793965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75534991929184270041862643 113302487893776405062793965)
      ·
        refine ⟨42488432960166151898547737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113302487893776405062793965 42488432960166151898547737)
        ·
          refine ⟨31866324720124613923910803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42488432960166151898547737 31866324720124613923910803)
          ·
            refine ⟨47799487080186920885866205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31866324720124613923910803 47799487080186920885866205)
            ·
              refine ⟨17924807655070095332199827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47799487080186920885866205 17924807655070095332199827)
              ·
                refine ⟨26887211482605142998299741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17924807655070095332199827 26887211482605142998299741)
                ·
                  refine ⟨10082704305976928624362403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26887211482605142998299741 10082704305976928624362403)
                  ·
                    refine ⟨15124056458965392936543605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10082704305976928624362403 15124056458965392936543605)
                    ·
                      refine ⟨1417880293028005587800963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15124056458965392936543605 1417880293028005587800963)
                      ·
                        rfl

theorem cell23_2761312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_2761312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761312 prefixEnd_2761312 := by exact prefixLift 2761312
  have htrace : WordTrace (prefixWord ++ tailWord_2761312) baseStart_2761312 baseEnd_2761312 := by
    simpa [prefixWord, tailWord_2761312, baseEnd_2761312] using wordTrace_append hprefix tailTrace_2761312
  have hstable : (prefixWord ++ tailWord_2761312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761312).length < 2 ^ (prefixWord ++ tailWord_2761312).sum := by decide
  have hdescent : baseEnd_2761312 < baseStart_2761312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761326 : List Nat := [4, 1, 2, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_2761326 : Nat := 118140960795 + 2761326 * 2 ^ 59
def prefixEnd_2761326 : Nat := 4983230072969 + 3 ^ 40 * 2761326 * 2
def baseEnd_2761326 : Nat := 1417887481757168533025899

theorem tailTrace_2761326 : CollatzResearch.WordTrace tailWord_2761326 prefixEnd_2761326 1417887481757168533025899 := by
  unfold tailWord_2761326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12589229149274371722519979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67142555462796649186773221 12589229149274371722519979)
  ·
    refine ⟨18883843723911557583779969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12589229149274371722519979 18883843723911557583779969)
    ·
      refine ⟨14162882792933668187834977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18883843723911557583779969 14162882792933668187834977)
      ·
        refine ⟨10622162094700251140876233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14162882792933668187834977 10622162094700251140876233)
        ·
          refine ⟨7966621571025188355657175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10622162094700251140876233 7966621571025188355657175)
          ·
            refine ⟨11949932356537782533485763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7966621571025188355657175 11949932356537782533485763)
            ·
              refine ⟨17924898534806673800228645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11949932356537782533485763 17924898534806673800228645)
              ·
                refine ⟨3360918475276251337542871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17924898534806673800228645 3360918475276251337542871)
                ·
                  refine ⟨5041377712914377006314307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3360918475276251337542871 5041377712914377006314307)
                  ·
                    refine ⟨7562066569371565509471461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5041377712914377006314307 7562066569371565509471461)
                    ·
                      refine ⟨1417887481757168533025899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7562066569371565509471461 1417887481757168533025899)
                      ·
                        rfl

theorem cell23_2761326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_2761326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761326 prefixEnd_2761326 := by exact prefixLift 2761326
  have htrace : WordTrace (prefixWord ++ tailWord_2761326) baseStart_2761326 baseEnd_2761326 := by
    simpa [prefixWord, tailWord_2761326, baseEnd_2761326] using wordTrace_append hprefix tailTrace_2761326
  have hstable : (prefixWord ++ tailWord_2761326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761326).length < 2 ^ (prefixWord ++ tailWord_2761326).sum := by decide
  have hdescent : baseEnd_2761326 < baseStart_2761326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761343 : List Nat := [1, 1, 2, 2, 1, 1, 1, 9, 1, 2, 2]
def baseStart_2761343 : Nat := 118140960795 + 2761343 * 2 ^ 59
def prefixEnd_2761343 : Nat := 4983230072969 + 3 ^ 40 * 2761343 * 2
def baseEnd_2761343 : Nat := 1417896210928294966513321

theorem tailTrace_2761343 : CollatzResearch.WordTrace tailWord_2761343 prefixEnd_2761343 1417896210928294966513321 := by
  unfold tailWord_2761343
  simp only [CollatzResearch.WordTrace]
  refine ⟨100714453235133385683528683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67142968823422257122352455 100714453235133385683528683)
  ·
    refine ⟨151071679852700078525293025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100714453235133385683528683 151071679852700078525293025)
    ·
      refine ⟨113303759889525058893969769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151071679852700078525293025 113303759889525058893969769)
      ·
        refine ⟨84977819917143794170477327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113303759889525058893969769 84977819917143794170477327)
        ·
          refine ⟨127466729875715691255715991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84977819917143794170477327 127466729875715691255715991)
          ·
            refine ⟨191200094813573536883573987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127466729875715691255715991 191200094813573536883573987)
            ·
              refine ⟨286800142220360305325360981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191200094813573536883573987 286800142220360305325360981)
              ·
                refine ⟨1680469583322423664015787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 286800142220360305325360981 1680469583322423664015787)
                ·
                  refine ⟨2520704374983635496023681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1680469583322423664015787 2520704374983635496023681)
                  ·
                    refine ⟨1890528281237726622017761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2520704374983635496023681 1890528281237726622017761)
                    ·
                      refine ⟨1417896210928294966513321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1890528281237726622017761 1417896210928294966513321)
                      ·
                        rfl

theorem cell23_2761343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 1, 2, 2].length) (baseStart_2761343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761343 prefixEnd_2761343 := by exact prefixLift 2761343
  have htrace : WordTrace (prefixWord ++ tailWord_2761343) baseStart_2761343 baseEnd_2761343 := by
    simpa [prefixWord, tailWord_2761343, baseEnd_2761343] using wordTrace_append hprefix tailTrace_2761343
  have hstable : (prefixWord ++ tailWord_2761343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761343).length < 2 ^ (prefixWord ++ tailWord_2761343).sum := by decide
  have hdescent : baseEnd_2761343 < baseStart_2761343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761392 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 4, 6]
def baseStart_2761392 : Nat := 118140960795 + 2761392 * 2 ^ 59
def prefixEnd_2761392 : Nat := 4983230072969 + 3 ^ 40 * 2761392 * 2
def baseEnd_2761392 : Nat := 472640457160121758266865

theorem tailTrace_2761392 : CollatzResearch.WordTrace tailWord_2761392 prefixEnd_2761392 472640457160121758266865 := by
  unfold tailWord_2761392
  simp only [CollatzResearch.WordTrace]
  refine ⟨50358120205977933526031215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67144160274637244701374953 50358120205977933526031215)
  ·
    refine ⟨75537180308966900289046823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50358120205977933526031215 75537180308966900289046823)
    ·
      refine ⟨113305770463450350433570235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75537180308966900289046823 113305770463450350433570235)
      ·
        refine ⟨169958655695175525650355353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113305770463450350433570235 169958655695175525650355353)
        ·
          refine ⟨127468991771381644237766515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169958655695175525650355353 127468991771381644237766515)
          ·
            refine ⟨191203487657072466356649773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127468991771381644237766515 191203487657072466356649773)
            ·
              refine ⟨71701307871402174883743665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191203487657072466356649773 71701307871402174883743665)
              ·
                refine ⟨53775980903551631162807749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71701307871402174883743665 53775980903551631162807749)
                ·
                  refine ⟨10082996419415930843026453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53775980903551631162807749 10082996419415930843026453)
                  ·
                    refine ⟨472640457160121758266865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10082996419415930843026453 472640457160121758266865)
                    ·
                      rfl

theorem cell23_2761392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4, 6].length) (baseStart_2761392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761392 prefixEnd_2761392 := by exact prefixLift 2761392
  have htrace : WordTrace (prefixWord ++ tailWord_2761392) baseStart_2761392 baseEnd_2761392 := by
    simpa [prefixWord, tailWord_2761392, baseEnd_2761392] using wordTrace_append hprefix tailTrace_2761392
  have hstable : (prefixWord ++ tailWord_2761392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761392).length < 2 ^ (prefixWord ++ tailWord_2761392).sum := by decide
  have hdescent : baseEnd_2761392 < baseStart_2761392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761393 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2761393 : Nat := 118140960795 + 2761393 * 2 ^ 59
def prefixEnd_2761393 : Nat := 4983230072969 + 3 ^ 40 * 2761393 * 2
def baseEnd_2761393 : Nat := 1417921884961019770888091

theorem tailTrace_2761393 : CollatzResearch.WordTrace tailWord_2761393 prefixEnd_2761393 1417921884961019770888091 := by
  unfold tailWord_2761393
  simp only [CollatzResearch.WordTrace]
  refine ⟨100716276884952244222848833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67144184589968162815232555 100716276884952244222848833)
  ·
    refine ⟨75537207663714183167136625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100716276884952244222848833 75537207663714183167136625)
    ·
      refine ⟨56652905747785637375352469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75537207663714183167136625 56652905747785637375352469)
      ·
        refine ⟨2655604956927451751969647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56652905747785637375352469 2655604956927451751969647)
        ·
          refine ⟨3983407435391177627954471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2655604956927451751969647 3983407435391177627954471)
          ·
            refine ⟨5975111153086766441931707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983407435391177627954471 5975111153086766441931707)
            ·
              refine ⟨8962666729630149662897561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5975111153086766441931707 8962666729630149662897561)
              ·
                refine ⟨6722000047222612247173171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8962666729630149662897561 6722000047222612247173171)
                ·
                  refine ⟨10083000070833918370759757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6722000047222612247173171 10083000070833918370759757)
                  ·
                    refine ⟨3781125026562719389034909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10083000070833918370759757 3781125026562719389034909)
                    ·
                      refine ⟨1417921884961019770888091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3781125026562719389034909 1417921884961019770888091)
                      ·
                        rfl

theorem cell23_2761393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2761393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761393 prefixEnd_2761393 := by exact prefixLift 2761393
  have htrace : WordTrace (prefixWord ++ tailWord_2761393) baseStart_2761393 baseEnd_2761393 := by
    simpa [prefixWord, tailWord_2761393, baseEnd_2761393] using wordTrace_append hprefix tailTrace_2761393
  have hstable : (prefixWord ++ tailWord_2761393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761393).length < 2 ^ (prefixWord ++ tailWord_2761393).sum := by decide
  have hdescent : baseEnd_2761393 < baseStart_2761393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761426 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 2, 6]
def baseStart_2761426 : Nat := 118140960795 + 2761426 * 2 ^ 59
def prefixEnd_2761426 : Nat := 4983230072969 + 3 ^ 40 * 2761426 * 2
def baseEnd_2761426 : Nat := 472646276607539380591813

theorem tailTrace_2761426 : CollatzResearch.WordTrace tailWord_2761426 prefixEnd_2761426 472646276607539380591813 := by
  unfold tailWord_2761426
  simp only [CollatzResearch.WordTrace]
  refine ⟨25179370123458172714700033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67144986995888460572533421 25179370123458172714700033)
  ·
    refine ⟨18884527592593629536025025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25179370123458172714700033 18884527592593629536025025)
    ·
      refine ⟨14163395694445222152018769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18884527592593629536025025 14163395694445222152018769)
      ·
        refine ⟨10622546770833916614014077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14163395694445222152018769 10622546770833916614014077)
        ·
          refine ⟨3983455039062718730255279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10622546770833916614014077 3983455039062718730255279)
          ·
            refine ⟨5975182558594078095382919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983455039062718730255279 5975182558594078095382919)
            ·
              refine ⟨8962773837891117143074379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5975182558594078095382919 8962773837891117143074379)
              ·
                refine ⟨13444160756836675714611569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8962773837891117143074379 13444160756836675714611569)
                ·
                  refine ⟨10083120567627506785958677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13444160756836675714611569 10083120567627506785958677)
                  ·
                    refine ⟨472646276607539380591813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10083120567627506785958677 472646276607539380591813)
                    ·
                      rfl

theorem cell23_2761426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_2761426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761426 prefixEnd_2761426 := by exact prefixLift 2761426
  have htrace : WordTrace (prefixWord ++ tailWord_2761426) baseStart_2761426 baseEnd_2761426 := by
    simpa [prefixWord, tailWord_2761426, baseEnd_2761426] using wordTrace_append hprefix tailTrace_2761426
  have hstable : (prefixWord ++ tailWord_2761426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761426).length < 2 ^ (prefixWord ++ tailWord_2761426).sum := by decide
  have hdescent : baseEnd_2761426 < baseStart_2761426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761433 : List Nat := [1, 2, 1, 2, 3, 2, 1, 5, 2, 2, 2]
def baseStart_2761433 : Nat := 118140960795 + 2761433 * 2 ^ 59
def prefixEnd_2761433 : Nat := 4983230072969 + 3 ^ 40 * 2761433 * 2
def baseEnd_2761433 : Nat := 1417942424187199614387907

theorem tailTrace_2761433 : CollatzResearch.WordTrace tailWord_2761433 prefixEnd_2761433 1417942424187199614387907 := by
  unfold tailWord_2761433
  simp only [CollatzResearch.WordTrace]
  refine ⟨100717735804807331054304953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67145157203204887369536635 100717735804807331054304953)
  ·
    refine ⟨75538301853605498290728715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100717735804807331054304953 75538301853605498290728715)
    ·
      refine ⟨113307452780408247436093073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75538301853605498290728715 113307452780408247436093073)
      ·
        refine ⟨84980589585306185577069805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113307452780408247436093073 84980589585306185577069805)
        ·
          refine ⟨31867721094489819591401177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84980589585306185577069805 31867721094489819591401177)
          ·
            refine ⟨23900790820867364693550883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31867721094489819591401177 23900790820867364693550883)
            ·
              refine ⟨35851186231301047040326325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23900790820867364693550883 35851186231301047040326325)
              ·
                refine ⟨3361048709184473160030593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35851186231301047040326325 3361048709184473160030593)
                ·
                  refine ⟨2520786531888354870022945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3361048709184473160030593 2520786531888354870022945)
                  ·
                    refine ⟨1890589898916266152517209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2520786531888354870022945 1890589898916266152517209)
                    ·
                      refine ⟨1417942424187199614387907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1890589898916266152517209 1417942424187199614387907)
                      ·
                        rfl

theorem cell23_2761433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 2, 2].length) (baseStart_2761433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761433 prefixEnd_2761433 := by exact prefixLift 2761433
  have htrace : WordTrace (prefixWord ++ tailWord_2761433) baseStart_2761433 baseEnd_2761433 := by
    simpa [prefixWord, tailWord_2761433, baseEnd_2761433] using wordTrace_append hprefix tailTrace_2761433
  have hstable : (prefixWord ++ tailWord_2761433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761433).length < 2 ^ (prefixWord ++ tailWord_2761433).sum := by decide
  have hdescent : baseEnd_2761433 < baseStart_2761433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761439 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 7]
def baseStart_2761439 : Nat := 118140960795 + 2761439 * 2 ^ 59
def prefixEnd_2761439 : Nat := 4983230072969 + 3 ^ 40 * 2761439 * 2
def baseEnd_2761439 : Nat := 157549500563458510101431

theorem tailTrace_2761439 : CollatzResearch.WordTrace tailWord_2761439 prefixEnd_2761439 157549500563458510101431 := by
  unfold tailWord_2761439
  simp only [CollatzResearch.WordTrace]
  refine ⟨100717954642785594079023371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67145303095190396052682247 100717954642785594079023371)
  ·
    refine ⟨151076931964178391118535057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100717954642785594079023371 151076931964178391118535057)
    ·
      refine ⟨113307698973133793338901293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151076931964178391118535057 113307698973133793338901293)
      ·
        refine ⟨42490387114925172502087985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113307698973133793338901293 42490387114925172502087985)
        ·
          refine ⟨31867790336193879376565989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42490387114925172502087985 31867790336193879376565989)
          ·
            refine ⟨5975210688036352383106123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31867790336193879376565989 5975210688036352383106123)
            ·
              refine ⟨8962816032054528574659185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5975210688036352383106123 8962816032054528574659185)
              ·
                refine ⟨6722112024040896430994389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8962816032054528574659185 6722112024040896430994389)
                ·
                  refine ⟨157549500563458510101431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6722112024040896430994389 157549500563458510101431)
                  ·
                    rfl

theorem cell23_2761439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 7].length) (baseStart_2761439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761439 prefixEnd_2761439 := by exact prefixLift 2761439
  have htrace : WordTrace (prefixWord ++ tailWord_2761439) baseStart_2761439 baseEnd_2761439 := by
    simpa [prefixWord, tailWord_2761439, baseEnd_2761439] using wordTrace_append hprefix tailTrace_2761439
  have hstable : (prefixWord ++ tailWord_2761439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761439).length < 2 ^ (prefixWord ++ tailWord_2761439).sum := by decide
  have hdescent : baseEnd_2761439 < baseStart_2761439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761456 : List Nat := [2, 1, 1, 1, 3, 1, 6, 3, 5]
def baseStart_2761456 : Nat := 118140960795 + 2761456 * 2 ^ 59
def prefixEnd_2761456 : Nat := 4983230072969 + 3 ^ 40 * 2761456 * 2
def baseEnd_2761456 : Nat := 157550470471361447155589

theorem tailTrace_2761456 : CollatzResearch.WordTrace tailWord_2761456 prefixEnd_2761456 157550470471361447155589 := by
  unfold tailWord_2761456
  simp only [CollatzResearch.WordTrace]
  refine ⟨50359287341862002991196111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67145716455816003988261481 50359287341862002991196111)
  ·
    refine ⟨75538931012793004486794167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50359287341862002991196111 75538931012793004486794167)
    ·
      refine ⟨113308396519189506730191251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75538931012793004486794167 113308396519189506730191251)
      ·
        refine ⟨169962594778784260095286877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113308396519189506730191251 169962594778784260095286877)
        ·
          refine ⟨63735973042044097535732579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169962594778784260095286877 63735973042044097535732579)
          ·
            refine ⟨95603959563066146303598869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63735973042044097535732579 95603959563066146303598869)
            ·
              refine ⟨4481435604518725607981197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95603959563066146303598869 4481435604518725607981197)
              ·
                refine ⟨1680538351694522102992949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4481435604518725607981197 1680538351694522102992949)
                ·
                  refine ⟨157550470471361447155589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1680538351694522102992949 157550470471361447155589)
                  ·
                    rfl

theorem cell23_2761456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 5].length) (baseStart_2761456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761456 prefixEnd_2761456 := by exact prefixLift 2761456
  have htrace : WordTrace (prefixWord ++ tailWord_2761456) baseStart_2761456 baseEnd_2761456 := by
    simpa [prefixWord, tailWord_2761456, baseEnd_2761456] using wordTrace_append hprefix tailTrace_2761456
  have hstable : (prefixWord ++ tailWord_2761456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761456).length < 2 ^ (prefixWord ++ tailWord_2761456).sum := by decide
  have hdescent : baseEnd_2761456 < baseStart_2761456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761461 : List Nat := [1, 3, 6, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_2761461 : Nat := 118140960795 + 2761461 * 2 ^ 59
def prefixEnd_2761461 : Nat := 4983230072969 + 3 ^ 40 * 2761461 * 2
def baseEnd_2761461 : Nat := 1417956801645525504837779

theorem tailTrace_2761461 : CollatzResearch.WordTrace tailWord_2761461 prefixEnd_2761461 1417956801645525504837779 := by
  unfold tailWord_2761461
  simp only [CollatzResearch.WordTrace]
  refine ⟨100718757048705891836324237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67145838032470594557549491 100718757048705891836324237)
  ·
    refine ⟨37769533893264709438621589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100718757048705891836324237 37769533893264709438621589)
    ·
      refine ⟨1770446901246783254935387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37769533893264709438621589 1770446901246783254935387)
      ·
        refine ⟨2655670351870174882403081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1770446901246783254935387 2655670351870174882403081)
        ·
          refine ⟨1991752763902631161802311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2655670351870174882403081 1991752763902631161802311)
          ·
            refine ⟨2987629145853946742703467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991752763902631161802311 2987629145853946742703467)
            ·
              refine ⟨4481443718780920114055201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2987629145853946742703467 4481443718780920114055201)
              ·
                refine ⟨3361082789085690085541401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4481443718780920114055201 3361082789085690085541401)
                ·
                  refine ⟨2520812091814267564156051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3361082789085690085541401 2520812091814267564156051)
                  ·
                    refine ⟨3781218137721401346234077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2520812091814267564156051 3781218137721401346234077)
                    ·
                      refine ⟨1417956801645525504837779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3781218137721401346234077 1417956801645525504837779)
                      ·
                        rfl

theorem cell23_2761461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_2761461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761461 prefixEnd_2761461 := by exact prefixLift 2761461
  have htrace : WordTrace (prefixWord ++ tailWord_2761461) baseStart_2761461 baseEnd_2761461 := by
    simpa [prefixWord, tailWord_2761461, baseEnd_2761461] using wordTrace_append hprefix tailTrace_2761461
  have hstable : (prefixWord ++ tailWord_2761461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761461).length < 2 ^ (prefixWord ++ tailWord_2761461).sum := by decide
  have hdescent : baseEnd_2761461 < baseStart_2761461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761469 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 4, 5]
def baseStart_2761469 : Nat := 118140960795 + 2761469 * 2 ^ 59
def prefixEnd_2761469 : Nat := 4983230072969 + 3 ^ 40 * 2761469 * 2
def baseEnd_2761469 : Nat := 472653636496920491179247

theorem tailTrace_2761469 : CollatzResearch.WordTrace tailWord_2761469 prefixEnd_2761469 472653636496920491179247 := by
  unfold tailWord_2761469
  simp only [CollatzResearch.WordTrace]
  refine ⟨100719048832676909202615461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67146032555117939468410307 100719048832676909202615461)
  ·
    refine ⟨18884821656126920475490399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100719048832676909202615461 18884821656126920475490399)
    ·
      refine ⟨28327232484190380713235599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18884821656126920475490399 28327232484190380713235599)
      ·
        refine ⟨42490848726285571069853399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28327232484190380713235599 42490848726285571069853399)
        ·
          refine ⟨63736273089428356604780099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42490848726285571069853399 63736273089428356604780099)
          ·
            refine ⟨95604409634142534907170149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63736273089428356604780099 95604409634142534907170149)
            ·
              refine ⟨17925826806401725295094403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95604409634142534907170149 17925826806401725295094403)
              ·
                refine ⟨26888740209602587942641605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17925826806401725295094403 26888740209602587942641605)
                ·
                  refine ⟨5041638789300485239245301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26888740209602587942641605 5041638789300485239245301)
                  ·
                    refine ⟨472653636496920491179247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5041638789300485239245301 472653636496920491179247)
                    ·
                      rfl

theorem cell23_2761469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_2761469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761469 prefixEnd_2761469 := by exact prefixLift 2761469
  have htrace : WordTrace (prefixWord ++ tailWord_2761469) baseStart_2761469 baseEnd_2761469 := by
    simpa [prefixWord, tailWord_2761469, baseEnd_2761469] using wordTrace_append hprefix tailTrace_2761469
  have hstable : (prefixWord ++ tailWord_2761469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761469).length < 2 ^ (prefixWord ++ tailWord_2761469).sum := by decide
  have hdescent : baseEnd_2761469 < baseStart_2761469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761489 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 4]
def baseStart_2761489 : Nat := 118140960795 + 2761489 * 2 ^ 59
def prefixEnd_2761489 : Nat := 4983230072969 + 3 ^ 40 * 2761489 * 2
def baseEnd_2761489 : Nat := 1417971179103851395287649

theorem tailTrace_2761489 : CollatzResearch.WordTrace tailWord_2761489 prefixEnd_2761489 1417971179103851395287649 := by
  unfold tailWord_2761489
  simp only [CollatzResearch.WordTrace]
  refine ⟨100719778292604452618343521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67146518861736301745562347 100719778292604452618343521)
  ·
    refine ⟨75539833719453339463757641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100719778292604452618343521 75539833719453339463757641)
    ·
      refine ⟨56654875289590004597818231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75539833719453339463757641 56654875289590004597818231)
      ·
        refine ⟨84982312934385006896727347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56654875289590004597818231 84982312934385006896727347)
        ·
          refine ⟨127473469401577510345091021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84982312934385006896727347 127473469401577510345091021)
          ·
            refine ⟨47802551025591566379409133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127473469401577510345091021 47802551025591566379409133)
            ·
              refine ⟨17925956634596837392278425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47802551025591566379409133 17925956634596837392278425)
              ·
                refine ⟨13444467475947628044208819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17925956634596837392278425 13444467475947628044208819)
                ·
                  refine ⟨20166701213921442066313229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13444467475947628044208819 20166701213921442066313229)
                  ·
                    refine ⟨7562512955220540774867461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20166701213921442066313229 7562512955220540774867461)
                    ·
                      refine ⟨1417971179103851395287649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7562512955220540774867461 1417971179103851395287649)
                      ·
                        rfl

theorem cell23_2761489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_2761489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761489 prefixEnd_2761489 := by exact prefixLift 2761489
  have htrace : WordTrace (prefixWord ++ tailWord_2761489) baseStart_2761489 baseEnd_2761489 := by
    simpa [prefixWord, tailWord_2761489, baseEnd_2761489] using wordTrace_append hprefix tailTrace_2761489
  have hstable : (prefixWord ++ tailWord_2761489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761489).length < 2 ^ (prefixWord ++ tailWord_2761489).sum := by decide
  have hdescent : baseEnd_2761489 < baseStart_2761489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761506 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_2761506 : Nat := 118140960795 + 2761506 * 2 ^ 59
def prefixEnd_2761506 : Nat := 4983230072969 + 3 ^ 40 * 2761506 * 2
def baseEnd_2761506 : Nat := 1417979908274977828775071

theorem tailTrace_2761506 : CollatzResearch.WordTrace tailWord_2761506 prefixEnd_2761506 1417979908274977828775071 := by
  unfold tailWord_2761506
  simp only [CollatzResearch.WordTrace]
  refine ⟨25180099583385716130428093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67146932222361909681141581 25180099583385716130428093)
  ·
    refine ⟨9442537343769643548910535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25180099583385716130428093 9442537343769643548910535)
    ·
      refine ⟨14163806015654465323365803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9442537343769643548910535 14163806015654465323365803)
      ·
        refine ⟨21245709023481697985048705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14163806015654465323365803 21245709023481697985048705)
        ·
          refine ⟨15934281767611273488786529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21245709023481697985048705 15934281767611273488786529)
          ·
            refine ⟨11950711325708455116589897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15934281767611273488786529 11950711325708455116589897)
            ·
              refine ⟨8963033494281341337442423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11950711325708455116589897 8963033494281341337442423)
              ·
                refine ⟨13444550241422012006163635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8963033494281341337442423 13444550241422012006163635)
                ·
                  refine ⟨20166825362133018009245453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13444550241422012006163635 20166825362133018009245453)
                  ·
                    refine ⟨7562559510799881753467045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20166825362133018009245453 7562559510799881753467045)
                    ·
                      refine ⟨1417979908274977828775071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7562559510799881753467045 1417979908274977828775071)
                      ·
                        rfl

theorem cell23_2761506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_2761506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761506 prefixEnd_2761506 := by exact prefixLift 2761506
  have htrace : WordTrace (prefixWord ++ tailWord_2761506) baseStart_2761506 baseEnd_2761506 := by
    simpa [prefixWord, tailWord_2761506, baseEnd_2761506] using wordTrace_append hprefix tailTrace_2761506
  have hstable : (prefixWord ++ tailWord_2761506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761506).length < 2 ^ (prefixWord ++ tailWord_2761506).sum := by decide
  have hdescent : baseEnd_2761506 < baseStart_2761506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761569 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_2761569 : Nat := 118140960795 + 2761569 * 2 ^ 59
def prefixEnd_2761569 : Nat := 4983230072969 + 3 ^ 40 * 2761569 * 2
def baseEnd_2761569 : Nat := 1418012257556211082287281

theorem tailTrace_2761569 : CollatzResearch.WordTrace tailWord_2761569 prefixEnd_2761569 1418012257556211082287281 := by
  unfold tailWord_2761569
  simp only [CollatzResearch.WordTrace]
  refine ⟨100722696132314626281255761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67148464088209750854170507 100722696132314626281255761)
  ·
    refine ⟨75542022099235969710941821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100722696132314626281255761 75542022099235969710941821)
    ·
      refine ⟨28328258287213488641603183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75542022099235969710941821 28328258287213488641603183)
      ·
        refine ⟨42492387430820232962404775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28328258287213488641603183 42492387430820232962404775)
        ·
          refine ⟨63738581146230349443607163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42492387430820232962404775 63738581146230349443607163)
          ·
            refine ⟨95607871719345524165410745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63738581146230349443607163 95607871719345524165410745)
            ·
              refine ⟨71705903789509143124058059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95607871719345524165410745 71705903789509143124058059)
              ·
                refine ⟨107558855684263714686087089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71705903789509143124058059 107558855684263714686087089)
                ·
                  refine ⟨80669141763197786014565317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107558855684263714686087089 80669141763197786014565317)
                  ·
                    refine ⟨15125464080599584877730997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80669141763197786014565317 15125464080599584877730997)
                    ·
                      refine ⟨1418012257556211082287281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15125464080599584877730997 1418012257556211082287281)
                      ·
                        rfl

theorem cell23_2761569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_2761569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761569 prefixEnd_2761569 := by exact prefixLift 2761569
  have htrace : WordTrace (prefixWord ++ tailWord_2761569) baseStart_2761569 baseEnd_2761569 := by
    simpa [prefixWord, tailWord_2761569, baseEnd_2761569] using wordTrace_append hprefix tailTrace_2761569
  have hstable : (prefixWord ++ tailWord_2761569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761569).length < 2 ^ (prefixWord ++ tailWord_2761569).sum := by decide
  have hdescent : baseEnd_2761569 < baseStart_2761569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761616 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 3]
def baseStart_2761616 : Nat := 118140960795 + 2761616 * 2 ^ 59
def prefixEnd_2761616 : Nat := 4983230072969 + 3 ^ 40 * 2761616 * 2
def baseEnd_2761616 : Nat := 1418036391146972398399565

theorem tailTrace_2761616 : CollatzResearch.WordTrace tailWord_2761616 prefixEnd_2761616 1418036391146972398399565 := by
  unfold tailWord_2761616
  simp only [CollatzResearch.WordTrace]
  refine ⟨50362205181572176654108351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67149606908762902205477801 50362205181572176654108351)
  ·
    refine ⟨75543307772358264981162527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50362205181572176654108351 75543307772358264981162527)
    ·
      refine ⟨113314961658537397471743791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75543307772358264981162527 113314961658537397471743791)
      ·
        refine ⟨169972442487806096207615687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113314961658537397471743791 169972442487806096207615687)
        ·
          refine ⟨254958663731709144311423531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169972442487806096207615687 254958663731709144311423531)
          ·
            refine ⟨382437995597563716467135297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254958663731709144311423531 382437995597563716467135297)
            ·
              refine ⟨286828496698172787350351473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382437995597563716467135297 286828496698172787350351473)
              ·
                refine ⟨215121372523629590512763605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286828496698172787350351473 215121372523629590512763605)
                ·
                  refine ⟨5041907168522568527642897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 215121372523629590512763605 5041907168522568527642897)
                  ·
                    refine ⟨3781430376391926395732173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5041907168522568527642897 3781430376391926395732173)
                    ·
                      refine ⟨1418036391146972398399565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3781430376391926395732173 1418036391146972398399565)
                      ·
                        rfl

theorem cell23_2761616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 3].length) (baseStart_2761616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761616 prefixEnd_2761616 := by exact prefixLift 2761616
  have htrace : WordTrace (prefixWord ++ tailWord_2761616) baseStart_2761616 baseEnd_2761616 := by
    simpa [prefixWord, tailWord_2761616, baseEnd_2761616] using wordTrace_append hprefix tailTrace_2761616
  have hstable : (prefixWord ++ tailWord_2761616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761616).length < 2 ^ (prefixWord ++ tailWord_2761616).sum := by decide
  have hdescent : baseEnd_2761616 < baseStart_2761616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761676 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2761676 : Nat := 118140960795 + 2761676 * 2 ^ 59
def prefixEnd_2761676 : Nat := 4983230072969 + 3 ^ 40 * 2761676 * 2
def baseEnd_2761676 : Nat := 1418067199986242163649289

theorem tailTrace_2761676 : CollatzResearch.WordTrace tailWord_2761676 prefixEnd_2761676 1418067199986242163649289 := by
  unfold tailWord_2761676
  simp only [CollatzResearch.WordTrace]
  refine ⟨50363299371463491777700441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67151065828617989036933921 50363299371463491777700441)
  ·
    refine ⟨37772474528597618833275331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50363299371463491777700441 37772474528597618833275331)
    ·
      refine ⟨56658711792896428249912997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37772474528597618833275331 56658711792896428249912997)
      ·
        refine ⟨10623508461168080296858687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56658711792896428249912997 10623508461168080296858687)
        ·
          refine ⟨15935262691752120445288031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10623508461168080296858687 15935262691752120445288031)
          ·
            refine ⟨23902894037628180667932047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15935262691752120445288031 23902894037628180667932047)
            ·
              refine ⟨35854341056442271001898071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23902894037628180667932047 35854341056442271001898071)
              ·
                refine ⟨53781511584663406502847107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35854341056442271001898071 53781511584663406502847107)
                ·
                  refine ⟨80672267376995109754270661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53781511584663406502847107 80672267376995109754270661)
                  ·
                    refine ⟨15126050133186583078925749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80672267376995109754270661 15126050133186583078925749)
                    ·
                      refine ⟨1418067199986242163649289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15126050133186583078925749 1418067199986242163649289)
                      ·
                        rfl

theorem cell23_2761676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2761676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761676 prefixEnd_2761676 := by exact prefixLift 2761676
  have htrace : WordTrace (prefixWord ++ tailWord_2761676) baseStart_2761676 baseEnd_2761676 := by
    simpa [prefixWord, tailWord_2761676, baseEnd_2761676] using wordTrace_append hprefix tailTrace_2761676
  have hstable : (prefixWord ++ tailWord_2761676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761676).length < 2 ^ (prefixWord ++ tailWord_2761676).sum := by decide
  have hdescent : baseEnd_2761676 < baseStart_2761676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761698 : List Nat := [3, 3, 3, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_2761698 : Nat := 118140960795 + 2761698 * 2 ^ 59
def prefixEnd_2761698 : Nat := 4983230072969 + 3 ^ 40 * 2761698 * 2
def baseEnd_2761698 : Nat := 1418078496560641077574189

theorem tailTrace_2761698 : CollatzResearch.WordTrace tailWord_2761698 prefixEnd_2761698 1418078496560641077574189 := by
  unfold tailWord_2761698
  simp only [CollatzResearch.WordTrace]
  refine ⟨25181850287211820328175437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67151600765898187541801165 25181850287211820328175437)
  ·
    refine ⟨9443193857704432623065789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25181850287211820328175437 9443193857704432623065789)
    ·
      refine ⟨3541197696639162233649671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9443193857704432623065789 3541197696639162233649671)
      ·
        refine ⟨5311796544958743350474507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3541197696639162233649671 5311796544958743350474507)
        ·
          refine ⟨7967694817438115025711761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5311796544958743350474507 7967694817438115025711761)
          ·
            refine ⟨5975771113078586269283821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7967694817438115025711761 5975771113078586269283821)
            ·
              refine ⟨2240914167404469850981433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5975771113078586269283821 2240914167404469850981433)
              ·
                refine ⟨1680685625553352388236075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2240914167404469850981433 1680685625553352388236075)
                ·
                  refine ⟨2521028438330028582354113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1680685625553352388236075 2521028438330028582354113)
                  ·
                    refine ⟨1890771328747521436765585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2521028438330028582354113 1890771328747521436765585)
                    ·
                      refine ⟨1418078496560641077574189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1890771328747521436765585 1418078496560641077574189)
                      ·
                        rfl

theorem cell23_2761698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_2761698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761698 prefixEnd_2761698 := by exact prefixLift 2761698
  have htrace : WordTrace (prefixWord ++ tailWord_2761698) baseStart_2761698 baseEnd_2761698 := by
    simpa [prefixWord, tailWord_2761698, baseEnd_2761698] using wordTrace_append hprefix tailTrace_2761698
  have hstable : (prefixWord ++ tailWord_2761698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761698).length < 2 ^ (prefixWord ++ tailWord_2761698).sum := by decide
  have hdescent : baseEnd_2761698 < baseStart_2761698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761714 : List Nat := [3, 2, 1, 5, 1, 1, 1, 3, 2, 1, 3]
def baseStart_2761714 : Nat := 118140960795 + 2761714 * 2 ^ 59
def prefixEnd_2761714 : Nat := 4983230072969 + 3 ^ 40 * 2761714 * 2
def baseEnd_2761714 : Nat := 1418086712251113014974115

theorem tailTrace_2761714 : CollatzResearch.WordTrace tailWord_2761714 prefixEnd_2761714 1418086712251113014974115 := by
  unfold tailWord_2761714
  simp only [CollatzResearch.WordTrace]
  refine ⟨25181996179197329011321049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67151989811192877363522797 25181996179197329011321049)
  ·
    refine ⟨18886497134397996758490787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25181996179197329011321049 18886497134397996758490787)
    ·
      refine ⟨28329745701596995137736181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18886497134397996758490787 28329745701596995137736181)
      ·
        refine ⟨2655913659524718294162767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28329745701596995137736181 2655913659524718294162767)
        ·
          refine ⟨3983870489287077441244151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2655913659524718294162767 3983870489287077441244151)
          ·
            refine ⟨5975805733930616161866227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983870489287077441244151 5975805733930616161866227)
            ·
              refine ⟨8963708600895924242799341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5975805733930616161866227 8963708600895924242799341)
              ·
                refine ⟨3361390725335971591049753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8963708600895924242799341 3361390725335971591049753)
                ·
                  refine ⟨2521043044001978693287315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3361390725335971591049753 2521043044001978693287315)
                  ·
                    refine ⟨3781564566002968039930973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2521043044001978693287315 3781564566002968039930973)
                    ·
                      refine ⟨1418086712251113014974115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3781564566002968039930973 1418086712251113014974115)
                      ·
                        rfl

theorem cell23_2761714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_2761714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761714 prefixEnd_2761714 := by exact prefixLift 2761714
  have htrace : WordTrace (prefixWord ++ tailWord_2761714) baseStart_2761714 baseEnd_2761714 := by
    simpa [prefixWord, tailWord_2761714, baseEnd_2761714] using wordTrace_append hprefix tailTrace_2761714
  have hstable : (prefixWord ++ tailWord_2761714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761714).length < 2 ^ (prefixWord ++ tailWord_2761714).sum := by decide
  have hdescent : baseEnd_2761714 < baseStart_2761714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761790 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_2761790 : Nat := 118140960795 + 2761790 * 2 ^ 59
def prefixEnd_2761790 : Nat := 4983230072969 + 3 ^ 40 * 2761790 * 2
def baseEnd_2761790 : Nat := 472708578926951572541255

theorem tailTrace_2761790 : CollatzResearch.WordTrace tailWord_2761790 prefixEnd_2761790 472708578926951572541255 := by
  unfold tailWord_2761790
  simp only [CollatzResearch.WordTrace]
  refine ⟨12591344583064247628131353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67153837776342654016700549 12591344583064247628131353)
  ·
    refine ⟨9443508437298185721098515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12591344583064247628131353 9443508437298185721098515)
    ·
      refine ⟨14165262655947278581647773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9443508437298185721098515 14165262655947278581647773)
      ·
        refine ⟨5311973495980229468117915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14165262655947278581647773 5311973495980229468117915)
        ·
          refine ⟨7967960243970344202176873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5311973495980229468117915 7967960243970344202176873)
          ·
            refine ⟨5975970182977758151632655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7967960243970344202176873 5975970182977758151632655)
            ·
              refine ⟨8963955274466637227448983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5975970182977758151632655 8963955274466637227448983)
              ·
                refine ⟨13445932911699955841173475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8963955274466637227448983 13445932911699955841173475)
                ·
                  refine ⟨20168899367549933761760213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13445932911699955841173475 20168899367549933761760213)
                  ·
                    refine ⟨472708578926951572541255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20168899367549933761760213 472708578926951572541255)
                    ·
                      rfl

theorem cell23_2761790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_2761790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761790 prefixEnd_2761790 := by exact prefixLift 2761790
  have htrace : WordTrace (prefixWord ++ tailWord_2761790) baseStart_2761790 baseEnd_2761790 := by
    simpa [prefixWord, tailWord_2761790, baseEnd_2761790] using wordTrace_append hprefix tailTrace_2761790
  have hstable : (prefixWord ++ tailWord_2761790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761790).length < 2 ^ (prefixWord ++ tailWord_2761790).sum := by decide
  have hdescent : baseEnd_2761790 < baseStart_2761790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761863 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 5, 5]
def baseStart_2761863 : Nat := 118140960795 + 2761863 * 2 ^ 59
def prefixEnd_2761863 : Nat := 4983230072969 + 3 ^ 40 * 2761863 * 2
def baseEnd_2761863 : Nat := 472721073622877644003643

theorem tailTrace_2761863 : CollatzResearch.WordTrace tailWord_2761863 prefixEnd_2761863 472721073622877644003643 := by
  unfold tailWord_2761863
  simp only [CollatzResearch.WordTrace]
  refine ⟨100733419193249514492458243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67155612795499676328305495 100733419193249514492458243)
  ·
    refine ⟨151100128789874271738687365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100733419193249514492458243 151100128789874271738687365)
    ·
      refine ⟨28331274148101425951003881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151100128789874271738687365 28331274148101425951003881)
      ·
        refine ⟨21248455611076069463252911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28331274148101425951003881 21248455611076069463252911)
        ·
          refine ⟨31872683416614104194879367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21248455611076069463252911 31872683416614104194879367)
          ·
            refine ⟨47809025124921156292319051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31872683416614104194879367 47809025124921156292319051)
            ·
              refine ⟨71713537687381734438478577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47809025124921156292319051 71713537687381734438478577)
              ·
                refine ⟨53785153265536300828858933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71713537687381734438478577 53785153265536300828858933)
                ·
                  refine ⟨5042358118644028202705525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53785153265536300828858933 5042358118644028202705525)
                  ·
                    refine ⟨472721073622877644003643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5042358118644028202705525 472721073622877644003643)
                    ·
                      rfl

theorem cell23_2761863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_2761863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761863 prefixEnd_2761863 := by exact prefixLift 2761863
  have htrace : WordTrace (prefixWord ++ tailWord_2761863) baseStart_2761863 baseEnd_2761863 := by
    simpa [prefixWord, tailWord_2761863, baseEnd_2761863] using wordTrace_append hprefix tailTrace_2761863
  have hstable : (prefixWord ++ tailWord_2761863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761863).length < 2 ^ (prefixWord ++ tailWord_2761863).sum := by decide
  have hdescent : baseEnd_2761863 < baseStart_2761863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761900 : List Nat := [2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 4]
def baseStart_2761900 : Nat := 118140960795 + 2761900 * 2 ^ 59
def prefixEnd_2761900 : Nat := 4983230072969 + 3 ^ 40 * 2761900 * 2
def baseEnd_2761900 : Nat := 1418182219652849287248259

theorem tailTrace_2761900 : CollatzResearch.WordTrace tailWord_2761900 prefixEnd_2761900 1418182219652849287248259 := by
  unfold tailWord_2761900
  simp only [CollatzResearch.WordTrace]
  refine ⟨50367384347057734905777577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67156512462743646541036769 50367384347057734905777577)
  ·
    refine ⟨37775538260293301179333183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50367384347057734905777577 37775538260293301179333183)
    ·
      refine ⟨56663307390439951768999775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37775538260293301179333183 56663307390439951768999775)
      ·
        refine ⟨84994961085659927653499663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56663307390439951768999775 84994961085659927653499663)
        ·
          refine ⟨127492441628489891480249495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84994961085659927653499663 127492441628489891480249495)
          ·
            refine ⟨191238662442734837220374243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127492441628489891480249495 191238662442734837220374243)
            ·
              refine ⟨286857993664102255830561365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191238662442734837220374243 286857993664102255830561365)
              ·
                refine ⟨3361617113251198310514391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 286857993664102255830561365 3361617113251198310514391)
                ·
                  refine ⟨5042425669876797465771587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3361617113251198310514391 5042425669876797465771587)
                  ·
                    refine ⟨7563638504815196198657381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5042425669876797465771587 7563638504815196198657381)
                    ·
                      refine ⟨1418182219652849287248259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7563638504815196198657381 1418182219652849287248259)
                      ·
                        rfl

theorem cell23_2761900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_2761900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761900 prefixEnd_2761900 := by exact prefixLift 2761900
  have htrace : WordTrace (prefixWord ++ tailWord_2761900) baseStart_2761900 baseEnd_2761900 := by
    simpa [prefixWord, tailWord_2761900, baseEnd_2761900] using wordTrace_append hprefix tailTrace_2761900
  have hstable : (prefixWord ++ tailWord_2761900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761900).length < 2 ^ (prefixWord ++ tailWord_2761900).sum := by decide
  have hdescent : baseEnd_2761900 < baseStart_2761900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761903 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 5]
def baseStart_2761903 : Nat := 118140960795 + 2761903 * 2 ^ 59
def prefixEnd_2761903 : Nat := 4983230072969 + 3 ^ 40 * 2761903 * 2
def baseEnd_2761903 : Nat := 1418183760094812775510745

theorem tailTrace_2761903 : CollatzResearch.WordTrace tailWord_2761903 prefixEnd_2761903 1418183760094812775510745 := by
  unfold tailWord_2761903
  simp only [CollatzResearch.WordTrace]
  refine ⟨100734878113104601323914363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67156585408736400882609575 100734878113104601323914363)
  ·
    refine ⟨151102317169656901985871545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100734878113104601323914363 151102317169656901985871545)
    ·
      refine ⟨113326737877242676489403659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151102317169656901985871545 113326737877242676489403659)
      ·
        refine ⟨169990106815864014734105489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113326737877242676489403659 169990106815864014734105489)
        ·
          refine ⟨127492580111898011050579117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169990106815864014734105489 127492580111898011050579117)
          ·
            refine ⟨47809717541961754143967169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127492580111898011050579117 47809717541961754143967169)
            ·
              refine ⟨35857288156471315607975377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47809717541961754143967169 35857288156471315607975377)
              ·
                refine ⟨26892966117353486705981533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35857288156471315607975377 26892966117353486705981533)
                ·
                  refine ⟨10084862294007557514743075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26892966117353486705981533 10084862294007557514743075)
                  ·
                    refine ⟨15127293441011336272114613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10084862294007557514743075 15127293441011336272114613)
                    ·
                      refine ⟨1418183760094812775510745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15127293441011336272114613 1418183760094812775510745)
                      ·
                        rfl

theorem cell23_2761903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_2761903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761903 prefixEnd_2761903 := by exact prefixLift 2761903
  have htrace : WordTrace (prefixWord ++ tailWord_2761903) baseStart_2761903 baseEnd_2761903 := by
    simpa [prefixWord, tailWord_2761903, baseEnd_2761903] using wordTrace_append hprefix tailTrace_2761903
  have hstable : (prefixWord ++ tailWord_2761903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761903).length < 2 ^ (prefixWord ++ tailWord_2761903).sum := by decide
  have hdescent : baseEnd_2761903 < baseStart_2761903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761922 : List Nat := [3, 5, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_2761922 : Nat := 118140960795 + 2761922 * 2 ^ 59
def prefixEnd_2761922 : Nat := 4983230072969 + 3 ^ 40 * 2761922 * 2
def baseEnd_2761922 : Nat := 472731172075749400391053

theorem tailTrace_2761922 : CollatzResearch.WordTrace tailWord_2761922 prefixEnd_2761922 472731172075749400391053 := by
  unfold tailWord_2761922
  simp only [CollatzResearch.WordTrace]
  refine ⟨25183892775008941892214005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67157047400023845045904013 25183892775008941892214005)
  ·
    refine ⟨2360989947657088302395063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25183892775008941892214005 2360989947657088302395063)
    ·
      refine ⟨3541484921485632453592595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2360989947657088302395063 3541484921485632453592595)
      ·
        refine ⟨5312227382228448680388893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3541484921485632453592595 5312227382228448680388893)
        ·
          refine ⟨1992085268335668255145835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5312227382228448680388893 1992085268335668255145835)
          ·
            refine ⟨2988127902503502382718753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1992085268335668255145835 2988127902503502382718753)
            ·
              refine ⟨2241095926877626787039065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2988127902503502382718753 2241095926877626787039065)
              ·
                refine ⟨1680821945158220090279299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2241095926877626787039065 1680821945158220090279299)
                ·
                  refine ⟨2521232917737330135418949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1680821945158220090279299 2521232917737330135418949)
                  ·
                    refine ⟨472731172075749400391053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2521232917737330135418949 472731172075749400391053)
                    ·
                      rfl

theorem cell23_2761922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_2761922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761922 prefixEnd_2761922 := by exact prefixLift 2761922
  have htrace : WordTrace (prefixWord ++ tailWord_2761922) baseStart_2761922 baseEnd_2761922 := by
    simpa [prefixWord, tailWord_2761922, baseEnd_2761922] using wordTrace_append hprefix tailTrace_2761922
  have hstable : (prefixWord ++ tailWord_2761922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761922).length < 2 ^ (prefixWord ++ tailWord_2761922).sum := by decide
  have hdescent : baseEnd_2761922 < baseStart_2761922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761943 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 6]
def baseStart_2761943 : Nat := 118140960795 + 2761943 * 2 ^ 59
def prefixEnd_2761943 : Nat := 4983230072969 + 3 ^ 40 * 2761943 * 2
def baseEnd_2761943 : Nat := 1418204299320992619010561

theorem tailTrace_2761943 : CollatzResearch.WordTrace tailWord_2761943 prefixEnd_2761943 1418204299320992619010561 := by
  unfold tailWord_2761943
  simp only [CollatzResearch.WordTrace]
  refine ⟨100736337032959688155370483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67157558021973125436913655 100736337032959688155370483)
  ·
    refine ⟨151104505549439532233055725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100736337032959688155370483 151104505549439532233055725)
    ·
      refine ⟨56664189581039824587395897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151104505549439532233055725 56664189581039824587395897)
      ·
        refine ⟨42498142185779868440546923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56664189581039824587395897 42498142185779868440546923)
        ·
          refine ⟨63747213278669802660820385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42498142185779868440546923 63747213278669802660820385)
          ·
            refine ⟨47810409959002351995615289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63747213278669802660820385 47810409959002351995615289)
            ·
              refine ⟨35857807469251763996711467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47810409959002351995615289 35857807469251763996711467)
              ·
                refine ⟨53786711203877645995067201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35857807469251763996711467 53786711203877645995067201)
                ·
                  refine ⟨40340033402908234496300401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53786711203877645995067201 40340033402908234496300401)
                  ·
                    refine ⟨30255025052181175872225301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40340033402908234496300401 30255025052181175872225301)
                    ·
                      refine ⟨1418204299320992619010561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30255025052181175872225301 1418204299320992619010561)
                      ·
                        rfl

theorem cell23_2761943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_2761943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761943 prefixEnd_2761943 := by exact prefixLift 2761943
  have htrace : WordTrace (prefixWord ++ tailWord_2761943) baseStart_2761943 baseEnd_2761943 := by
    simpa [prefixWord, tailWord_2761943, baseEnd_2761943] using wordTrace_append hprefix tailTrace_2761943
  have hstable : (prefixWord ++ tailWord_2761943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761943).length < 2 ^ (prefixWord ++ tailWord_2761943).sum := by decide
  have hdescent : baseEnd_2761943 < baseStart_2761943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761957 : List Nat := [1, 3, 1, 4, 3, 1, 3, 7]
def baseStart_2761957 : Nat := 118140960795 + 2761957 * 2 ^ 59
def prefixEnd_2761957 : Nat := 4983230072969 + 3 ^ 40 * 2761957 * 2
def baseEnd_2761957 : Nat := 52526351409265020897611

theorem tailTrace_2761957 : CollatzResearch.WordTrace tailWord_2761957 prefixEnd_2761957 52526351409265020897611 := by
  unfold tailWord_2761957
  simp only [CollatzResearch.WordTrace]
  refine ⟨100736847654908968546380125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67157898436605979030920083 100736847654908968546380125)
  ·
    refine ⟨37776317870590863204892547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100736847654908968546380125 37776317870590863204892547)
    ·
      refine ⟨56664476805886294807338821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37776317870590863204892547 56664476805886294807338821)
      ·
        refine ⟨10624589401103680276376029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56664476805886294807338821 10624589401103680276376029)
        ·
          refine ⟨3984221025413880103641011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10624589401103680276376029 3984221025413880103641011)
          ·
            refine ⟨5976331538120820155461517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3984221025413880103641011 5976331538120820155461517)
            ·
              refine ⟨2241124326795307558298069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5976331538120820155461517 2241124326795307558298069)
              ·
                refine ⟨52526351409265020897611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2241124326795307558298069 52526351409265020897611)
                ·
                  rfl

theorem cell23_2761957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 7].length) (baseStart_2761957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2761957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2761957 prefixEnd_2761957 := by exact prefixLift 2761957
  have htrace : WordTrace (prefixWord ++ tailWord_2761957) baseStart_2761957 baseEnd_2761957 := by
    simpa [prefixWord, tailWord_2761957, baseEnd_2761957] using wordTrace_append hprefix tailTrace_2761957
  have hstable : (prefixWord ++ tailWord_2761957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761957).length < 2 ^ (prefixWord ++ tailWord_2761957).sum := by decide
  have hdescent : baseEnd_2761957 < baseStart_2761957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762047 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 7]
def baseStart_2762047 : Nat := 118140960795 + 2762047 * 2 ^ 59
def prefixEnd_2762047 : Nat := 4983230072969 + 3 ^ 40 * 2762047 * 2
def baseEnd_2762047 : Nat := 157584189034340023567787

theorem tailTrace_2762047 : CollatzResearch.WordTrace tailWord_2762047 prefixEnd_2762047 157584189034340023567787 := by
  unfold tailWord_2762047
  simp only [CollatzResearch.WordTrace]
  refine ⟨100740130224582913917156395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67160086816388609278104263 100740130224582913917156395)
  ·
    refine ⟨151110195336874370875734593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100740130224582913917156395 151110195336874370875734593)
    ·
      refine ⟨113332646502655778156800945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151110195336874370875734593 113332646502655778156800945)
      ·
        refine ⟨84999484876991833617600709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113332646502655778156800945 84999484876991833617600709)
        ·
          refine ⟨15937403414435968803300133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84999484876991833617600709 15937403414435968803300133)
          ·
            refine ⟨2988263140206744150618775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15937403414435968803300133 2988263140206744150618775)
            ·
              refine ⟨4482394710310116225928163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2988263140206744150618775 4482394710310116225928163)
              ·
                refine ⟨6723592065465174338892245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4482394710310116225928163 6723592065465174338892245)
                ·
                  refine ⟨157584189034340023567787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6723592065465174338892245 157584189034340023567787)
                  ·
                    rfl

theorem cell23_2762047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 7].length) (baseStart_2762047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762047 prefixEnd_2762047 := by exact prefixLift 2762047
  have htrace : WordTrace (prefixWord ++ tailWord_2762047) baseStart_2762047 baseEnd_2762047 := by
    simpa [prefixWord, tailWord_2762047, baseEnd_2762047] using wordTrace_append hprefix tailTrace_2762047
  have hstable : (prefixWord ++ tailWord_2762047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762047).length < 2 ^ (prefixWord ++ tailWord_2762047).sum := by decide
  have hdescent : baseEnd_2762047 < baseStart_2762047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762097 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 2, 1, 4]
def baseStart_2762097 : Nat := 118140960795 + 2762097 * 2 ^ 59
def prefixEnd_2762097 : Nat := 4983230072969 + 3 ^ 40 * 2762097 * 2
def baseEnd_2762097 : Nat := 1418283375341785016484853

theorem tailTrace_2762097 : CollatzResearch.WordTrace tailWord_2762097 prefixEnd_2762097 1418283375341785016484853 := by
  unfold tailWord_2762097
  simp only [CollatzResearch.WordTrace]
  refine ⟨100741953874401772456476545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67161302582934514970984363 100741953874401772456476545)
  ·
    refine ⟨75556465405801329342357409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100741953874401772456476545 75556465405801329342357409)
    ·
      refine ⟨56667349054350997006768057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75556465405801329342357409 56667349054350997006768057)
      ·
        refine ⟨42500511790763247755076043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56667349054350997006768057 42500511790763247755076043)
        ·
          refine ⟨63750767686144871632614065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42500511790763247755076043 63750767686144871632614065)
          ·
            refine ⟨47813075764608653724460549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63750767686144871632614065 47813075764608653724460549)
            ·
              refine ⟨8964951705864122573336353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47813075764608653724460549 8964951705864122573336353)
              ·
                refine ⟨6723713779398091930002265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8964951705864122573336353 6723713779398091930002265)
                ·
                  refine ⟨5042785334548568947501699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6723713779398091930002265 5042785334548568947501699)
                  ·
                    refine ⟨7564178001822853421252549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5042785334548568947501699 7564178001822853421252549)
                    ·
                      refine ⟨1418283375341785016484853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7564178001822853421252549 1418283375341785016484853)
                      ·
                        rfl

theorem cell23_2762097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_2762097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762097 prefixEnd_2762097 := by exact prefixLift 2762097
  have htrace : WordTrace (prefixWord ++ tailWord_2762097) baseStart_2762097 baseEnd_2762097 := by
    simpa [prefixWord, tailWord_2762097, baseEnd_2762097] using wordTrace_append hprefix tailTrace_2762097
  have hstable : (prefixWord ++ tailWord_2762097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762097).length < 2 ^ (prefixWord ++ tailWord_2762097).sum := by decide
  have hdescent : baseEnd_2762097 < baseStart_2762097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762107 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 3, 4]
def baseStart_2762107 : Nat := 118140960795 + 2762107 * 2 ^ 59
def prefixEnd_2762107 : Nat := 4983230072969 + 3 ^ 40 * 2762107 * 2
def baseEnd_2762107 : Nat := 472762836716109992453269

theorem tailTrace_2762107 : CollatzResearch.WordTrace tailWord_2762107 prefixEnd_2762107 472762836716109992453269 := by
  unfold tailWord_2762107
  simp only [CollatzResearch.WordTrace]
  refine ⟨100742318604365544164340575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67161545736243696109560383 100742318604365544164340575)
  ·
    refine ⟨151113477906548316246510863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100742318604365544164340575 151113477906548316246510863)
    ·
      refine ⟨226670216859822474369766295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151113477906548316246510863 226670216859822474369766295)
      ·
        refine ⟨340005325289733711554649443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226670216859822474369766295 340005325289733711554649443)
        ·
          refine ⟨510007987934600567331974165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340005325289733711554649443 510007987934600567331974165)
          ·
            refine ⟨23906624434434401593686289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 510007987934600567331974165 23906624434434401593686289)
            ·
              refine ⟨17929968325825801195264717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23906624434434401593686289 17929968325825801195264717)
              ·
                refine ⟨6723738122184675448224269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17929968325825801195264717 6723738122184675448224269)
                ·
                  refine ⟨2521401795819253293084101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6723738122184675448224269 2521401795819253293084101)
                  ·
                    refine ⟨472762836716109992453269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2521401795819253293084101 472762836716109992453269)
                    ·
                      rfl

theorem cell23_2762107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 4].length) (baseStart_2762107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762107 prefixEnd_2762107 := by exact prefixLift 2762107
  have htrace : WordTrace (prefixWord ++ tailWord_2762107) baseStart_2762107 baseEnd_2762107 := by
    simpa [prefixWord, tailWord_2762107, baseEnd_2762107] using wordTrace_append hprefix tailTrace_2762107
  have hstable : (prefixWord ++ tailWord_2762107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762107).length < 2 ^ (prefixWord ++ tailWord_2762107).sum := by decide
  have hdescent : baseEnd_2762107 < baseStart_2762107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762117 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 4, 2, 3]
def baseStart_2762117 : Nat := 118140960795 + 2762117 * 2 ^ 59
def prefixEnd_2762117 : Nat := 4983230072969 + 3 ^ 40 * 2762117 * 2
def baseEnd_2762117 : Nat := 1418293644954874938234761

theorem tailTrace_2762117 : CollatzResearch.WordTrace tailWord_2762117 prefixEnd_2762117 1418293644954874938234761 := by
  unfold tailWord_2762117
  simp only [CollatzResearch.WordTrace]
  refine ⟨100742683334329315872204605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67161788889552877248136403 100742683334329315872204605)
  ·
    refine ⟨37778506250373493452076727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100742683334329315872204605 37778506250373493452076727)
    ·
      refine ⟨56667759375560240178115091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37778506250373493452076727 56667759375560240178115091)
      ·
        refine ⟨85001639063340360267172637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56667759375560240178115091 85001639063340360267172637)
        ·
          refine ⟨31875614648752635100189739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85001639063340360267172637 31875614648752635100189739)
          ·
            refine ⟨47813421973128952650284609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31875614648752635100189739 47813421973128952650284609)
            ·
              refine ⟨35860066479846714487713457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47813421973128952650284609 35860066479846714487713457)
              ·
                refine ⟨26895049859885035865785093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35860066479846714487713457 26895049859885035865785093)
                ·
                  refine ⟨5042821848728444224834705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26895049859885035865785093 5042821848728444224834705)
                  ·
                    refine ⟨3782116386546333168626029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5042821848728444224834705 3782116386546333168626029)
                    ·
                      refine ⟨1418293644954874938234761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3782116386546333168626029 1418293644954874938234761)
                      ·
                        rfl

theorem cell23_2762117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_2762117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762117 prefixEnd_2762117 := by exact prefixLift 2762117
  have htrace : WordTrace (prefixWord ++ tailWord_2762117) baseStart_2762117 baseEnd_2762117 := by
    simpa [prefixWord, tailWord_2762117, baseEnd_2762117] using wordTrace_append hprefix tailTrace_2762117
  have hstable : (prefixWord ++ tailWord_2762117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762117).length < 2 ^ (prefixWord ++ tailWord_2762117).sum := by decide
  have hdescent : baseEnd_2762117 < baseStart_2762117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762141 : List Nat := [1, 4, 2, 1, 3, 1, 1, 5, 1, 4]
def baseStart_2762141 : Nat := 118140960795 + 2762141 * 2 ^ 59
def prefixEnd_2762141 : Nat := 4983230072969 + 3 ^ 40 * 2762141 * 2
def baseEnd_2762141 : Nat := 472768656163527614778217

theorem tailTrace_2762141 : CollatzResearch.WordTrace tailWord_2762141 prefixEnd_2762141 472768656163527614778217 := by
  unfold tailWord_2762141
  simp only [CollatzResearch.WordTrace]
  refine ⟨100743558686242367971078277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67162372457494911980718851 100743558686242367971078277)
  ·
    refine ⟨18889417253670443994577177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100743558686242367971078277 18889417253670443994577177)
    ·
      refine ⟨14167062940252832995932883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18889417253670443994577177 14167062940252832995932883)
      ·
        refine ⟨21250594410379249493899325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14167062940252832995932883 21250594410379249493899325)
        ·
          refine ⟨7968972903892218560212247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21250594410379249493899325 7968972903892218560212247)
          ·
            refine ⟨11953459355838327840318371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7968972903892218560212247 11953459355838327840318371)
            ·
              refine ⟨17930189033757491760477557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11953459355838327840318371 17930189033757491760477557)
              ·
                refine ⟨1680955221914764852544771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17930189033757491760477557 1680955221914764852544771)
                ·
                  refine ⟨2521432832872147278817157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1680955221914764852544771 2521432832872147278817157)
                  ·
                    refine ⟨472768656163527614778217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2521432832872147278817157 472768656163527614778217)
                    ·
                      rfl

theorem cell23_2762141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_2762141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762141 prefixEnd_2762141 := by exact prefixLift 2762141
  have htrace : WordTrace (prefixWord ++ tailWord_2762141) baseStart_2762141 baseEnd_2762141 := by
    simpa [prefixWord, tailWord_2762141, baseEnd_2762141] using wordTrace_append hprefix tailTrace_2762141
  have hstable : (prefixWord ++ tailWord_2762141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762141).length < 2 ^ (prefixWord ++ tailWord_2762141).sum := by decide
  have hdescent : baseEnd_2762141 < baseStart_2762141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762160 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 7]
def baseStart_2762160 : Nat := 118140960795 + 2762160 * 2 ^ 59
def prefixEnd_2762160 : Nat := 4983230072969 + 3 ^ 40 * 2762160 * 2
def baseEnd_2762160 : Nat := 1418315724623018269997063

theorem tailTrace_2762160 : CollatzResearch.WordTrace tailWord_2762160 prefixEnd_2762160 1418315724623018269997063 := by
  unfold tailWord_2762160
  simp only [CollatzResearch.WordTrace]
  refine ⟨50372125836586767108009967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67162834448782356144013289 50372125836586767108009967)
  ·
    refine ⟨75558188754880150662014951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50372125836586767108009967 75558188754880150662014951)
    ·
      refine ⟨113337283132320225993022427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75558188754880150662014951 113337283132320225993022427)
      ·
        refine ⟨170005924698480338989533641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113337283132320225993022427 170005924698480338989533641)
        ·
          refine ⟨127504443523860254242150231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170005924698480338989533641 127504443523860254242150231)
          ·
            refine ⟨191256665285790381363225347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127504443523860254242150231 191256665285790381363225347)
            ·
              refine ⟨286884997928685572044838021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191256665285790381363225347 286884997928685572044838021)
              ·
                refine ⟨53790937111628544758407129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 286884997928685572044838021 53790937111628544758407129)
                ·
                  refine ⟨40343202833721408568805347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53790937111628544758407129 40343202833721408568805347)
                  ·
                    refine ⟨60514804250582112853208021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40343202833721408568805347 60514804250582112853208021)
                    ·
                      refine ⟨1418315724623018269997063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60514804250582112853208021 1418315724623018269997063)
                      ·
                        rfl

theorem cell23_2762160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_2762160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762160 prefixEnd_2762160 := by exact prefixLift 2762160
  have htrace : WordTrace (prefixWord ++ tailWord_2762160) baseStart_2762160 baseEnd_2762160 := by
    simpa [prefixWord, tailWord_2762160, baseEnd_2762160] using wordTrace_append hprefix tailTrace_2762160
  have hstable : (prefixWord ++ tailWord_2762160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762160).length < 2 ^ (prefixWord ++ tailWord_2762160).sum := by decide
  have hdescent : baseEnd_2762160 < baseStart_2762160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762184 : List Nat := [2, 1, 3, 1, 3, 1, 4, 2, 1, 5]
def baseStart_2762184 : Nat := 118140960795 + 2762184 * 2 ^ 59
def prefixEnd_2762184 : Nat := 4983230072969 + 3 ^ 40 * 2762184 * 2
def baseEnd_2762184 : Nat := 472776016052908725365651

theorem tailTrace_2762184 : CollatzResearch.WordTrace tailWord_2762184 prefixEnd_2762184 472776016052908725365651 := by
  unfold tailWord_2762184
  simp only [CollatzResearch.WordTrace]
  refine ⟨50372563512543293157446803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67163418016724390876595737 50372563512543293157446803)
  ·
    refine ⟨75558845268814939736170205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50372563512543293157446803 75558845268814939736170205)
    ·
      refine ⟨28334566975805602401063827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75558845268814939736170205 28334566975805602401063827)
      ·
        refine ⟨42501850463708403601595741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28334566975805602401063827 42501850463708403601595741)
        ·
          refine ⟨15938193923890651350598403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42501850463708403601595741 15938193923890651350598403)
          ·
            refine ⟨23907290885835977025897605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15938193923890651350598403 23907290885835977025897605)
            ·
              refine ⟨4482617041094245692355801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23907290885835977025897605 4482617041094245692355801)
              ·
                refine ⟨3361962780820684269266851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4482617041094245692355801 3361962780820684269266851)
                ·
                  refine ⟨5042944171231026403900277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3361962780820684269266851 5042944171231026403900277)
                  ·
                    refine ⟨472776016052908725365651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5042944171231026403900277 472776016052908725365651)
                    ·
                      rfl

theorem cell23_2762184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_2762184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762184 prefixEnd_2762184 := by exact prefixLift 2762184
  have htrace : WordTrace (prefixWord ++ tailWord_2762184) baseStart_2762184 baseEnd_2762184 := by
    simpa [prefixWord, tailWord_2762184, baseEnd_2762184] using wordTrace_append hprefix tailTrace_2762184
  have hstable : (prefixWord ++ tailWord_2762184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762184).length < 2 ^ (prefixWord ++ tailWord_2762184).sum := by decide
  have hdescent : baseEnd_2762184 < baseStart_2762184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762187 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 4]
def baseStart_2762187 : Nat := 118140960795 + 2762187 * 2 ^ 59
def prefixEnd_2762187 : Nat := 4983230072969 + 3 ^ 40 * 2762187 * 2
def baseEnd_2762187 : Nat := 1418329588600689664359439

theorem tailTrace_2762187 : CollatzResearch.WordTrace tailWord_2762187 prefixEnd_2762187 1418329588600689664359439 := by
  unfold tailWord_2762187
  simp only [CollatzResearch.WordTrace]
  refine ⟨100745236444075717827252815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67163490962717145218168543 100745236444075717827252815)
  ·
    refine ⟨151117854666113576740879223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100745236444075717827252815 151117854666113576740879223)
    ·
      refine ⟨226676781999170365111318835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151117854666113576740879223 226676781999170365111318835)
      ·
        refine ⟨340015172998755547666978253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226676781999170365111318835 340015172998755547666978253)
        ·
          refine ⟨127505689874533330375116845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340015172998755547666978253 127505689874533330375116845)
          ·
            refine ⟨47814633702949998890668817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127505689874533330375116845 47814633702949998890668817)
            ·
              refine ⟨35860975277212499168001613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47814633702949998890668817 35860975277212499168001613)
              ·
                refine ⟨13447865728954687188000605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35860975277212499168001613 13447865728954687188000605)
                ·
                  refine ⟨5042949648358007695500227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13447865728954687188000605 5042949648358007695500227)
                  ·
                    refine ⟨7564424472537011543250341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5042949648358007695500227 7564424472537011543250341)
                    ·
                      refine ⟨1418329588600689664359439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7564424472537011543250341 1418329588600689664359439)
                      ·
                        rfl

theorem cell23_2762187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 4].length) (baseStart_2762187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762187 prefixEnd_2762187 := by exact prefixLift 2762187
  have htrace : WordTrace (prefixWord ++ tailWord_2762187) baseStart_2762187 baseEnd_2762187 := by
    simpa [prefixWord, tailWord_2762187, baseEnd_2762187] using wordTrace_append hprefix tailTrace_2762187
  have hstable : (prefixWord ++ tailWord_2762187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762187).length < 2 ^ (prefixWord ++ tailWord_2762187).sum := by decide
  have hdescent : baseEnd_2762187 < baseStart_2762187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762197 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 3, 6]
def baseStart_2762197 : Nat := 118140960795 + 2762197 * 2 ^ 59
def prefixEnd_2762197 : Nat := 4983230072969 + 3 ^ 40 * 2762197 * 2
def baseEnd_2762197 : Nat := 472778241135744875078131

theorem tailTrace_2762197 : CollatzResearch.WordTrace tailWord_2762197 prefixEnd_2762197 472778241135744875078131 := by
  unfold tailWord_2762197
  simp only [CollatzResearch.WordTrace]
  refine ⟨100745601174039489535116845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67163734116026326356744563 100745601174039489535116845)
  ·
    refine ⟨37779600440264808575668817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100745601174039489535116845 37779600440264808575668817)
    ·
      refine ⟨28334700330198606431751613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37779600440264808575668817 28334700330198606431751613)
      ·
        refine ⟨10625512623824477411906855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28334700330198606431751613 10625512623824477411906855)
        ·
          refine ⟨15938268935736716117860283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10625512623824477411906855 15938268935736716117860283)
          ·
            refine ⟨23907403403605074176790425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15938268935736716117860283 23907403403605074176790425)
            ·
              refine ⟨17930552552703805632592819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23907403403605074176790425 17930552552703805632592819)
              ·
                refine ⟨26895828829055708448889229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17930552552703805632592819 26895828829055708448889229)
                ·
                  refine ⟨10085935810895890668333461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26895828829055708448889229 10085935810895890668333461)
                  ·
                    refine ⟨472778241135744875078131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10085935810895890668333461 472778241135744875078131)
                    ·
                      rfl

theorem cell23_2762197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_2762197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762197 prefixEnd_2762197 := by exact prefixLift 2762197
  have htrace : WordTrace (prefixWord ++ tailWord_2762197) baseStart_2762197 baseEnd_2762197 := by
    simpa [prefixWord, tailWord_2762197, baseEnd_2762197] using wordTrace_append hprefix tailTrace_2762197
  have hstable : (prefixWord ++ tailWord_2762197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762197).length < 2 ^ (prefixWord ++ tailWord_2762197).sum := by decide
  have hdescent : baseEnd_2762197 < baseStart_2762197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762215 : List Nat := [1, 1, 5, 2, 1, 3, 3, 2, 1, 1, 3]
def baseStart_2762215 : Nat := 118140960795 + 2762215 * 2 ^ 59
def prefixEnd_2762215 : Nat := 4983230072969 + 3 ^ 40 * 2762215 * 2
def baseEnd_2762215 : Nat := 1418343966059015554809311

theorem tailTrace_2762215 : CollatzResearch.WordTrace tailWord_2762215 prefixEnd_2762215 1418343966059015554809311 := by
  unfold tailWord_2762215
  simp only [CollatzResearch.WordTrace]
  refine ⟨100746257687974278609272099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67164171791982852406181399 100746257687974278609272099)
  ·
    refine ⟨151119386531961417913908149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100746257687974278609272099 151119386531961417913908149)
    ·
      refine ⟨14167442487371382929428889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151119386531961417913908149 14167442487371382929428889)
      ·
        refine ⟨10625581865528537197071667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14167442487371382929428889 10625581865528537197071667)
        ·
          refine ⟨15938372798292805795607501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10625581865528537197071667 15938372798292805795607501)
          ·
            refine ⟨5976889799359802173352813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15938372798292805795607501 5976889799359802173352813)
            ·
              refine ⟨2241333674759925815007305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5976889799359802173352813 2241333674759925815007305)
              ·
                refine ⟨1681000256069944361255479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2241333674759925815007305 1681000256069944361255479)
                ·
                  refine ⟨2521500384104916541883219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681000256069944361255479 2521500384104916541883219)
                  ·
                    refine ⟨3782250576157374812824829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2521500384104916541883219 3782250576157374812824829)
                    ·
                      refine ⟨1418343966059015554809311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3782250576157374812824829 1418343966059015554809311)
                      ·
                        rfl

theorem cell23_2762215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_2762215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762215 prefixEnd_2762215 := by exact prefixLift 2762215
  have htrace : WordTrace (prefixWord ++ tailWord_2762215) baseStart_2762215 baseEnd_2762215 := by
    simpa [prefixWord, tailWord_2762215, baseEnd_2762215] using wordTrace_append hprefix tailTrace_2762215
  have hstable : (prefixWord ++ tailWord_2762215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762215).length < 2 ^ (prefixWord ++ tailWord_2762215).sum := by decide
  have hdescent : baseEnd_2762215 < baseStart_2762215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762238 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2762238 : Nat := 118140960795 + 2762238 * 2 ^ 59
def prefixEnd_2762238 : Nat := 4983230072969 + 3 ^ 40 * 2762238 * 2
def baseEnd_2762238 : Nat := 1418355776114068964821705

theorem tailTrace_2762238 : CollatzResearch.WordTrace tailWord_2762238 prefixEnd_2762238 1418355776114068964821705 := by
  unfold tailWord_2762238
  simp only [CollatzResearch.WordTrace]
  refine ⟨12593387070861369192169921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67164731044593969024906245 12593387070861369192169921)
  ·
    refine ⟨9445040303146026894127441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12593387070861369192169921 9445040303146026894127441)
    ·
      refine ⟨7083780227359520170595581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9445040303146026894127441 7083780227359520170595581)
      ·
        refine ⟨2656417585259820063973343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7083780227359520170595581 2656417585259820063973343)
        ·
          refine ⟨3984626377889730095960015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2656417585259820063973343 3984626377889730095960015)
          ·
            refine ⟨5976939566834595143940023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3984626377889730095960015 5976939566834595143940023)
            ·
              refine ⟨8965409350251892715910035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5976939566834595143940023 8965409350251892715910035)
              ·
                refine ⟨13448114025377839073865053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8965409350251892715910035 13448114025377839073865053)
                ·
                  refine ⟨5043042759516689652699395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13448114025377839073865053 5043042759516689652699395)
                  ·
                    refine ⟨7564564139275034479049093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5043042759516689652699395 7564564139275034479049093)
                    ·
                      refine ⟨1418355776114068964821705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7564564139275034479049093 1418355776114068964821705)
                      ·
                        rfl

theorem cell23_2762238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2762238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762238 prefixEnd_2762238 := by exact prefixLift 2762238
  have htrace : WordTrace (prefixWord ++ tailWord_2762238) baseStart_2762238 baseEnd_2762238 := by
    simpa [prefixWord, tailWord_2762238, baseEnd_2762238] using wordTrace_append hprefix tailTrace_2762238
  have hstable : (prefixWord ++ tailWord_2762238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762238).length < 2 ^ (prefixWord ++ tailWord_2762238).sum := by decide
  have hdescent : baseEnd_2762238 < baseStart_2762238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762241 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_2762241 : Nat := 118140960795 + 2762241 * 2 ^ 59
def prefixEnd_2762241 : Nat := 4983230072969 + 3 ^ 40 * 2762241 * 2
def baseEnd_2762241 : Nat := 1418357316556032453084191

theorem tailTrace_2762241 : CollatzResearch.WordTrace tailWord_2762241 prefixEnd_2762241 1418357316556032453084191 := by
  unfold tailWord_2762241
  simp only [CollatzResearch.WordTrace]
  refine ⟨100747205985880085049718577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67164803990586723366479051 100747205985880085049718577)
  ·
    refine ⟨75560404489410063787288933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100747205985880085049718577 75560404489410063787288933)
    ·
      refine ⟨14167575841764386960116675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75560404489410063787288933 14167575841764386960116675)
      ·
        refine ⟨21251363762646580440175013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14167575841764386960116675 21251363762646580440175013)
        ·
          refine ⟨3984630705496233832532815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21251363762646580440175013 3984630705496233832532815)
          ·
            refine ⟨5976946058244350748799223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3984630705496233832532815 5976946058244350748799223)
            ·
              refine ⟨8965419087366526123198835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5976946058244350748799223 8965419087366526123198835)
              ·
                refine ⟨13448128631049789184798253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8965419087366526123198835 13448128631049789184798253)
                ·
                  refine ⟨5043048236643670944299345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13448128631049789184798253 5043048236643670944299345)
                  ·
                    refine ⟨3782286177482753208224509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5043048236643670944299345 3782286177482753208224509)
                    ·
                      refine ⟨1418357316556032453084191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3782286177482753208224509 1418357316556032453084191)
                      ·
                        rfl

theorem cell23_2762241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_2762241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762241 prefixEnd_2762241 := by exact prefixLift 2762241
  have htrace : WordTrace (prefixWord ++ tailWord_2762241) baseStart_2762241 baseEnd_2762241 := by
    simpa [prefixWord, tailWord_2762241, baseEnd_2762241] using wordTrace_append hprefix tailTrace_2762241
  have hstable : (prefixWord ++ tailWord_2762241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762241).length < 2 ^ (prefixWord ++ tailWord_2762241).sum := by decide
  have hdescent : baseEnd_2762241 < baseStart_2762241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762271 : List Nat := [1, 1, 2, 4, 1, 1, 3, 4, 2, 1, 3]
def baseStart_2762271 : Nat := 118140960795 + 2762271 * 2 ^ 59
def prefixEnd_2762271 : Nat := 4983230072969 + 3 ^ 40 * 2762271 * 2
def baseEnd_2762271 : Nat := 1418372720975667335709053

theorem tailTrace_2762271 : CollatzResearch.WordTrace tailWord_2762271 prefixEnd_2762271 1418372720975667335709053 := by
  unfold tailWord_2762271
  simp only [CollatzResearch.WordTrace]
  refine ⟨100748300175771400173310667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67165533450514266782207111 100748300175771400173310667)
  ·
    refine ⟨151122450263657100259966001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100748300175771400173310667 151122450263657100259966001)
    ·
      refine ⟨113341837697742825194974501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151122450263657100259966001 113341837697742825194974501)
      ·
        refine ⟨21251594568326779724057719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113341837697742825194974501 21251594568326779724057719)
        ·
          refine ⟨31877391852490169586086579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21251594568326779724057719 31877391852490169586086579)
          ·
            refine ⟨47816087778735254379129869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31877391852490169586086579 47816087778735254379129869)
            ·
              refine ⟨17931032917025720392173701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47816087778735254379129869 17931032917025720392173701)
              ·
                refine ⟨3362068671942322573532569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17931032917025720392173701 3362068671942322573532569)
                ·
                  refine ⟨2521551503956741930149427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3362068671942322573532569 2521551503956741930149427)
                  ·
                    refine ⟨3782327255935112895224141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2521551503956741930149427 3782327255935112895224141)
                    ·
                      refine ⟨1418372720975667335709053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3782327255935112895224141 1418372720975667335709053)
                      ·
                        rfl

theorem cell23_2762271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_2762271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762271 prefixEnd_2762271 := by exact prefixLift 2762271
  have htrace : WordTrace (prefixWord ++ tailWord_2762271) baseStart_2762271 baseEnd_2762271 := by
    simpa [prefixWord, tailWord_2762271, baseEnd_2762271] using wordTrace_append hprefix tailTrace_2762271
  have hstable : (prefixWord ++ tailWord_2762271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762271).length < 2 ^ (prefixWord ++ tailWord_2762271).sum := by decide
  have hdescent : baseEnd_2762271 < baseStart_2762271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762272 : List Nat := [2, 1, 1, 6, 1, 1, 4, 2, 1, 2, 2]
def baseStart_2762272 : Nat := 118140960795 + 2762272 * 2 ^ 59
def prefixEnd_2762272 : Nat := 4983230072969 + 3 ^ 40 * 2762272 * 2
def baseEnd_2762272 : Nat := 1418373234456321831796549

theorem tailTrace_2762272 : CollatzResearch.WordTrace tailWord_2762272 prefixEnd_2762272 1418373234456321831796549 := by
  unfold tailWord_2762272
  simp only [CollatzResearch.WordTrace]
  refine ⟨50374168324383888672048535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67165557765845184896064713 50374168324383888672048535)
  ·
    refine ⟨75561252486575833008072803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50374168324383888672048535 75561252486575833008072803)
    ·
      refine ⟨113341878729863749512109205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75561252486575833008072803 113341878729863749512109205)
      ·
        refine ⟨5312900565462363258380119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 113341878729863749512109205 5312900565462363258380119)
        ·
          refine ⟨7969350848193544887570179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5312900565462363258380119 7969350848193544887570179)
          ·
            refine ⟨11954026272290317331355269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7969350848193544887570179 11954026272290317331355269)
            ·
              refine ⟨2241379926054434499629113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11954026272290317331355269 2241379926054434499629113)
              ·
                refine ⟨1681034944540825874721835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2241379926054434499629113 1681034944540825874721835)
                ·
                  refine ⟨2521552416811238812082753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681034944540825874721835 2521552416811238812082753)
                  ·
                    refine ⟨1891164312608429109062065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2521552416811238812082753 1891164312608429109062065)
                    ·
                      refine ⟨1418373234456321831796549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1891164312608429109062065 1418373234456321831796549)
                      ·
                        rfl

theorem cell23_2762272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_2762272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762272 prefixEnd_2762272 := by exact prefixLift 2762272
  have htrace : WordTrace (prefixWord ++ tailWord_2762272) baseStart_2762272 baseEnd_2762272 := by
    simpa [prefixWord, tailWord_2762272, baseEnd_2762272] using wordTrace_append hprefix tailTrace_2762272
  have hstable : (prefixWord ++ tailWord_2762272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762272).length < 2 ^ (prefixWord ++ tailWord_2762272).sum := by decide
  have hdescent : baseEnd_2762272 < baseStart_2762272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762324 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_2762324 : Nat := 118140960795 + 2762324 * 2 ^ 59
def prefixEnd_2762324 : Nat := 4983230072969 + 3 ^ 40 * 2762324 * 2
def baseEnd_2762324 : Nat := 1418399935450355628346309

theorem tailTrace_2762324 : CollatzResearch.WordTrace tailWord_2762324 prefixEnd_2762324 1418399935450355628346309 := by
  unfold tailWord_2762324
  simp only [CollatzResearch.WordTrace]
  refine ⟨50375116622289695112495013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67166822163052926816660017 50375116622289695112495013)
  ·
    refine ⟨9445334366679317833592815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50375116622289695112495013 9445334366679317833592815)
    ·
      refine ⟨14168001550018976750389223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9445334366679317833592815 14168001550018976750389223)
      ·
        refine ⟨21252002325028465125583835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14168001550018976750389223 21252002325028465125583835)
        ·
          refine ⟨31878003487542697688375753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21252002325028465125583835 31878003487542697688375753)
          ·
            refine ⟨23908502615657023266281815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31878003487542697688375753 23908502615657023266281815)
            ·
              refine ⟨35862753923485534899422723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23908502615657023266281815 35862753923485534899422723)
              ·
                refine ⟨53794130885228302349134085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35862753923485534899422723 53794130885228302349134085)
                ·
                  refine ⟨10086399540980306690462641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53794130885228302349134085 10086399540980306690462641)
                  ·
                    refine ⟨7564799655735230017846981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10086399540980306690462641 7564799655735230017846981)
                    ·
                      refine ⟨1418399935450355628346309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7564799655735230017846981 1418399935450355628346309)
                      ·
                        rfl

theorem cell23_2762324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_2762324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762324 prefixEnd_2762324 := by exact prefixLift 2762324
  have htrace : WordTrace (prefixWord ++ tailWord_2762324) baseStart_2762324 baseEnd_2762324 := by
    simpa [prefixWord, tailWord_2762324, baseEnd_2762324] using wordTrace_append hprefix tailTrace_2762324
  have hstable : (prefixWord ++ tailWord_2762324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762324).length < 2 ^ (prefixWord ++ tailWord_2762324).sum := by decide
  have hdescent : baseEnd_2762324 < baseStart_2762324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762364 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 2, 5]
def baseStart_2762364 : Nat := 118140960795 + 2762364 * 2 ^ 59
def prefixEnd_2762364 : Nat := 4983230072969 + 3 ^ 40 * 2762364 * 2
def baseEnd_2762364 : Nat := 472806824892178490615375

theorem tailTrace_2762364 : CollatzResearch.WordTrace tailWord_2762364 prefixEnd_2762364 472806824892178490615375 := by
  unfold tailWord_2762364
  simp only [CollatzResearch.WordTrace]
  refine ⟨50375846082217238528223073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67167794776289651370964097 50375846082217238528223073)
  ·
    refine ⟨37781884561662928896167305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50375846082217238528223073 37781884561662928896167305)
    ·
      refine ⟨28336413421247196672125479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37781884561662928896167305 28336413421247196672125479)
      ·
        refine ⟨42504620131870795008188219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28336413421247196672125479 42504620131870795008188219)
        ·
          refine ⟨63756930197806192512282329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42504620131870795008188219 63756930197806192512282329)
          ·
            refine ⟨47817697648354644384211747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63756930197806192512282329 47817697648354644384211747)
            ·
              refine ⟨71726546472531966576317621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47817697648354644384211747 71726546472531966576317621)
              ·
                refine ⟨6724363731799871866529777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71726546472531966576317621 6724363731799871866529777)
                ·
                  refine ⟨5043272798849903899897333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6724363731799871866529777 5043272798849903899897333)
                  ·
                    refine ⟨472806824892178490615375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5043272798849903899897333 472806824892178490615375)
                    ·
                      rfl

theorem cell23_2762364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_2762364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762364 prefixEnd_2762364 := by exact prefixLift 2762364
  have htrace : WordTrace (prefixWord ++ tailWord_2762364) baseStart_2762364 baseEnd_2762364 := by
    simpa [prefixWord, tailWord_2762364, baseEnd_2762364] using wordTrace_append hprefix tailTrace_2762364
  have hstable : (prefixWord ++ tailWord_2762364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762364).length < 2 ^ (prefixWord ++ tailWord_2762364).sum := by decide
  have hdescent : baseEnd_2762364 < baseStart_2762364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762367 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 8]
def baseStart_2762367 : Nat := 118140960795 + 2762367 * 2 ^ 59
def prefixEnd_2762367 : Nat := 4983230072969 + 3 ^ 40 * 2762367 * 2
def baseEnd_2762367 : Nat := 1418422015118498960108611

theorem tailTrace_2762367 : CollatzResearch.WordTrace tailWord_2762367 prefixEnd_2762367 1418422015118498960108611 := by
  unfold tailWord_2762367
  simp only [CollatzResearch.WordTrace]
  refine ⟨100751801583423608568805355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67167867722282405712536903 100751801583423608568805355)
  ·
    refine ⟨151127702375135412853208033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100751801583423608568805355 151127702375135412853208033)
    ·
      refine ⟨113345776781351559639906025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151127702375135412853208033 113345776781351559639906025)
      ·
        refine ⟨85009332586013669729929519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113345776781351559639906025 85009332586013669729929519)
        ·
          refine ⟨127513998879020504594894279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85009332586013669729929519 127513998879020504594894279)
          ·
            refine ⟨191270998318530756892341419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127513998879020504594894279 191270998318530756892341419)
            ·
              refine ⟨286906497477796135338512129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191270998318530756892341419 286906497477796135338512129)
              ·
                refine ⟨215179873108347101503884097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286906497477796135338512129 215179873108347101503884097)
                ·
                  refine ⟨161384904831260326127913073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215179873108347101503884097 161384904831260326127913073)
                  ·
                    refine ⟨121038678623445244595934805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 161384904831260326127913073 121038678623445244595934805)
                    ·
                      refine ⟨1418422015118498960108611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 121038678623445244595934805 1418422015118498960108611)
                      ·
                        rfl

theorem cell23_2762367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_2762367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762367 prefixEnd_2762367 := by exact prefixLift 2762367
  have htrace : WordTrace (prefixWord ++ tailWord_2762367) baseStart_2762367 baseEnd_2762367 := by
    simpa [prefixWord, tailWord_2762367, baseEnd_2762367] using wordTrace_append hprefix tailTrace_2762367
  have hstable : (prefixWord ++ tailWord_2762367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762367).length < 2 ^ (prefixWord ++ tailWord_2762367).sum := by decide
  have hdescent : baseEnd_2762367 < baseStart_2762367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762468 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 3, 1, 3]
def baseStart_2762468 : Nat := 118140960795 + 2762468 * 2 ^ 59
def prefixEnd_2762468 : Nat := 4983230072969 + 3 ^ 40 * 2762468 * 2
def baseEnd_2762468 : Nat := 1418473876664603064945647

theorem tailTrace_2762468 : CollatzResearch.WordTrace tailWord_2762468 prefixEnd_2762468 1418473876664603064945647 := by
  unfold tailWord_2762468
  simp only [CollatzResearch.WordTrace]
  refine ⟨50377742678028851409116029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67170323570705135212154705 50377742678028851409116029)
  ·
    refine ⟨18891653504260819278418511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50377742678028851409116029 18891653504260819278418511)
    ·
      refine ⟨28337480256391228917627767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18891653504260819278418511 28337480256391228917627767)
      ·
        refine ⟨42506220384586843376441651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28337480256391228917627767 42506220384586843376441651)
        ·
          refine ⟨63759330576880265064662477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42506220384586843376441651 63759330576880265064662477)
          ·
            refine ⟨23909748966330099399248429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63759330576880265064662477 23909748966330099399248429)
            ·
              refine ⟨8966155862373787274718161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23909748966330099399248429 8966155862373787274718161)
              ·
                refine ⟨6724616896780340456038621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8966155862373787274718161 6724616896780340456038621)
                ·
                  refine ⟨2521731336292627671014483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6724616896780340456038621 2521731336292627671014483)
                  ·
                    refine ⟨3782597004438941506521725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2521731336292627671014483 3782597004438941506521725)
                    ·
                      refine ⟨1418473876664603064945647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3782597004438941506521725 1418473876664603064945647)
                      ·
                        rfl

theorem cell23_2762468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_2762468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762468 prefixEnd_2762468 := by exact prefixLift 2762468
  have htrace : WordTrace (prefixWord ++ tailWord_2762468) baseStart_2762468 baseEnd_2762468 := by
    simpa [prefixWord, tailWord_2762468, baseEnd_2762468] using wordTrace_append hprefix tailTrace_2762468
  have hstable : (prefixWord ++ tailWord_2762468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762468).length < 2 ^ (prefixWord ++ tailWord_2762468).sum := by decide
  have hdescent : baseEnd_2762468 < baseStart_2762468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762478 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 1, 5, 2]
def baseStart_2762478 : Nat := 118140960795 + 2762478 * 2 ^ 59
def prefixEnd_2762478 : Nat := 4983230072969 + 3 ^ 40 * 2762478 * 2
def baseEnd_2762478 : Nat := 1418479011471148025820601

theorem tailTrace_2762478 : CollatzResearch.WordTrace tailWord_2762478 prefixEnd_2762478 1418479011471148025820601 := by
  unfold tailWord_2762478
  simp only [CollatzResearch.WordTrace]
  refine ⟨12594481260752684315762011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67170566724014316350730725 12594481260752684315762011)
  ·
    refine ⟨18891721891129026473643017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12594481260752684315762011 18891721891129026473643017)
    ·
      refine ⟨14168791418346769855232263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18891721891129026473643017 14168791418346769855232263)
      ·
        refine ⟨21253187127520154782848395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14168791418346769855232263 21253187127520154782848395)
        ·
          refine ⟨31879780691280232174272593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21253187127520154782848395 31879780691280232174272593)
          ·
            refine ⟨23909835518460174130704445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31879780691280232174272593 23909835518460174130704445)
            ·
              refine ⟨8966188319422565299014167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23909835518460174130704445 8966188319422565299014167)
              ·
                refine ⟨13449282479133847948521251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8966188319422565299014167 13449282479133847948521251)
                ·
                  refine ⟨20173923718700771922781877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13449282479133847948521251 20173923718700771922781877)
                  ·
                    refine ⟨1891305348628197367760801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20173923718700771922781877 1891305348628197367760801)
                    ·
                      refine ⟨1418479011471148025820601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1891305348628197367760801 1418479011471148025820601)
                      ·
                        rfl

theorem cell23_2762478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_2762478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762478 prefixEnd_2762478 := by exact prefixLift 2762478
  have htrace : WordTrace (prefixWord ++ tailWord_2762478) baseStart_2762478 baseEnd_2762478 := by
    simpa [prefixWord, tailWord_2762478, baseEnd_2762478] using wordTrace_append hprefix tailTrace_2762478
  have hstable : (prefixWord ++ tailWord_2762478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762478).length < 2 ^ (prefixWord ++ tailWord_2762478).sum := by decide
  have hdescent : baseEnd_2762478 < baseStart_2762478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762511 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 3]
def baseStart_2762511 : Nat := 118140960795 + 2762511 * 2 ^ 59
def prefixEnd_2762511 : Nat := 4983230072969 + 3 ^ 40 * 2762511 * 2
def baseEnd_2762511 : Nat := 1418495956332746396707949

theorem tailTrace_2762511 : CollatzResearch.WordTrace tailWord_2762511 prefixEnd_2762511 1418495956332746396707949 := by
  unfold tailWord_2762511
  simp only [CollatzResearch.WordTrace]
  refine ⟨100757053694901921162047387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67171369129934614108031591 100757053694901921162047387)
  ·
    refine ⟨151135580542352881743071081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100757053694901921162047387 151135580542352881743071081)
    ·
      refine ⟨113351685406764661307303311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151135580542352881743071081 113351685406764661307303311)
      ·
        refine ⟨170027528110146991960954967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113351685406764661307303311 170027528110146991960954967)
        ·
          refine ⟨255041292165220487941432451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170027528110146991960954967 255041292165220487941432451)
          ·
            refine ⟨382561938247830731912148677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255041292165220487941432451 382561938247830731912148677)
            ·
              refine ⟨71730363421468262233527877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 382561938247830731912148677 71730363421468262233527877)
              ·
                refine ⟨13449443141525299168786477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71730363421468262233527877 13449443141525299168786477)
                ·
                  refine ⟨5043541178071987188294929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13449443141525299168786477 5043541178071987188294929)
                  ·
                    refine ⟨3782655883553990391221197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5043541178071987188294929 3782655883553990391221197)
                    ·
                      refine ⟨1418495956332746396707949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3782655883553990391221197 1418495956332746396707949)
                      ·
                        rfl

theorem cell23_2762511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 3].length) (baseStart_2762511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762511 prefixEnd_2762511 := by exact prefixLift 2762511
  have htrace : WordTrace (prefixWord ++ tailWord_2762511) baseStart_2762511 baseEnd_2762511 := by
    simpa [prefixWord, tailWord_2762511, baseEnd_2762511] using wordTrace_append hprefix tailTrace_2762511
  have hstable : (prefixWord ++ tailWord_2762511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762511).length < 2 ^ (prefixWord ++ tailWord_2762511).sum := by decide
  have hdescent : baseEnd_2762511 < baseStart_2762511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762531 : List Nat := [1, 1, 1, 4, 2, 1, 6, 7]
def baseStart_2762531 : Nat := 118140960795 + 2762531 * 2 ^ 59
def prefixEnd_2762531 : Nat := 4983230072969 + 3 ^ 40 * 2762531 * 2
def baseEnd_2762531 : Nat := 52537267627623567350291

theorem tailTrace_2762531 : CollatzResearch.WordTrace tailWord_2762531 prefixEnd_2762531 52537267627623567350291 := by
  unfold tailWord_2762531
  simp only [CollatzResearch.WordTrace]
  refine ⟨100757783154829464577775447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67171855436552976385183631 100757783154829464577775447)
  ·
    refine ⟨151136674732244196866663171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100757783154829464577775447 151136674732244196866663171)
    ·
      refine ⟨226705012098366295299994757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151136674732244196866663171 226705012098366295299994757)
      ·
        refine ⟨42507189768443680368749017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226705012098366295299994757 42507189768443680368749017)
        ·
          refine ⟨31880392326332760276561763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42507189768443680368749017 31880392326332760276561763)
          ·
            refine ⟨47820588489499140414842645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31880392326332760276561763 47820588489499140414842645)
            ·
              refine ⟨2241590085445272206945749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47820588489499140414842645 2241590085445272206945749)
              ·
                refine ⟨52537267627623567350291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2241590085445272206945749 52537267627623567350291)
                ·
                  rfl

theorem cell23_2762531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 7].length) (baseStart_2762531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762531 prefixEnd_2762531 := by exact prefixLift 2762531
  have htrace : WordTrace (prefixWord ++ tailWord_2762531) baseStart_2762531 baseEnd_2762531 := by
    simpa [prefixWord, tailWord_2762531, baseEnd_2762531] using wordTrace_append hprefix tailTrace_2762531
  have hstable : (prefixWord ++ tailWord_2762531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762531).length < 2 ^ (prefixWord ++ tailWord_2762531).sum := by decide
  have hdescent : baseEnd_2762531 < baseStart_2762531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762544 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 3, 9]
def baseStart_2762544 : Nat := 118140960795 + 2762544 * 2 ^ 59
def prefixEnd_2762544 : Nat := 4983230072969 + 3 ^ 40 * 2762544 * 2
def baseEnd_2762544 : Nat := 472837633731448255865099

theorem tailTrace_2762544 : CollatzResearch.WordTrace tailWord_2762544 prefixEnd_2762544 472837633731448255865099 := by
  unfold tailWord_2762544
  simp only [CollatzResearch.WordTrace]
  refine ⟨50379128651891183898999343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67172171535854911865332457 50379128651891183898999343)
  ·
    refine ⟨75568692977836775848499015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50379128651891183898999343 75568692977836775848499015)
    ·
      refine ⟨113353039466755163772748523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75568692977836775848499015 113353039466755163772748523)
      ·
        refine ⟨170029559200132745659122785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113353039466755163772748523 170029559200132745659122785)
        ·
          refine ⟨127522169400099559244342089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170029559200132745659122785 127522169400099559244342089)
          ·
            refine ⟨95641627050074669433256567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127522169400099559244342089 95641627050074669433256567)
            ·
              refine ⟨143462440575112004149884851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95641627050074669433256567 143462440575112004149884851)
              ·
                refine ⟨215193660862668006224827277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143462440575112004149884851 215193660862668006224827277)
                ·
                  refine ⟨80697622823500502334310229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215193660862668006224827277 80697622823500502334310229)
                  ·
                    refine ⟨472837633731448255865099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 80697622823500502334310229 472837633731448255865099)
                    ·
                      rfl

theorem cell23_2762544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 9].length) (baseStart_2762544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762544 prefixEnd_2762544 := by exact prefixLift 2762544
  have htrace : WordTrace (prefixWord ++ tailWord_2762544) baseStart_2762544 baseEnd_2762544 := by
    simpa [prefixWord, tailWord_2762544, baseEnd_2762544] using wordTrace_append hprefix tailTrace_2762544
  have hstable : (prefixWord ++ tailWord_2762544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762544).length < 2 ^ (prefixWord ++ tailWord_2762544).sum := by decide
  have hdescent : baseEnd_2762544 < baseStart_2762544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762548 : List Nat := [2, 5, 1, 1, 2, 3, 9]
def baseStart_2762548 : Nat := 118140960795 + 2762548 * 2 ^ 59
def prefixEnd_2762548 : Nat := 4983230072969 + 3 ^ 40 * 2762548 * 2
def baseEnd_2762548 : Nat := 17512530310085959900559

theorem tailTrace_2762548 : CollatzResearch.WordTrace tailWord_2762548 prefixEnd_2762548 17512530310085959900559 := by
  unfold tailWord_2762548
  simp only [CollatzResearch.WordTrace]
  refine ⟨50379201597883938240572149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67172268797178584320762865 50379201597883938240572149)
  ·
    refine ⟨4723050149801619210053639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50379201597883938240572149 4723050149801619210053639)
    ·
      refine ⟨7084575224702428815080459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4723050149801619210053639 7084575224702428815080459)
      ·
        refine ⟨10626862837053643222620689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7084575224702428815080459 10626862837053643222620689)
        ·
          refine ⟨7970147127790232416965517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10626862837053643222620689 7970147127790232416965517)
          ·
            refine ⟨2988805172921337156362069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7970147127790232416965517 2988805172921337156362069)
            ·
              refine ⟨17512530310085959900559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2988805172921337156362069 17512530310085959900559)
              ·
                rfl

theorem cell23_2762548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 9].length) (baseStart_2762548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762548 prefixEnd_2762548 := by exact prefixLift 2762548
  have htrace : WordTrace (prefixWord ++ tailWord_2762548) baseStart_2762548 baseEnd_2762548 := by
    simpa [prefixWord, tailWord_2762548, baseEnd_2762548] using wordTrace_append hprefix tailTrace_2762548
  have hstable : (prefixWord ++ tailWord_2762548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762548).length < 2 ^ (prefixWord ++ tailWord_2762548).sum := by decide
  have hdescent : baseEnd_2762548 < baseStart_2762548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762559 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 3, 2, 2]
def baseStart_2762559 : Nat := 118140960795 + 2762559 * 2 ^ 59
def prefixEnd_2762559 : Nat := 4983230072969 + 3 ^ 40 * 2762559 * 2
def baseEnd_2762559 : Nat := 1418520603404162208907729

theorem tailTrace_2762559 : CollatzResearch.WordTrace tailWord_2762559 prefixEnd_2762559 1418520603404162208907729 := by
  unfold tailWord_2762559
  simp only [CollatzResearch.WordTrace]
  refine ⟨100758804398728025359794731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67172536265818683573196487 100758804398728025359794731)
  ·
    refine ⟨151138206598092038039692097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100758804398728025359794731 151138206598092038039692097)
    ·
      refine ⟨113353654948569028529769073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151138206598092038039692097 113353654948569028529769073)
      ·
        refine ⟨85015241211426771397326805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113353654948569028529769073 85015241211426771397326805)
        ·
          refine ⟨1992544715892814954624847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 85015241211426771397326805 1992544715892814954624847)
          ·
            refine ⟨2988817073839222431937271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1992544715892814954624847 2988817073839222431937271)
            ·
              refine ⟨4483225610758833647905907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2988817073839222431937271 4483225610758833647905907)
              ·
                refine ⟨6724838416138250471858861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4483225610758833647905907 6724838416138250471858861)
                ·
                  refine ⟨2521814406051843926947073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6724838416138250471858861 2521814406051843926947073)
                  ·
                    refine ⟨1891360804538882945210305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2521814406051843926947073 1891360804538882945210305)
                    ·
                      refine ⟨1418520603404162208907729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1891360804538882945210305 1418520603404162208907729)
                      ·
                        rfl

theorem cell23_2762559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 3, 2, 2].length) (baseStart_2762559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762559 prefixEnd_2762559 := by exact prefixLift 2762559
  have htrace : WordTrace (prefixWord ++ tailWord_2762559) baseStart_2762559 baseEnd_2762559 := by
    simpa [prefixWord, tailWord_2762559, baseEnd_2762559] using wordTrace_append hprefix tailTrace_2762559
  have hstable : (prefixWord ++ tailWord_2762559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762559).length < 2 ^ (prefixWord ++ tailWord_2762559).sum := by decide
  have hdescent : baseEnd_2762559 < baseStart_2762559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762601 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 4, 4, 3]
def baseStart_2762601 : Nat := 118140960795 + 2762601 * 2 ^ 59
def prefixEnd_2762601 : Nat := 4983230072969 + 3 ^ 40 * 2762601 * 2
def baseEnd_2762601 : Nat := 1418542169591651044582535

theorem tailTrace_2762601 : CollatzResearch.WordTrace tailWord_2762601 prefixEnd_2762601 1418542169591651044582535 := by
  unfold tailWord_2762601
  simp only [CollatzResearch.WordTrace]
  refine ⟨100760336264575866532823657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67173557509717244355215771 100760336264575866532823657)
  ·
    refine ⟨75570252198431899899617743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100760336264575866532823657 75570252198431899899617743)
    ·
      refine ⟨113355378297647849849426615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75570252198431899899617743 113355378297647849849426615)
      ·
        refine ⟨170033067446471774774139923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113355378297647849849426615 170033067446471774774139923)
        ·
          refine ⟨255049601169707662161209885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170033067446471774774139923 255049601169707662161209885)
          ·
            refine ⟨95643600438640373310453707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255049601169707662161209885 95643600438640373310453707)
            ·
              refine ⟨143465400657960559965680561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95643600438640373310453707 143465400657960559965680561)
              ·
                refine ⟨107599050493470419974260421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143465400657960559965680561 107599050493470419974260421)
                ·
                  refine ⟨20174821967525703745173829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107599050493470419974260421 20174821967525703745173829)
                  ·
                    refine ⟨3782779118911069452220093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20174821967525703745173829 3782779118911069452220093)
                    ·
                      refine ⟨1418542169591651044582535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3782779118911069452220093 1418542169591651044582535)
                      ·
                        rfl

theorem cell23_2762601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 4, 3].length) (baseStart_2762601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762601 prefixEnd_2762601 := by exact prefixLift 2762601
  have htrace : WordTrace (prefixWord ++ tailWord_2762601) baseStart_2762601 baseEnd_2762601 := by
    simpa [prefixWord, tailWord_2762601, baseEnd_2762601] using wordTrace_append hprefix tailTrace_2762601
  have hstable : (prefixWord ++ tailWord_2762601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762601).length < 2 ^ (prefixWord ++ tailWord_2762601).sum := by decide
  have hdescent : baseEnd_2762601 < baseStart_2762601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
