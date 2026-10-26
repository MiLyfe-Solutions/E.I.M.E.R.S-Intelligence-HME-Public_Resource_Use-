import V185TrunkScan21Chunk100

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1226804 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 5]
def baseStart_1226804 : Nat := 118140960795 + 1226804 * 2 ^ 59
def prefixEnd_1226804 : Nat := 4983230072969 + 3 ^ 40 * 1226804 * 2
def baseEnd_1226804 : Nat := 279973387048232603292461

theorem tailTrace_1226804 : CollatzResearch.WordTrace tailWord_1226804 prefixEnd_1226804 279973387048232603292461 := by
  unfold tailWord_1226804
  simp only [CollatzResearch.WordTrace]
  refine ⟨22372608923753052143727733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29830145231670736191636977 22372608923753052143727733)
  ·
    refine ⟨2097432086601848638474475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22372608923753052143727733 2097432086601848638474475)
    ·
      refine ⟨3146148129902772957711713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2097432086601848638474475 3146148129902772957711713)
      ·
        refine ⟨2359611097427079718283785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3146148129902772957711713 2359611097427079718283785)
        ·
          refine ⟨1769708323070309788712839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2359611097427079718283785 1769708323070309788712839)
          ·
            refine ⟨2654562484605464683069259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769708323070309788712839 2654562484605464683069259)
            ·
              refine ⟨3981843726908197024603889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2654562484605464683069259 3981843726908197024603889)
              ·
                refine ⟨2986382795181147768452917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3981843726908197024603889 2986382795181147768452917)
                ·
                  refine ⟨279973387048232603292461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2986382795181147768452917 279973387048232603292461)
                  ·
                    rfl

theorem cell21_1226804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_1226804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1226804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1226804 prefixEnd_1226804 := by exact prefixLift 1226804
  have htrace : WordTrace (prefixWord ++ tailWord_1226804) baseStart_1226804 baseEnd_1226804 := by
    simpa [prefixWord, tailWord_1226804, baseEnd_1226804] using wordTrace_append hprefix tailTrace_1226804
  have hstable : (prefixWord ++ tailWord_1226804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226804).length < 2 ^ (prefixWord ++ tailWord_1226804).sum := by decide
  have hdescent : baseEnd_1226804 < baseStart_1226804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226911 : List Nat := [1, 1, 2, 6, 1, 3, 2, 1, 4]
def baseStart_1226911 : Nat := 118140960795 + 1226911 * 2 ^ 59
def prefixEnd_1226911 : Nat := 4983230072969 + 3 ^ 40 * 1226911 * 2
def baseEnd_1226911 : Nat := 279997805906024195008909

theorem tailTrace_1226911 : CollatzResearch.WordTrace tailWord_1226911 prefixEnd_1226911 279997805906024195008909 := by
  unfold tailWord_1226911
  simp only [CollatzResearch.WordTrace]
  refine ⟨44749120458118461561600587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29832746972078974374400391 44749120458118461561600587)
  ·
    refine ⟨67123680687177692342400881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44749120458118461561600587 67123680687177692342400881)
    ·
      refine ⟨50342760515383269256800661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67123680687177692342400881 50342760515383269256800661)
      ·
        refine ⟨2359816899158590746412531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50342760515383269256800661 2359816899158590746412531)
        ·
          refine ⟨3539725348737886119618797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2359816899158590746412531 3539725348737886119618797)
          ·
            refine ⟨1327397005776707294857049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3539725348737886119618797 1327397005776707294857049)
            ·
              refine ⟨995547754332530471142787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1327397005776707294857049 995547754332530471142787)
              ·
                refine ⟨1493321631498795706714181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995547754332530471142787 1493321631498795706714181)
                ·
                  refine ⟨279997805906024195008909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1493321631498795706714181 279997805906024195008909)
                  ·
                    rfl

theorem cell21_1226911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 4].length) (baseStart_1226911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1226911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1226911 prefixEnd_1226911 := by exact prefixLift 1226911
  have htrace : WordTrace (prefixWord ++ tailWord_1226911) baseStart_1226911 baseEnd_1226911 := by
    simpa [prefixWord, tailWord_1226911, baseEnd_1226911] using wordTrace_append hprefix tailTrace_1226911
  have hstable : (prefixWord ++ tailWord_1226911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226911).length < 2 ^ (prefixWord ++ tailWord_1226911).sum := by decide
  have hdescent : baseEnd_1226911 < baseStart_1226911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226984 : List Nat := [2, 1, 4, 1, 2, 3, 3, 5]
def baseStart_1226984 : Nat := 118140960795 + 1226984 * 2 ^ 59
def prefixEnd_1226984 : Nat := 4983230072969 + 3 ^ 40 * 1226984 * 2
def baseEnd_1226984 : Nat := 93338155166864096764031

theorem tailTrace_1226984 : CollatzResearch.WordTrace tailWord_1226984 prefixEnd_1226984 93338155166864096764031 := by
  unfold tailWord_1226984
  simp only [CollatzResearch.WordTrace]
  refine ⟨22375891493426997514504003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29834521991235996686005337 22375891493426997514504003)
  ·
    refine ⟨33563837240140496271756005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22375891493426997514504003 33563837240140496271756005)
    ·
      refine ⟨6293219482526343050954251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33563837240140496271756005 6293219482526343050954251)
      ·
        refine ⟨9439829223789514576431377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6293219482526343050954251 9439829223789514576431377)
        ·
          refine ⟨7079871917842135932323533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9439829223789514576431377 7079871917842135932323533)
          ·
            refine ⟨2654951969190800974621325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7079871917842135932323533 2654951969190800974621325)
            ·
              refine ⟨995606988446550365482997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2654951969190800974621325 995606988446550365482997)
              ·
                refine ⟨93338155166864096764031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 995606988446550365482997 93338155166864096764031)
                ·
                  rfl

theorem cell21_1226984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 5].length) (baseStart_1226984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1226984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1226984 prefixEnd_1226984 := by exact prefixLift 1226984
  have htrace : WordTrace (prefixWord ++ tailWord_1226984) baseStart_1226984 baseEnd_1226984 := by
    simpa [prefixWord, tailWord_1226984, baseEnd_1226984] using wordTrace_append hprefix tailTrace_1226984
  have hstable : (prefixWord ++ tailWord_1226984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226984).length < 2 ^ (prefixWord ++ tailWord_1226984).sum := by decide
  have hdescent : baseEnd_1226984 < baseStart_1226984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227060 : List Nat := [2, 5, 1, 1, 1, 4, 7]
def baseStart_1227060 : Nat := 118140960795 + 1227060 * 2 ^ 59
def prefixEnd_1227060 : Nat := 4983230072969 + 3 ^ 40 * 1227060 * 2
def baseEnd_1227060 : Nat := 31114645526225894113919

theorem tailTrace_1227060 : CollatzResearch.WordTrace tailWord_1227060 prefixEnd_1227060 31114645526225894113919 := by
  unfold tailWord_1227060
  simp only [CollatzResearch.WordTrace]
  refine ⟨22377277467289330004387317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29836369956385773339183089 22377277467289330004387317)
  ·
    refine ⟨2097869762558374687911311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22377277467289330004387317 2097869762558374687911311)
    ·
      refine ⟨3146804643837562031866967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2097869762558374687911311 3146804643837562031866967)
      ·
        refine ⟨4720206965756343047800451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3146804643837562031866967 4720206965756343047800451)
        ·
          refine ⟨7080310448634514571700677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4720206965756343047800451 7080310448634514571700677)
          ·
            refine ⟨1327558209118971482193877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7080310448634514571700677 1327558209118971482193877)
            ·
              refine ⟨31114645526225894113919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1327558209118971482193877 31114645526225894113919)
              ·
                rfl

theorem cell21_1227060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 7].length) (baseStart_1227060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227060 prefixEnd_1227060 := by exact prefixLift 1227060
  have htrace : WordTrace (prefixWord ++ tailWord_1227060) baseStart_1227060 baseEnd_1227060 := by
    simpa [prefixWord, tailWord_1227060, baseEnd_1227060] using wordTrace_append hprefix tailTrace_1227060
  have hstable : (prefixWord ++ tailWord_1227060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227060).length < 2 ^ (prefixWord ++ tailWord_1227060).sum := by decide
  have hdescent : baseEnd_1227060 < baseStart_1227060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227125 : List Nat := [1, 3, 4, 1, 2, 3, 2, 2, 3]
def baseStart_1227125 : Nat := 118140960795 + 1227125 * 2 ^ 59
def prefixEnd_1227125 : Nat := 4983230072969 + 3 ^ 40 * 1227125 * 2
def baseEnd_1227125 : Nat := 280046643621607378441805

theorem tailTrace_1227125 : CollatzResearch.WordTrace tailWord_1227125 prefixEnd_1227125 280046643621607378441805 := by
  unfold tailWord_1227125
  simp only [CollatzResearch.WordTrace]
  refine ⟨44756925679343176109890829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29837950452895450739927219 44756925679343176109890829)
  ·
    refine ⟨16783847129753691041209061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44756925679343176109890829 16783847129753691041209061)
    ·
      refine ⟨3146971336828817070226699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16783847129753691041209061 3146971336828817070226699)
      ·
        refine ⟨4720457005243225605340049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3146971336828817070226699 4720457005243225605340049)
        ·
          refine ⟨3540342753932419204005037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4720457005243225605340049 3540342753932419204005037)
          ·
            refine ⟨1327628532724657201501889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3540342753932419204005037 1327628532724657201501889)
            ·
              refine ⟨995721399543492901126417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1327628532724657201501889 995721399543492901126417)
              ·
                refine ⟨746791049657619675844813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 995721399543492901126417 746791049657619675844813)
                ·
                  refine ⟨280046643621607378441805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746791049657619675844813 280046643621607378441805)
                  ·
                    rfl

theorem cell21_1227125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_1227125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227125 prefixEnd_1227125 := by exact prefixLift 1227125
  have htrace : WordTrace (prefixWord ++ tailWord_1227125) baseStart_1227125 baseEnd_1227125 := by
    simpa [prefixWord, tailWord_1227125, baseEnd_1227125] using wordTrace_append hprefix tailTrace_1227125
  have hstable : (prefixWord ++ tailWord_1227125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227125).length < 2 ^ (prefixWord ++ tailWord_1227125).sum := by decide
  have hdescent : baseEnd_1227125 < baseStart_1227125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227150 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_1227150 : Nat := 118140960795 + 1227150 * 2 ^ 59
def prefixEnd_1227150 : Nat := 4983230072969 + 3 ^ 40 * 1227150 * 2
def baseEnd_1227150 : Nat := 280052348962212890525087

theorem tailTrace_1227150 : CollatzResearch.WordTrace tailWord_1227150 prefixEnd_1227150 280052348962212890525087 := by
  unfold tailWord_1227150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5594729688031575672443863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29838558336168403586367269 5594729688031575672443863)
  ·
    refine ⟨8392094532047363508665795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5594729688031575672443863 8392094532047363508665795)
    ·
      refine ⟨12588141798071045262998693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8392094532047363508665795 12588141798071045262998693)
      ·
        refine ⟨2360276587138320986812255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12588141798071045262998693 2360276587138320986812255)
        ·
          refine ⟨3540414880707481480218383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2360276587138320986812255 3540414880707481480218383)
          ·
            refine ⟨5310622321061222220327575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3540414880707481480218383 5310622321061222220327575)
            ·
              refine ⟨7965933481591833330491363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5310622321061222220327575 7965933481591833330491363)
              ·
                refine ⟨11948900222387749995737045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7965933481591833330491363 11948900222387749995737045)
                ·
                  refine ⟨280052348962212890525087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11948900222387749995737045 280052348962212890525087)
                  ·
                    rfl

theorem cell21_1227150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_1227150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227150 prefixEnd_1227150 := by exact prefixLift 1227150
  have htrace : WordTrace (prefixWord ++ tailWord_1227150) baseStart_1227150 baseEnd_1227150 := by
    simpa [prefixWord, tailWord_1227150, baseEnd_1227150] using wordTrace_append hprefix tailTrace_1227150
  have hstable : (prefixWord ++ tailWord_1227150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227150).length < 2 ^ (prefixWord ++ tailWord_1227150).sum := by decide
  have hdescent : baseEnd_1227150 < baseStart_1227150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227167 : List Nat := [1, 1, 2, 5, 1, 1, 4, 3, 3]
def baseStart_1227167 : Nat := 118140960795 + 1227167 * 2 ^ 59
def prefixEnd_1227167 : Nat := 4983230072969 + 3 ^ 40 * 1227167 * 2
def baseEnd_1227167 : Nat := 280056228593824638741719

theorem tailTrace_1227167 : CollatzResearch.WordTrace tailWord_1227167 prefixEnd_1227167 280056228593824638741719 := by
  unfold tailWord_1227167
  simp only [CollatzResearch.WordTrace]
  refine ⟨44758457545191017282919755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29838971696794011521946503 44758457545191017282919755)
  ·
    refine ⟨67137686317786525924379633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44758457545191017282919755 67137686317786525924379633)
    ·
      refine ⟨50353264738339894443284725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67137686317786525924379633 50353264738339894443284725)
      ·
        refine ⟨4720618569219365104057943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50353264738339894443284725 4720618569219365104057943)
        ·
          refine ⟨7080927853829047656086915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4720618569219365104057943 7080927853829047656086915)
          ·
            refine ⟨10621391780743571484130373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7080927853829047656086915 10621391780743571484130373)
            ·
              refine ⟨1991510958889419653274445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10621391780743571484130373 1991510958889419653274445)
              ·
                refine ⟨746816609583532369977917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1991510958889419653274445 746816609583532369977917)
                ·
                  refine ⟨280056228593824638741719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746816609583532369977917 280056228593824638741719)
                  ·
                    rfl

theorem cell21_1227167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 3].length) (baseStart_1227167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227167 prefixEnd_1227167 := by exact prefixLift 1227167
  have htrace : WordTrace (prefixWord ++ tailWord_1227167) baseStart_1227167 baseEnd_1227167 := by
    simpa [prefixWord, tailWord_1227167, baseEnd_1227167] using wordTrace_append hprefix tailTrace_1227167
  have hstable : (prefixWord ++ tailWord_1227167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227167).length < 2 ^ (prefixWord ++ tailWord_1227167).sum := by decide
  have hdescent : baseEnd_1227167 < baseStart_1227167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227209 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 5]
def baseStart_1227209 : Nat := 118140960795 + 1227209 * 2 ^ 59
def prefixEnd_1227209 : Nat := 4983230072969 + 3 ^ 40 * 1227209 * 2
def baseEnd_1227209 : Nat := 280065813566041899041633

theorem tailTrace_1227209 : CollatzResearch.WordTrace tailWord_1227209 prefixEnd_1227209 280065813566041899041633 := by
  unfold tailWord_1227209
  simp only [CollatzResearch.WordTrace]
  refine ⟨44759989411038858455948681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29839992940692572303965787 44759989411038858455948681)
  ·
    refine ⟨33569992058279143841961511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44759989411038858455948681 33569992058279143841961511)
    ·
      refine ⟨50354988087418715762942267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33569992058279143841961511 50354988087418715762942267)
      ·
        refine ⟨75532482131128073644413401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50354988087418715762942267 75532482131128073644413401)
        ·
          refine ⟨56649361598346055233310051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75532482131128073644413401 56649361598346055233310051)
          ·
            refine ⟨84974042397519082849965077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56649361598346055233310051 84974042397519082849965077)
            ·
              refine ⟨3983158237383707008592113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 84974042397519082849965077 3983158237383707008592113)
              ·
                refine ⟨2987368678037780256444085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3983158237383707008592113 2987368678037780256444085)
                ·
                  refine ⟨280065813566041899041633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2987368678037780256444085 280065813566041899041633)
                  ·
                    rfl

theorem cell21_1227209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_1227209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227209 prefixEnd_1227209 := by exact prefixLift 1227209
  have htrace : WordTrace (prefixWord ++ tailWord_1227209) baseStart_1227209 baseEnd_1227209 := by
    simpa [prefixWord, tailWord_1227209, baseEnd_1227209] using wordTrace_append hprefix tailTrace_1227209
  have hstable : (prefixWord ++ tailWord_1227209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227209).length < 2 ^ (prefixWord ++ tailWord_1227209).sum := by decide
  have hdescent : baseEnd_1227209 < baseStart_1227209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227218 : List Nat := [3, 2, 2, 4, 2, 1, 1, 3, 3]
def baseStart_1227218 : Nat := 118140960795 + 1227218 * 2 ^ 59
def prefixEnd_1227218 : Nat := 4983230072969 + 3 ^ 40 * 1227218 * 2
def baseEnd_1227218 : Nat := 280067867488659883391615

theorem tailTrace_1227218 : CollatzResearch.WordTrace tailWord_1227218 prefixEnd_1227218 280067867488659883391615 := by
  unfold tailWord_1227218
  simp only [CollatzResearch.WordTrace]
  refine ⟨11190079417001563248256577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29840211778670835328684205 11190079417001563248256577)
  ·
    refine ⟨8392559562751172436192433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11190079417001563248256577 8392559562751172436192433)
    ·
      refine ⟨6294419672063379327144325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8392559562751172436192433 6294419672063379327144325)
      ·
        refine ⟨1180203688511883623839561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6294419672063379327144325 1180203688511883623839561)
        ·
          refine ⟨885152766383912717879671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1180203688511883623839561 885152766383912717879671)
          ·
            refine ⟨1327729149575869076819507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885152766383912717879671 1327729149575869076819507)
            ·
              refine ⟨1991593724363803615229261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1327729149575869076819507 1991593724363803615229261)
              ·
                refine ⟨746847646636426355710973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1991593724363803615229261 746847646636426355710973)
                ·
                  refine ⟨280067867488659883391615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746847646636426355710973 280067867488659883391615)
                  ·
                    rfl

theorem cell21_1227218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_1227218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227218 prefixEnd_1227218 := by exact prefixLift 1227218
  have htrace : WordTrace (prefixWord ++ tailWord_1227218) baseStart_1227218 baseEnd_1227218 := by
    simpa [prefixWord, tailWord_1227218, baseEnd_1227218] using wordTrace_append hprefix tailTrace_1227218
  have hstable : (prefixWord ++ tailWord_1227218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227218).length < 2 ^ (prefixWord ++ tailWord_1227218).sum := by decide
  have hdescent : baseEnd_1227218 < baseStart_1227218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227240 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 6]
def baseStart_1227240 : Nat := 118140960795 + 1227240 * 2 ^ 59
def prefixEnd_1227240 : Nat := 4983230072969 + 3 ^ 40 * 1227240 * 2
def baseEnd_1227240 : Nat := 280072888188392734024903

theorem tailTrace_1227240 : CollatzResearch.WordTrace tailWord_1227240 prefixEnd_1227240 280072888188392734024903 := by
  unfold tailWord_1227240
  simp only [CollatzResearch.WordTrace]
  refine ⟨22380560036963275375163587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29840746715951033833551449 22380560036963275375163587)
  ·
    refine ⟨33570840055444913062745381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22380560036963275375163587 33570840055444913062745381)
    ·
      refine ⟨6294532510395921199264759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33570840055444913062745381 6294532510395921199264759)
      ·
        refine ⟨9441798765593881798897139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6294532510395921199264759 9441798765593881798897139)
        ·
          refine ⟨14162698148390822698345709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9441798765593881798897139 14162698148390822698345709)
          ·
            refine ⟨5311011805646558511879641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14162698148390822698345709 5311011805646558511879641)
            ·
              refine ⟨3983258854234918883909731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5311011805646558511879641 3983258854234918883909731)
              ·
                refine ⟨5974888281352378325864597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3983258854234918883909731 5974888281352378325864597)
                ·
                  refine ⟨280072888188392734024903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5974888281352378325864597 280072888188392734024903)
                  ·
                    rfl

theorem cell21_1227240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_1227240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227240 prefixEnd_1227240 := by exact prefixLift 1227240
  have htrace : WordTrace (prefixWord ++ tailWord_1227240) baseStart_1227240 baseEnd_1227240 := by
    simpa [prefixWord, tailWord_1227240, baseEnd_1227240] using wordTrace_append hprefix tailTrace_1227240
  have hstable : (prefixWord ++ tailWord_1227240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227240).length < 2 ^ (prefixWord ++ tailWord_1227240).sum := by decide
  have hdescent : baseEnd_1227240 < baseStart_1227240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227243 : List Nat := [1, 1, 1, 1, 2, 3, 7, 2, 3]
def baseStart_1227243 : Nat := 118140960795 + 1227243 * 2 ^ 59
def prefixEnd_1227243 : Nat := 4983230072969 + 3 ^ 40 * 1227243 * 2
def baseEnd_1227243 : Nat := 280073572829265395474897

theorem tailTrace_1227243 : CollatzResearch.WordTrace tailWord_1227243 prefixEnd_1227243 280073572829265395474897 := by
  unfold tailWord_1227243
  simp only [CollatzResearch.WordTrace]
  refine ⟨44761229492915682262686383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29840819661943788175124255 44761229492915682262686383)
  ·
    refine ⟨67141844239373523394029575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44761229492915682262686383 67141844239373523394029575)
    ·
      refine ⟨100712766359060285091044363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67141844239373523394029575 100712766359060285091044363)
      ·
        refine ⟨151069149538590427636566545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100712766359060285091044363 151069149538590427636566545)
        ·
          refine ⟨113301862153942820727424909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151069149538590427636566545 113301862153942820727424909)
          ·
            refine ⟨42488198307728557772784341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113301862153942820727424909 42488198307728557772784341)
            ·
              refine ⟨995817147837388072799633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 42488198307728557772784341 995817147837388072799633)
              ·
                refine ⟨746862860878041054599725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 995817147837388072799633 746862860878041054599725)
                ·
                  refine ⟨280073572829265395474897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746862860878041054599725 280073572829265395474897)
                  ·
                    rfl

theorem cell21_1227243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 3].length) (baseStart_1227243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227243 prefixEnd_1227243 := by exact prefixLift 1227243
  have htrace : WordTrace (prefixWord ++ tailWord_1227243) baseStart_1227243 baseEnd_1227243 := by
    simpa [prefixWord, tailWord_1227243, baseEnd_1227243] using wordTrace_append hprefix tailTrace_1227243
  have hstable : (prefixWord ++ tailWord_1227243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227243).length < 2 ^ (prefixWord ++ tailWord_1227243).sum := by decide
  have hdescent : baseEnd_1227243 < baseStart_1227243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227257 : List Nat := [1, 2, 1, 3, 1, 2, 6, 1, 4]
def baseStart_1227257 : Nat := 118140960795 + 1227257 * 2 ^ 59
def prefixEnd_1227257 : Nat := 4983230072969 + 3 ^ 40 * 1227257 * 2
def baseEnd_1227257 : Nat := 280076767820004482241535

theorem tailTrace_1227257 : CollatzResearch.WordTrace tailWord_1227257 prefixEnd_1227257 280076767820004482241535 := by
  unfold tailWord_1227257
  simp only [CollatzResearch.WordTrace]
  refine ⟨44761740114864962653696025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29841160076576641769130683 44761740114864962653696025)
  ·
    refine ⟨33571305086148721990272019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44761740114864962653696025 33571305086148721990272019)
    ·
      refine ⟨50356957629223082985408029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33571305086148721990272019 50356957629223082985408029)
      ·
        refine ⟨18883859110958656119528011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50356957629223082985408029 18883859110958656119528011)
        ·
          refine ⟨28325788666437984179292017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18883859110958656119528011 28325788666437984179292017)
          ·
            refine ⟨21244341499828488134469013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28325788666437984179292017 21244341499828488134469013)
            ·
              refine ⟨995828507804460381303235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21244341499828488134469013 995828507804460381303235)
              ·
                refine ⟨1493742761706690571954853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995828507804460381303235 1493742761706690571954853)
                ·
                  refine ⟨280076767820004482241535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1493742761706690571954853 280076767820004482241535)
                  ·
                    rfl

theorem cell21_1227257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 4].length) (baseStart_1227257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227257 prefixEnd_1227257 := by exact prefixLift 1227257
  have htrace : WordTrace (prefixWord ++ tailWord_1227257) baseStart_1227257 baseEnd_1227257 := by
    simpa [prefixWord, tailWord_1227257, baseEnd_1227257] using wordTrace_append hprefix tailTrace_1227257
  have hstable : (prefixWord ++ tailWord_1227257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227257).length < 2 ^ (prefixWord ++ tailWord_1227257).sum := by decide
  have hdescent : baseEnd_1227257 < baseStart_1227257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227361 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 5]
def baseStart_1227361 : Nat := 118140960795 + 1227361 * 2 ^ 59
def prefixEnd_1227361 : Nat := 4983230072969 + 3 ^ 40 * 1227361 * 2
def baseEnd_1227361 : Nat := 280100502036923412507989

theorem tailTrace_1227361 : CollatzResearch.WordTrace tailWord_1227361 prefixEnd_1227361 280100502036923412507989 := by
  unfold tailWord_1227361
  simp only [CollatzResearch.WordTrace]
  refine ⟨44765533306488188415481937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29843688870992125610321291 44765533306488188415481937)
  ·
    refine ⟨33574149979866141311611453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44765533306488188415481937 33574149979866141311611453)
    ·
      refine ⟨12590306242449802991854295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33574149979866141311611453 12590306242449802991854295)
      ·
        refine ⟨18885459363674704487781443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12590306242449802991854295 18885459363674704487781443)
        ·
          refine ⟨28328189045512056731672165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18885459363674704487781443 28328189045512056731672165)
          ·
            refine ⟨5311535446033510637188531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28328189045512056731672165 5311535446033510637188531)
            ·
              refine ⟨7967303169050265955782797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5311535446033510637188531 7967303169050265955782797)
              ·
                refine ⟨2987738688393849733418549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7967303169050265955782797 2987738688393849733418549)
                ·
                  refine ⟨280100502036923412507989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2987738688393849733418549 280100502036923412507989)
                  ·
                    rfl

theorem cell21_1227361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_1227361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227361 prefixEnd_1227361 := by exact prefixLift 1227361
  have htrace : WordTrace (prefixWord ++ tailWord_1227361) baseStart_1227361 baseEnd_1227361 := by
    simpa [prefixWord, tailWord_1227361, baseEnd_1227361] using wordTrace_append hprefix tailTrace_1227361
  have hstable : (prefixWord ++ tailWord_1227361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227361).length < 2 ^ (prefixWord ++ tailWord_1227361).sum := by decide
  have hdescent : baseEnd_1227361 < baseStart_1227361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227381 : List Nat := [1, 3, 4, 2, 2, 2, 2, 5]
def baseStart_1227381 : Nat := 118140960795 + 1227381 * 2 ^ 59
def prefixEnd_1227381 : Nat := 4983230072969 + 3 ^ 40 * 1227381 * 2
def baseEnd_1227381 : Nat := 93368355436469274058205

theorem tailTrace_1227381 : CollatzResearch.WordTrace tailWord_1227381 prefixEnd_1227381 93368355436469274058205 := by
  unfold tailWord_1227381
  simp only [CollatzResearch.WordTrace]
  refine ⟨44766262766415731831209997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29844175177610487887473331 44766262766415731831209997)
  ·
    refine ⟨16787348537405899436703749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44766262766415731831209997 16787348537405899436703749)
    ·
      refine ⟨3147627850763606144381953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16787348537405899436703749 3147627850763606144381953)
      ·
        refine ⟨2360720888072704608286465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3147627850763606144381953 2360720888072704608286465)
        ·
          refine ⟨1770540666054528456214849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2360720888072704608286465 1770540666054528456214849)
          ·
            refine ⟨1327905499540896342161137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1770540666054528456214849 1327905499540896342161137)
            ·
              refine ⟨995929124655672256620853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1327905499540896342161137 995929124655672256620853)
              ·
                refine ⟨93368355436469274058205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 995929124655672256620853 93368355436469274058205)
                ·
                  rfl

theorem cell21_1227381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 5].length) (baseStart_1227381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227381 prefixEnd_1227381 := by exact prefixLift 1227381
  have htrace : WordTrace (prefixWord ++ tailWord_1227381) baseStart_1227381 baseEnd_1227381 := by
    simpa [prefixWord, tailWord_1227381, baseEnd_1227381] using wordTrace_append hprefix tailTrace_1227381
  have hstable : (prefixWord ++ tailWord_1227381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227381).length < 2 ^ (prefixWord ++ tailWord_1227381).sum := by decide
  have hdescent : baseEnd_1227381 < baseStart_1227381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227530 : List Nat := [3, 1, 2, 2, 1, 2, 1, 6, 3]
def baseStart_1227530 : Nat := 118140960795 + 1227530 * 2 ^ 59
def prefixEnd_1227530 : Nat := 4983230072969 + 3 ^ 40 * 1227530 * 2
def baseEnd_1227530 : Nat := 280139070139416674190977

theorem tailTrace_1227530 : CollatzResearch.WordTrace tailWord_1227530 prefixEnd_1227530 280139070139416674190977 := by
  unfold tailWord_1227530
  simp only [CollatzResearch.WordTrace]
  refine ⟨11192924310718982569596011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29847798161917286852256029 11192924310718982569596011)
  ·
    refine ⟨16789386466078473854394017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11192924310718982569596011 16789386466078473854394017)
    ·
      refine ⟨12592039849558855390795513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16789386466078473854394017 12592039849558855390795513)
      ·
        refine ⟨9444029887169141543096635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12592039849558855390795513 9444029887169141543096635)
        ·
          refine ⟨14166044830753712314644953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9444029887169141543096635 14166044830753712314644953)
          ·
            refine ⟨10624533623065284235983715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14166044830753712314644953 10624533623065284235983715)
            ·
              refine ⟨15936800434597926353975573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10624533623065284235983715 15936800434597926353975573)
              ·
                refine ⟨747037520371777797842605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15936800434597926353975573 747037520371777797842605)
                ·
                  refine ⟨280139070139416674190977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747037520371777797842605 280139070139416674190977)
                  ·
                    rfl

theorem cell21_1227530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_1227530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227530 prefixEnd_1227530 := by exact prefixLift 1227530
  have htrace : WordTrace (prefixWord ++ tailWord_1227530) baseStart_1227530 baseEnd_1227530 := by
    simpa [prefixWord, tailWord_1227530, baseEnd_1227530] using wordTrace_append hprefix tailTrace_1227530
  have hstable : (prefixWord ++ tailWord_1227530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227530).length < 2 ^ (prefixWord ++ tailWord_1227530).sum := by decide
  have hdescent : baseEnd_1227530 < baseStart_1227530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227637 : List Nat := [1, 3, 4, 1, 1, 3, 2, 2, 4]
def baseStart_1227637 : Nat := 118140960795 + 1227637 * 2 ^ 59
def prefixEnd_1227637 : Nat := 4983230072969 + 3 ^ 40 * 1227637 * 2
def baseEnd_1227637 : Nat := 280163488997208265907425

theorem tailTrace_1227637 : CollatzResearch.WordTrace tailWord_1227637 prefixEnd_1227637 280163488997208265907425 := by
  unfold tailWord_1227637
  simp only [CollatzResearch.WordTrace]
  refine ⟨44775599853488287552529165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29850399902325525035019443 44775599853488287552529165)
  ·
    refine ⟨16790849945058107832198437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44775599853488287552529165 16790849945058107832198437)
    ·
      refine ⟨3148284364698395218537207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16790849945058107832198437 3148284364698395218537207)
      ·
        refine ⟨4722426547047592827805811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3148284364698395218537207 4722426547047592827805811)
        ·
          refine ⟨7083639820571389241708717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4722426547047592827805811 7083639820571389241708717)
          ·
            refine ⟨2656364932714270965640769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7083639820571389241708717 2656364932714270965640769)
            ·
              refine ⟨1992273699535703224230577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2656364932714270965640769 1992273699535703224230577)
              ·
                refine ⟨1494205274651777418172933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1992273699535703224230577 1494205274651777418172933)
                ·
                  refine ⟨280163488997208265907425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1494205274651777418172933 280163488997208265907425)
                  ·
                    rfl

theorem cell21_1227637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_1227637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227637 prefixEnd_1227637 := by exact prefixLift 1227637
  have htrace : WordTrace (prefixWord ++ tailWord_1227637) baseStart_1227637 baseEnd_1227637 := by
    simpa [prefixWord, tailWord_1227637, baseEnd_1227637] using wordTrace_append hprefix tailTrace_1227637
  have hstable : (prefixWord ++ tailWord_1227637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227637).length < 2 ^ (prefixWord ++ tailWord_1227637).sum := by decide
  have hdescent : baseEnd_1227637 < baseStart_1227637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227710 : List Nat := [4, 2, 1, 1, 1, 2, 2, 8]
def baseStart_1227710 : Nat := 118140960795 + 1227710 * 2 ^ 59
def prefixEnd_1227710 : Nat := 4983230072969 + 3 ^ 40 * 1227710 * 2
def baseEnd_1227710 : Nat := 93393382863925453730203

theorem tailTrace_1227710 : CollatzResearch.WordTrace tailWord_1227710 prefixEnd_1227710 93393382863925453730203 := by
  unfold tailWord_1227710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5597282797777977627492073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29852174921482547346624389 5597282797777977627492073)
  ·
    refine ⟨4197962098333483220619055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5597282797777977627492073 4197962098333483220619055)
    ·
      refine ⟨6296943147500224830928583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4197962098333483220619055 6296943147500224830928583)
      ·
        refine ⟨9445414721250337246392875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6296943147500224830928583 9445414721250337246392875)
        ·
          refine ⟨14168122081875505869589313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9445414721250337246392875 14168122081875505869589313)
          ·
            refine ⟨10626091561406629402191985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14168122081875505869589313 10626091561406629402191985)
            ·
              refine ⟨7969568671054972051643989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10626091561406629402191985 7969568671054972051643989)
              ·
                refine ⟨93393382863925453730203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7969568671054972051643989 93393382863925453730203)
                ·
                  rfl

theorem cell21_1227710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_1227710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227710 prefixEnd_1227710 := by exact prefixLift 1227710
  have htrace : WordTrace (prefixWord ++ tailWord_1227710) baseStart_1227710 baseEnd_1227710 := by
    simpa [prefixWord, tailWord_1227710, baseEnd_1227710] using wordTrace_append hprefix tailTrace_1227710
  have hstable : (prefixWord ++ tailWord_1227710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227710).length < 2 ^ (prefixWord ++ tailWord_1227710).sum := by decide
  have hdescent : baseEnd_1227710 < baseStart_1227710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227727 : List Nat := [1, 1, 2, 1, 1, 8, 2, 5]
def baseStart_1227727 : Nat := 118140960795 + 1227727 * 2 ^ 59
def prefixEnd_1227727 : Nat := 4983230072969 + 3 ^ 40 * 1227727 * 2
def baseEnd_1227727 : Nat := 93394676074462703135747

theorem tailTrace_1227727 : CollatzResearch.WordTrace tailWord_1227727 prefixEnd_1227727 93394676074462703135747 := by
  unfold tailWord_1227727
  simp only [CollatzResearch.WordTrace]
  refine ⟨44778882423162232923305435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29852588282108155282203623 44778882423162232923305435)
  ·
    refine ⟨67168323634743349384958153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44778882423162232923305435 67168323634743349384958153)
    ·
      refine ⟨50376242726057512038718615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67168323634743349384958153 50376242726057512038718615)
      ·
        refine ⟨75564364089086268058077923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50376242726057512038718615 75564364089086268058077923)
        ·
          refine ⟨113346546133629402087116885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75564364089086268058077923 113346546133629402087116885)
          ·
            refine ⟨1328279837503469555708401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 113346546133629402087116885 1328279837503469555708401)
            ·
              refine ⟨996209878127602166781301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1328279837503469555708401 996209878127602166781301)
              ·
                refine ⟨93394676074462703135747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 996209878127602166781301 93394676074462703135747)
                ·
                  rfl

theorem cell21_1227727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 5].length) (baseStart_1227727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227727 prefixEnd_1227727 := by exact prefixLift 1227727
  have htrace : WordTrace (prefixWord ++ tailWord_1227727) baseStart_1227727 baseEnd_1227727 := by
    simpa [prefixWord, tailWord_1227727, baseEnd_1227727] using wordTrace_append hprefix tailTrace_1227727
  have hstable : (prefixWord ++ tailWord_1227727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227727).length < 2 ^ (prefixWord ++ tailWord_1227727).sum := by decide
  have hdescent : baseEnd_1227727 < baseStart_1227727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227764 : List Nat := [2, 6, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1227764 : Nat := 118140960795 + 1227764 * 2 ^ 59
def prefixEnd_1227764 : Nat := 4983230072969 + 3 ^ 40 * 1227764 * 2
def baseEnd_1227764 : Nat := 280192472127484267290499

theorem tailTrace_1227764 : CollatzResearch.WordTrace tailWord_1227764 prefixEnd_1227764 280192472127484267290499 := by
  unfold tailWord_1227764
  simp only [CollatzResearch.WordTrace]
  refine ⟨22390115962014094121201173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29853487949352125494934897 22390115962014094121201173)
  ·
    refine ⟨1049536685719410661931305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22390115962014094121201173 1049536685719410661931305)
    ·
      refine ⟨787152514289557996448479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1049536685719410661931305 787152514289557996448479)
      ·
        refine ⟨1180728771434336994672719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 787152514289557996448479 1180728771434336994672719)
        ·
          refine ⟨1771093157151505492009079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180728771434336994672719 1771093157151505492009079)
          ·
            refine ⟨2656639735727258238013619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1771093157151505492009079 2656639735727258238013619)
            ·
              refine ⟨3984959603590887357020429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2656639735727258238013619 3984959603590887357020429)
              ·
                refine ⟨1494359851346582758882661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3984959603590887357020429 1494359851346582758882661)
                ·
                  refine ⟨280192472127484267290499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1494359851346582758882661 280192472127484267290499)
                  ·
                    rfl

theorem cell21_1227764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1227764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227764 prefixEnd_1227764 := by exact prefixLift 1227764
  have htrace : WordTrace (prefixWord ++ tailWord_1227764) baseStart_1227764 baseEnd_1227764 := by
    simpa [prefixWord, tailWord_1227764, baseEnd_1227764] using wordTrace_append hprefix tailTrace_1227764
  have hstable : (prefixWord ++ tailWord_1227764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227764).length < 2 ^ (prefixWord ++ tailWord_1227764).sum := by decide
  have hdescent : baseEnd_1227764 < baseStart_1227764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227772 : List Nat := [2, 2, 2, 1, 2, 4, 1, 3, 4]
def baseStart_1227772 : Nat := 118140960795 + 1227772 * 2 ^ 59
def prefixEnd_1227772 : Nat := 4983230072969 + 3 ^ 40 * 1227772 * 2
def baseEnd_1227772 : Nat := 280194297836478031157149

theorem tailTrace_1227772 : CollatzResearch.WordTrace tailWord_1227772 prefixEnd_1227772 280194297836478031157149 := by
  unfold tailWord_1227772
  simp only [CollatzResearch.WordTrace]
  refine ⟨22390261853999602804346785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29853682471999470405795713 22390261853999602804346785)
  ·
    refine ⟨16792696390499702103260089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22390261853999602804346785 16792696390499702103260089)
    ·
      refine ⟨12594522292874776577445067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16792696390499702103260089 12594522292874776577445067)
      ·
        refine ⟨18891783439312164866167601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12594522292874776577445067 18891783439312164866167601)
        ·
          refine ⟨14168837579484123649625701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18891783439312164866167601 14168837579484123649625701)
          ·
            refine ⟨2656657046153273184304819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14168837579484123649625701 2656657046153273184304819)
            ·
              refine ⟨3984985569229909776457229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2656657046153273184304819 3984985569229909776457229)
              ·
                refine ⟨1494369588461216166171461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3984985569229909776457229 1494369588461216166171461)
                ·
                  refine ⟨280194297836478031157149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1494369588461216166171461 280194297836478031157149)
                  ·
                    rfl

theorem cell21_1227772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_1227772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227772 prefixEnd_1227772 := by exact prefixLift 1227772
  have htrace : WordTrace (prefixWord ++ tailWord_1227772) baseStart_1227772 baseEnd_1227772 := by
    simpa [prefixWord, tailWord_1227772, baseEnd_1227772] using wordTrace_append hprefix tailTrace_1227772
  have hstable : (prefixWord ++ tailWord_1227772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227772).length < 2 ^ (prefixWord ++ tailWord_1227772).sum := by decide
  have hdescent : baseEnd_1227772 < baseStart_1227772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227786 : List Nat := [3, 1, 2, 2, 3, 1, 2, 7]
def baseStart_1227786 : Nat := 118140960795 + 1227786 * 2 ^ 59
def prefixEnd_1227786 : Nat := 4983230072969 + 3 ^ 40 * 1227786 * 2
def baseEnd_1227786 : Nat := 93399164275739039307929

theorem tailTrace_1227786 : CollatzResearch.WordTrace tailWord_1227786 prefixEnd_1227786 93399164275739039307929 := by
  unfold tailWord_1227786
  simp only [CollatzResearch.WordTrace]
  refine ⟨11195258582487121499925803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29854022886632323999802141 11195258582487121499925803)
  ·
    refine ⟨16792887873730682249888705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11195258582487121499925803 16792887873730682249888705)
    ·
      refine ⟨12594665905298011687416529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16792887873730682249888705 12594665905298011687416529)
      ·
        refine ⟨9445999428973508765562397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12594665905298011687416529 9445999428973508765562397)
        ·
          refine ⟨3542249785865065787085899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9445999428973508765562397 3542249785865065787085899)
          ·
            refine ⟨5313374678797598680628849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3542249785865065787085899 5313374678797598680628849)
            ·
              refine ⟨3985031009098199010471637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5313374678797598680628849 3985031009098199010471637)
              ·
                refine ⟨93399164275739039307929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3985031009098199010471637 93399164275739039307929)
                ·
                  rfl

theorem cell21_1227786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_1227786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227786 prefixEnd_1227786 := by exact prefixLift 1227786
  have htrace : WordTrace (prefixWord ++ tailWord_1227786) baseStart_1227786 baseEnd_1227786 := by
    simpa [prefixWord, tailWord_1227786, baseEnd_1227786] using wordTrace_append hprefix tailTrace_1227786
  have hstable : (prefixWord ++ tailWord_1227786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227786).length < 2 ^ (prefixWord ++ tailWord_1227786).sum := by decide
  have hdescent : baseEnd_1227786 < baseStart_1227786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227845 : List Nat := [1, 3, 1, 1, 1, 3, 2, 9]
def baseStart_1227845 : Nat := 118140960795 + 1227845 * 2 ^ 59
def prefixEnd_1227845 : Nat := 4983230072969 + 3 ^ 40 * 1227845 * 2
def baseEnd_1227845 : Nat := 93403652477015375480111

theorem tailTrace_1227845 : CollatzResearch.WordTrace tailWord_1227845 prefixEnd_1227845 93403652477015375480111 := by
  unfold tailWord_1227845
  simp only [CollatzResearch.WordTrace]
  refine ⟨44783186236734739076100989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29855457491156492717400659 44783186236734739076100989)
  ·
    refine ⟨16793694838775527153537871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44783186236734739076100989 16793694838775527153537871)
    ·
      refine ⟨25190542258163290730306807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16793694838775527153537871 25190542258163290730306807)
      ·
        refine ⟨37785813387244936095460211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25190542258163290730306807 37785813387244936095460211)
        ·
          refine ⟨56678720080867404143190317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37785813387244936095460211 56678720080867404143190317)
          ·
            refine ⟨21254520030325276553696369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56678720080867404143190317 21254520030325276553696369)
            ·
              refine ⟨15940890022743957415272277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21254520030325276553696369 15940890022743957415272277)
              ·
                refine ⟨93403652477015375480111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15940890022743957415272277 93403652477015375480111)
                ·
                  rfl

theorem cell21_1227845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 9].length) (baseStart_1227845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227845 prefixEnd_1227845 := by exact prefixLift 1227845
  have htrace : WordTrace (prefixWord ++ tailWord_1227845) baseStart_1227845 baseEnd_1227845 := by
    simpa [prefixWord, tailWord_1227845, baseEnd_1227845] using wordTrace_append hprefix tailTrace_1227845
  have hstable : (prefixWord ++ tailWord_1227845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227845).length < 2 ^ (prefixWord ++ tailWord_1227845).sum := by decide
  have hdescent : baseEnd_1227845 < baseStart_1227845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227902 : List Nat := [4, 2, 4, 1, 1, 2, 1, 3, 3]
def baseStart_1227902 : Nat := 118140960795 + 1227902 * 2 ^ 59
def prefixEnd_1227902 : Nat := 4983230072969 + 3 ^ 40 * 1227902 * 2
def baseEnd_1227902 : Nat := 280223965607626693990217

theorem tailTrace_1227902 : CollatzResearch.WordTrace tailWord_1227902 prefixEnd_1227902 280223965607626693990217 := by
  unfold tailWord_1227902
  simp only [CollatzResearch.WordTrace]
  refine ⟨5598158149691029726365745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29856843465018825207283973 5598158149691029726365745)
  ·
    refine ⟨4198618612268272294774309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5598158149691029726365745 4198618612268272294774309)
    ·
      refine ⟨787240989800301055270183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4198618612268272294774309 787240989800301055270183)
      ·
        refine ⟨1180861484700451582905275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 787240989800301055270183 1180861484700451582905275)
        ·
          refine ⟨1771292227050677374357913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180861484700451582905275 1771292227050677374357913)
          ·
            refine ⟨1328469170288008030768435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1771292227050677374357913 1328469170288008030768435)
            ·
              refine ⟨1992703755432012046152653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328469170288008030768435 1992703755432012046152653)
              ·
                refine ⟨747263908287004517307245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1992703755432012046152653 747263908287004517307245)
                ·
                  refine ⟨280223965607626693990217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747263908287004517307245 280223965607626693990217)
                  ·
                    rfl

theorem cell21_1227902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_1227902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227902 prefixEnd_1227902 := by exact prefixLift 1227902
  have htrace : WordTrace (prefixWord ++ tailWord_1227902) baseStart_1227902 baseEnd_1227902 := by
    simpa [prefixWord, tailWord_1227902, baseEnd_1227902] using wordTrace_append hprefix tailTrace_1227902
  have hstable : (prefixWord ++ tailWord_1227902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227902).length < 2 ^ (prefixWord ++ tailWord_1227902).sum := by decide
  have hdescent : baseEnd_1227902 < baseStart_1227902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227927 : List Nat := [1, 1, 3, 3, 3, 2, 3, 2, 3]
def baseStart_1227927 : Nat := 118140960795 + 1227927 * 2 ^ 59
def prefixEnd_1227927 : Nat := 4983230072969 + 3 ^ 40 * 1227927 * 2
def baseEnd_1227927 : Nat := 280229670948232206073499

theorem tailTrace_1227927 : CollatzResearch.WordTrace tailWord_1227927 prefixEnd_1227927 280229670948232206073499 := by
  unfold tailWord_1227927
  simp only [CollatzResearch.WordTrace]
  refine ⟨44786177022437667080586035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29857451348291778053724023 44786177022437667080586035)
  ·
    refine ⟨67179265533656500620879053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44786177022437667080586035 67179265533656500620879053)
    ·
      refine ⟨25192224575121187732829645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67179265533656500620879053 25192224575121187732829645)
      ·
        refine ⟨9447084215670445399811117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25192224575121187732829645 9447084215670445399811117)
        ·
          refine ⟨3542656580876417024929169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9447084215670445399811117 3542656580876417024929169)
          ·
            refine ⟨2656992435657312768696877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3542656580876417024929169 2656992435657312768696877)
            ·
              refine ⟨996372163371492288261329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2656992435657312768696877 996372163371492288261329)
              ·
                refine ⟨747279122528619216195997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 996372163371492288261329 747279122528619216195997)
                ·
                  refine ⟨280229670948232206073499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747279122528619216195997 280229670948232206073499)
                  ·
                    rfl

theorem cell21_1227927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 3].length) (baseStart_1227927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227927 prefixEnd_1227927 := by exact prefixLift 1227927
  have htrace : WordTrace (prefixWord ++ tailWord_1227927) baseStart_1227927 baseEnd_1227927 := by
    simpa [prefixWord, tailWord_1227927, baseEnd_1227927] using wordTrace_append hprefix tailTrace_1227927
  have hstable : (prefixWord ++ tailWord_1227927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227927).length < 2 ^ (prefixWord ++ tailWord_1227927).sum := by decide
  have hdescent : baseEnd_1227927 < baseStart_1227927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227941 : List Nat := [1, 3, 1, 2, 1, 6, 2, 1, 4]
def baseStart_1227941 : Nat := 118140960795 + 1227941 * 2 ^ 59
def prefixEnd_1227941 : Nat := 4983230072969 + 3 ^ 40 * 1227941 * 2
def baseEnd_1227941 : Nat := 280232865938971292840137

theorem tailTrace_1227941 : CollatzResearch.WordTrace tailWord_1227941 prefixEnd_1227941 280232865938971292840137 := by
  unfold tailWord_1227941
  simp only [CollatzResearch.WordTrace]
  refine ⟨44786687644386947471595677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29857791762924631647730451 44786687644386947471595677)
  ·
    refine ⟨16795007866645105301848379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44786687644386947471595677 16795007866645105301848379)
    ·
      refine ⟨25192511799967657952772569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16795007866645105301848379 25192511799967657952772569)
      ·
        refine ⟨18894383849975743464579427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25192511799967657952772569 18894383849975743464579427)
        ·
          refine ⟨28341575774963615196869141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18894383849975743464579427 28341575774963615196869141)
          ·
            refine ⟨1328511364451419462353241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28341575774963615196869141 1328511364451419462353241)
            ·
              refine ⟨996383523338564596764931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1328511364451419462353241 996383523338564596764931)
              ·
                refine ⟨1494575285007846895147397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996383523338564596764931 1494575285007846895147397)
                ·
                  refine ⟨280232865938971292840137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1494575285007846895147397 280232865938971292840137)
                  ·
                    rfl

theorem cell21_1227941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_1227941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227941 prefixEnd_1227941 := by exact prefixLift 1227941
  have htrace : WordTrace (prefixWord ++ tailWord_1227941) baseStart_1227941 baseEnd_1227941 := by
    simpa [prefixWord, tailWord_1227941, baseEnd_1227941] using wordTrace_append hprefix tailTrace_1227941
  have hstable : (prefixWord ++ tailWord_1227941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227941).length < 2 ^ (prefixWord ++ tailWord_1227941).sum := by decide
  have hdescent : baseEnd_1227941 < baseStart_1227941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227986 : List Nat := [3, 2, 2, 2, 1, 1, 3, 4, 3]
def baseStart_1227986 : Nat := 118140960795 + 1227986 * 2 ^ 59
def prefixEnd_1227986 : Nat := 4983230072969 + 3 ^ 40 * 1227986 * 2
def baseEnd_1227986 : Nat := 280243135552061214590045

theorem tailTrace_1227986 : CollatzResearch.WordTrace tailWord_1227986 prefixEnd_1227986 280243135552061214590045 := by
  unfold tailWord_1227986
  simp only [CollatzResearch.WordTrace]
  refine ⟨11197082232305980039245953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29858885952815946771322541 11197082232305980039245953)
  ·
    refine ⟨8397811674229485029434465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11197082232305980039245953 8397811674229485029434465)
    ·
      refine ⟨6298358755672113772075849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8397811674229485029434465 6298358755672113772075849)
      ·
        refine ⟨4723769066754085329056887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6298358755672113772075849 4723769066754085329056887)
        ·
          refine ⟨7085653600131127993585331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4723769066754085329056887 7085653600131127993585331)
          ·
            refine ⟨10628480400196691990377997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7085653600131127993585331 10628480400196691990377997)
            ·
              refine ⟨3985680150073759496391749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10628480400196691990377997 3985680150073759496391749)
              ·
                refine ⟨747315028138829905573453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3985680150073759496391749 747315028138829905573453)
                ·
                  refine ⟨280243135552061214590045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747315028138829905573453 280243135552061214590045)
                  ·
                    rfl

theorem cell21_1227986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_1227986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1227986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1227986 prefixEnd_1227986 := by exact prefixLift 1227986
  have htrace : WordTrace (prefixWord ++ tailWord_1227986) baseStart_1227986 baseEnd_1227986 := by
    simpa [prefixWord, tailWord_1227986, baseEnd_1227986] using wordTrace_append hprefix tailTrace_1227986
  have hstable : (prefixWord ++ tailWord_1227986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227986).length < 2 ^ (prefixWord ++ tailWord_1227986).sum := by decide
  have hdescent : baseEnd_1227986 < baseStart_1227986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228034 : List Nat := [3, 4, 1, 1, 3, 2, 1, 2, 4]
def baseStart_1228034 : Nat := 118140960795 + 1228034 * 2 ^ 59
def prefixEnd_1228034 : Nat := 4983230072969 + 3 ^ 40 * 1228034 * 2
def baseEnd_1228034 : Nat := 280254089806023797789947

theorem tailTrace_1228034 : CollatzResearch.WordTrace tailWord_1228034 prefixEnd_1228034 280254089806023797789947 := by
  unfold tailWord_1228034
  simp only [CollatzResearch.WordTrace]
  refine ⟨11197519908262506088682789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29860053088700016236487437 11197519908262506088682789)
  ·
    refine ⟨2099534982799219891628023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11197519908262506088682789 2099534982799219891628023)
    ·
      refine ⟨3149302474198829837442035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2099534982799219891628023 3149302474198829837442035)
      ·
        refine ⟨4723953711298244756163053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3149302474198829837442035 4723953711298244756163053)
        ·
          refine ⟨1771482641736841783561145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4723953711298244756163053 1771482641736841783561145)
          ·
            refine ⟨1328611981302631337670859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1771482641736841783561145 1328611981302631337670859)
            ·
              refine ⟨1992917971953947006506289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328611981302631337670859 1992917971953947006506289)
              ·
                refine ⟨1494688478965460254879717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1992917971953947006506289 1494688478965460254879717)
                ·
                  refine ⟨280254089806023797789947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1494688478965460254879717 280254089806023797789947)
                  ·
                    rfl

theorem cell21_1228034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_1228034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1228034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1228034 prefixEnd_1228034 := by exact prefixLift 1228034
  have htrace : WordTrace (prefixWord ++ tailWord_1228034) baseStart_1228034 baseEnd_1228034 := by
    simpa [prefixWord, tailWord_1228034, baseEnd_1228034] using wordTrace_append hprefix tailTrace_1228034
  have hstable : (prefixWord ++ tailWord_1228034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228034).length < 2 ^ (prefixWord ++ tailWord_1228034).sum := by decide
  have hdescent : baseEnd_1228034 < baseStart_1228034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228149 : List Nat := [1, 3, 4, 1, 12]
def baseStart_1228149 : Nat := 118140960795 + 1228149 * 2 ^ 59
def prefixEnd_1228149 : Nat := 4983230072969 + 3 ^ 40 * 1228149 * 2
def baseEnd_1228149 : Nat := 3460251041639619177445

theorem tailTrace_1228149 : CollatzResearch.WordTrace tailWord_1228149 prefixEnd_1228149 3460251041639619177445 := by
  unfold tailWord_1228149
  simp only [CollatzResearch.WordTrace]
  refine ⟨44794274027633398995167501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29862849351755599330111667 44794274027633398995167501)
  ·
    refine ⟨16797852760362524623187813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44794274027633398995167501 16797852760362524623187813)
    ·
      refine ⟨3149597392567973366847715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16797852760362524623187813 3149597392567973366847715)
      ·
        refine ⟨4724396088851960050271573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3149597392567973366847715 4724396088851960050271573)
        ·
          refine ⟨3460251041639619177445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4724396088851960050271573 3460251041639619177445)
          ·
            rfl

theorem cell21_1228149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 12].length) (baseStart_1228149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1228149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1228149 prefixEnd_1228149 := by exact prefixLift 1228149
  have htrace : WordTrace (prefixWord ++ tailWord_1228149) baseStart_1228149 baseEnd_1228149 := by
    simpa [prefixWord, tailWord_1228149, baseEnd_1228149] using wordTrace_append hprefix tailTrace_1228149
  have hstable : (prefixWord ++ tailWord_1228149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228149).length < 2 ^ (prefixWord ++ tailWord_1228149).sum := by decide
  have hdescent : baseEnd_1228149 < baseStart_1228149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228273 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 5]
def baseStart_1228273 : Nat := 118140960795 + 1228273 * 2 ^ 59
def prefixEnd_1228273 : Nat := 4983230072969 + 3 ^ 40 * 1228273 * 2
def baseEnd_1228273 : Nat := 280308632862212493306125

theorem tailTrace_1228273 : CollatzResearch.WordTrace tailWord_1228273 prefixEnd_1228273 280308632862212493306125 := by
  unfold tailWord_1228273
  simp only [CollatzResearch.WordTrace]
  refine ⟨44798796679184168172681473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29865864452789445448454315 44798796679184168172681473)
  ·
    refine ⟨33599097509388126129511105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44798796679184168172681473 33599097509388126129511105)
    ·
      refine ⟨25199323132041094597133329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33599097509388126129511105 25199323132041094597133329)
      ·
        refine ⟨18899492349030820947849997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25199323132041094597133329 18899492349030820947849997)
        ·
          refine ⟨7087309630886557855443749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18899492349030820947849997 7087309630886557855443749)
          ·
            refine ⟨1328870555791229597895703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7087309630886557855443749 1328870555791229597895703)
            ·
              refine ⟨1993305833686844396843555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328870555791229597895703 1993305833686844396843555)
              ·
                refine ⟨2989958750530266595265333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1993305833686844396843555 2989958750530266595265333)
                ·
                  refine ⟨280308632862212493306125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2989958750530266595265333 280308632862212493306125)
                  ·
                    rfl

theorem cell21_1228273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_1228273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1228273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1228273 prefixEnd_1228273 := by exact prefixLift 1228273
  have htrace : WordTrace (prefixWord ++ tailWord_1228273) baseStart_1228273 baseEnd_1228273 := by
    simpa [prefixWord, tailWord_1228273, baseEnd_1228273] using wordTrace_append hprefix tailTrace_1228273
  have hstable : (prefixWord ++ tailWord_1228273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228273).length < 2 ^ (prefixWord ++ tailWord_1228273).sum := by decide
  have hdescent : baseEnd_1228273 < baseStart_1228273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228349 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 5]
def baseStart_1228349 : Nat := 118140960795 + 1228349 * 2 ^ 59
def prefixEnd_1228349 : Nat := 4983230072969 + 3 ^ 40 * 1228349 * 2
def baseEnd_1228349 : Nat := 280325977097653250039303

theorem tailTrace_1228349 : CollatzResearch.WordTrace tailWord_1228349 prefixEnd_1228349 280325977097653250039303 := by
  unfold tailWord_1228349
  simp only [CollatzResearch.WordTrace]
  refine ⟨44801568626908833152448101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29867712417939222101632067 44801568626908833152448101)
  ·
    refine ⟨8400294117545406216084019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44801568626908833152448101 8400294117545406216084019)
    ·
      refine ⟨12600441176318109324126029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8400294117545406216084019 12600441176318109324126029)
      ·
        refine ⟨4725165441119290996547261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12600441176318109324126029 4725165441119290996547261)
        ·
          refine ⟨1771937040419734123705223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4725165441119290996547261 1771937040419734123705223)
          ·
            refine ⟨2657905560629601185557835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1771937040419734123705223 2657905560629601185557835)
            ·
              refine ⟨3986858340944401778336753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2657905560629601185557835 3986858340944401778336753)
              ·
                refine ⟨2990143755708301333752565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3986858340944401778336753 2990143755708301333752565)
                ·
                  refine ⟨280325977097653250039303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2990143755708301333752565 280325977097653250039303)
                  ·
                    rfl

theorem cell21_1228349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_1228349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1228349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1228349 prefixEnd_1228349 := by exact prefixLift 1228349
  have htrace : WordTrace (prefixWord ++ tailWord_1228349) baseStart_1228349 baseEnd_1228349 := by
    simpa [prefixWord, tailWord_1228349, baseEnd_1228349] using wordTrace_append hprefix tailTrace_1228349
  have hstable : (prefixWord ++ tailWord_1228349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228349).length < 2 ^ (prefixWord ++ tailWord_1228349).sum := by decide
  have hdescent : baseEnd_1228349 < baseStart_1228349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228380 : List Nat := [2, 2, 4, 1, 2, 1, 3, 2, 4]
def baseStart_1228380 : Nat := 118140960795 + 1228380 * 2 ^ 59
def prefixEnd_1228380 : Nat := 4983230072969 + 3 ^ 40 * 1228380 * 2
def baseEnd_1228380 : Nat := 280333051720004085022573

theorem tailTrace_1228380 : CollatzResearch.WordTrace tailWord_1228380 prefixEnd_1228380 280333051720004085022573 := by
  unfold tailWord_1228380
  simp only [CollatzResearch.WordTrace]
  refine ⟨22401349644898262723413297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29868466193197683631217729 22401349644898262723413297)
  ·
    refine ⟨16801012233673697042559973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22401349644898262723413297 16801012233673697042559973)
    ·
      refine ⟨3150189793813818195479995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16801012233673697042559973 3150189793813818195479995)
      ·
        refine ⟨4725284690720727293219993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3150189793813818195479995 4725284690720727293219993)
        ·
          refine ⟨3543963518040545469914995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4725284690720727293219993 3543963518040545469914995)
          ·
            refine ⟨5315945277060818204872493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3543963518040545469914995 5315945277060818204872493)
            ·
              refine ⟨1993479478897806826827185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5315945277060818204872493 1993479478897806826827185)
              ·
                refine ⟨1495109609173355120120389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1993479478897806826827185 1495109609173355120120389)
                ·
                  refine ⟨280333051720004085022573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1495109609173355120120389 280333051720004085022573)
                  ·
                    rfl

theorem cell21_1228380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_1228380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1228380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1228380 prefixEnd_1228380 := by exact prefixLift 1228380
  have htrace : WordTrace (prefixWord ++ tailWord_1228380) baseStart_1228380 baseEnd_1228380 := by
    simpa [prefixWord, tailWord_1228380, baseEnd_1228380] using wordTrace_append hprefix tailTrace_1228380
  have hstable : (prefixWord ++ tailWord_1228380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228380).length < 2 ^ (prefixWord ++ tailWord_1228380).sum := by decide
  have hdescent : baseEnd_1228380 < baseStart_1228380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228397 : List Nat := [1, 5, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1228397 : Nat := 118140960795 + 1228397 * 2 ^ 59
def prefixEnd_1228397 : Nat := 4983230072969 + 3 ^ 40 * 1228397 * 2
def baseEnd_1228397 : Nat := 280336931351615833239205

theorem tailTrace_1228397 : CollatzResearch.WordTrace tailWord_1228397 prefixEnd_1228397 280336931351615833239205 := by
  unfold tailWord_1228397
  simp only [CollatzResearch.WordTrace]
  refine ⟨44803319330734937350195445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29868879553823291566796963 44803319330734937350195445)
  ·
    refine ⟨4200311187256400376580823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44803319330734937350195445 4200311187256400376580823)
    ·
      refine ⟨6300466780884600564871235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4200311187256400376580823 6300466780884600564871235)
      ·
        refine ⟨9450700171326900847306853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6300466780884600564871235 9450700171326900847306853)
        ·
          refine ⟨1772006282123793908870035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9450700171326900847306853 1772006282123793908870035)
          ·
            refine ⟨2658009423185690863305053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1772006282123793908870035 2658009423185690863305053)
            ·
              refine ⟨996753533694634073739395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2658009423185690863305053 996753533694634073739395)
              ·
                refine ⟨1495130300541951110609093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996753533694634073739395 1495130300541951110609093)
                ·
                  refine ⟨280336931351615833239205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1495130300541951110609093 280336931351615833239205)
                  ·
                    rfl

theorem cell21_1228397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1228397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1228397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1228397 prefixEnd_1228397 := by exact prefixLift 1228397
  have htrace : WordTrace (prefixWord ++ tailWord_1228397) baseStart_1228397 baseEnd_1228397 := by
    simpa [prefixWord, tailWord_1228397, baseEnd_1228397] using wordTrace_append hprefix tailTrace_1228397
  have hstable : (prefixWord ++ tailWord_1228397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228397).length < 2 ^ (prefixWord ++ tailWord_1228397).sum := by decide
  have hdescent : baseEnd_1228397 < baseStart_1228397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228425 : List Nat := [1, 2, 1, 1, 4, 1, 5, 3, 3]
def baseStart_1228425 : Nat := 118140960795 + 1228425 * 2 ^ 59
def prefixEnd_1228425 : Nat := 4983230072969 + 3 ^ 40 * 1228425 * 2
def baseEnd_1228425 : Nat := 280343321333094006772481

theorem tailTrace_1228425 : CollatzResearch.WordTrace tailWord_1228425 prefixEnd_1228425 280343321333094006772481 := by
  unfold tailWord_1228425
  simp only [CollatzResearch.WordTrace]
  refine ⟨44804340574633498132214729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29869560383088998754809819 44804340574633498132214729)
  ·
    refine ⟨33603255430975123599161047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44804340574633498132214729 33603255430975123599161047)
    ·
      refine ⟨50404883146462685398741571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33603255430975123599161047 50404883146462685398741571)
      ·
        refine ⟨75607324719694028098112357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50404883146462685398741571 75607324719694028098112357)
        ·
          refine ⟨14176373384942630268396067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75607324719694028098112357 14176373384942630268396067)
          ·
            refine ⟨21264560077413945402594101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14176373384942630268396067 21264560077413945402594101)
            ·
              refine ⟨1993552507257557381493197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21264560077413945402594101 1993552507257557381493197)
              ·
                refine ⟨747582190221584018059949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1993552507257557381493197 747582190221584018059949)
                ·
                  refine ⟨280343321333094006772481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747582190221584018059949 280343321333094006772481)
                  ·
                    rfl

theorem cell21_1228425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 3].length) (baseStart_1228425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1228425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1228425 prefixEnd_1228425 := by exact prefixLift 1228425
  have htrace : WordTrace (prefixWord ++ tailWord_1228425) baseStart_1228425 baseEnd_1228425 := by
    simpa [prefixWord, tailWord_1228425, baseEnd_1228425] using wordTrace_append hprefix tailTrace_1228425
  have hstable : (prefixWord ++ tailWord_1228425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228425).length < 2 ^ (prefixWord ++ tailWord_1228425).sum := by decide
  have hdescent : baseEnd_1228425 < baseStart_1228425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228467 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 7]
def baseStart_1228467 : Nat := 118140960795 + 1228467 * 2 ^ 59
def prefixEnd_1228467 : Nat := 4983230072969 + 3 ^ 40 * 1228467 * 2
def baseEnd_1228467 : Nat := 280352906305311267072395

theorem tailTrace_1228467 : CollatzResearch.WordTrace tailWord_1228467 prefixEnd_1228467 280352906305311267072395 := by
  unfold tailWord_1228467
  simp only [CollatzResearch.WordTrace]
  refine ⟨44805872440481339305243655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29870581626987559536829103 44805872440481339305243655)
  ·
    refine ⟨67208808660722008957865483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44805872440481339305243655 67208808660722008957865483)
    ·
      refine ⟨100813212991083013436798225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67208808660722008957865483 100813212991083013436798225)
      ·
        refine ⟨75609909743312260077598669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100813212991083013436798225 75609909743312260077598669)
        ·
          refine ⟨28353716153742097529099501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75609909743312260077598669 28353716153742097529099501)
          ·
            refine ⟨10632643557653286573412313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28353716153742097529099501 10632643557653286573412313)
            ·
              refine ⟨7974482668239964930059235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10632643557653286573412313 7974482668239964930059235)
              ·
                refine ⟨11961724002359947395088853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7974482668239964930059235 11961724002359947395088853)
                ·
                  refine ⟨280352906305311267072395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11961724002359947395088853 280352906305311267072395)
                  ·
                    rfl

theorem cell21_1228467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 7].length) (baseStart_1228467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1228467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1228467 prefixEnd_1228467 := by exact prefixLift 1228467
  have htrace : WordTrace (prefixWord ++ tailWord_1228467) baseStart_1228467 baseEnd_1228467 := by
    simpa [prefixWord, tailWord_1228467, baseEnd_1228467] using wordTrace_append hprefix tailTrace_1228467
  have hstable : (prefixWord ++ tailWord_1228467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228467).length < 2 ^ (prefixWord ++ tailWord_1228467).sum := by decide
  have hdescent : baseEnd_1228467 < baseStart_1228467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228594 : List Nat := [3, 2, 1, 1, 3, 4, 1, 3, 3]
def baseStart_1228594 : Nat := 118140960795 + 1228594 * 2 ^ 59
def prefixEnd_1228594 : Nat := 4983230072969 + 3 ^ 40 * 1228594 * 2
def baseEnd_1228594 : Nat := 280381889435587268455469

theorem tailTrace_1228594 : CollatzResearch.WordTrace tailWord_1228594 prefixEnd_1228594 280381889435587268455469 := by
  unfold tailWord_1228594
  simp only [CollatzResearch.WordTrace]
  refine ⟨11202626127755309998779209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29873669674014159996744557 11202626127755309998779209)
  ·
    refine ⟨8401969595816482499084407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11202626127755309998779209 8401969595816482499084407)
    ·
      refine ⟨12602954393724723748626611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8401969595816482499084407 12602954393724723748626611)
      ·
        refine ⟨18904431590587085622939917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12602954393724723748626611 18904431590587085622939917)
        ·
          refine ⟨7089161846470157108602469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18904431590587085622939917 7089161846470157108602469)
          ·
            refine ⟨1329217846213154457862963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7089161846470157108602469 1329217846213154457862963)
            ·
              refine ⟨1993826769319731686794445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1329217846213154457862963 1993826769319731686794445)
              ·
                refine ⟨747685038494899382547917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1993826769319731686794445 747685038494899382547917)
                ·
                  refine ⟨280381889435587268455469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747685038494899382547917 280381889435587268455469)
                  ·
                    rfl

theorem cell21_1228594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_1228594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1228594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1228594 prefixEnd_1228594 := by exact prefixLift 1228594
  have htrace : WordTrace (prefixWord ++ tailWord_1228594) baseStart_1228594 baseEnd_1228594 := by
    simpa [prefixWord, tailWord_1228594, baseEnd_1228594] using wordTrace_append hprefix tailTrace_1228594
  have hstable : (prefixWord ++ tailWord_1228594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228594).length < 2 ^ (prefixWord ++ tailWord_1228594).sum := by decide
  have hdescent : baseEnd_1228594 < baseStart_1228594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228605 : List Nat := [1, 4, 1, 4, 1, 1, 9]
def baseStart_1228605 : Nat := 118140960795 + 1228605 * 2 ^ 59
def prefixEnd_1228605 : Nat := 4983230072969 + 3 ^ 40 * 1228605 * 2
def baseEnd_1228605 : Nat := 31153822198383743752457

theorem tailTrace_1228605 : CollatzResearch.WordTrace tailWord_1228605 prefixEnd_1228605 31153822198383743752457 := by
  unfold tailWord_1228605
  simp only [CollatzResearch.WordTrace]
  refine ⟨44810905713981388873767269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29873937142654259249178179 44810905713981388873767269)
  ·
    refine ⟨8402044821371510413831363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44810905713981388873767269 8402044821371510413831363)
    ·
      refine ⟨12603067232057265620747045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8402044821371510413831363 12603067232057265620747045)
      ·
        refine ⟨2363075106010737303890071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12603067232057265620747045 2363075106010737303890071)
        ·
          refine ⟨3544612659016105955835107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2363075106010737303890071 3544612659016105955835107)
          ·
            refine ⟨5316918988524158933752661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3544612659016105955835107 5316918988524158933752661)
            ·
              refine ⟨31153822198383743752457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5316918988524158933752661 31153822198383743752457)
              ·
                rfl

theorem cell21_1228605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 9].length) (baseStart_1228605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1228605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1228605 prefixEnd_1228605 := by exact prefixLift 1228605
  have htrace : WordTrace (prefixWord ++ tailWord_1228605) baseStart_1228605 baseEnd_1228605 := by
    simpa [prefixWord, tailWord_1228605, baseEnd_1228605] using wordTrace_append hprefix tailTrace_1228605
  have hstable : (prefixWord ++ tailWord_1228605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228605).length < 2 ^ (prefixWord ++ tailWord_1228605).sum := by decide
  have hdescent : baseEnd_1228605 < baseStart_1228605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228695 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 7]
def baseStart_1228695 : Nat := 118140960795 + 1228695 * 2 ^ 59
def prefixEnd_1228695 : Nat := 4983230072969 + 3 ^ 40 * 1228695 * 2
def baseEnd_1228695 : Nat := 280404939011633537271929

theorem tailTrace_1228695 : CollatzResearch.WordTrace tailWord_1228695 prefixEnd_1228695 280404939011633537271929 := by
  unfold tailWord_1228695
  simp only [CollatzResearch.WordTrace]
  refine ⟨44814188283655334244543539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29876125522436889496362359 44814188283655334244543539)
  ·
    refine ⟨67221282425483001366815309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44814188283655334244543539 67221282425483001366815309)
    ·
      refine ⟨25207980909556125512555741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67221282425483001366815309 25207980909556125512555741)
      ·
        refine ⟨9452992841083547067208403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25207980909556125512555741 9452992841083547067208403)
        ·
          refine ⟨14179489261625320600812605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9452992841083547067208403 14179489261625320600812605)
          ·
            refine ⟨5317308473109495225304727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14179489261625320600812605 5317308473109495225304727)
            ·
              refine ⟨7975962709664242837957091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5317308473109495225304727 7975962709664242837957091)
              ·
                refine ⟨11963944064496364256935637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7975962709664242837957091 11963944064496364256935637)
                ·
                  refine ⟨280404939011633537271929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11963944064496364256935637 280404939011633537271929)
                  ·
                    rfl

theorem cell21_1228695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 7].length) (baseStart_1228695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1228695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1228695 prefixEnd_1228695 := by exact prefixLift 1228695
  have htrace : WordTrace (prefixWord ++ tailWord_1228695) baseStart_1228695 baseEnd_1228695 := by
    simpa [prefixWord, tailWord_1228695, baseEnd_1228695] using wordTrace_append hprefix tailTrace_1228695
  have hstable : (prefixWord ++ tailWord_1228695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228695).length < 2 ^ (prefixWord ++ tailWord_1228695).sum := by decide
  have hdescent : baseEnd_1228695 < baseStart_1228695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228698 : List Nat := [3, 1, 1, 4, 2, 2, 3, 5]
def baseStart_1228698 : Nat := 118140960795 + 1228698 * 2 ^ 59
def prefixEnd_1228698 : Nat := 4983230072969 + 3 ^ 40 * 1228698 * 2
def baseEnd_1228698 : Nat := 93468541217502066240641

theorem tailTrace_1228698 : CollatzResearch.WordTrace tailWord_1228698 prefixEnd_1228698 93468541217502066240641 := by
  unfold tailWord_1228698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11203574425661116439225687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29876198468429643837935165 11203574425661116439225687)
  ·
    refine ⟨16805361638491674658838531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11203574425661116439225687 16805361638491674658838531)
    ·
      refine ⟨25208042457737511988257797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16805361638491674658838531 25208042457737511988257797)
      ·
        refine ⟨4726507960825783497798337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25208042457737511988257797 4726507960825783497798337)
        ·
          refine ⟨3544880970619337623348753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4726507960825783497798337 3544880970619337623348753)
          ·
            refine ⟨2658660727964503217511565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3544880970619337623348753 2658660727964503217511565)
            ·
              refine ⟨996997772986688706566837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2658660727964503217511565 996997772986688706566837)
              ·
                refine ⟨93468541217502066240641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 996997772986688706566837 93468541217502066240641)
                ·
                  rfl

theorem cell21_1228698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_1228698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1228698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1228698 prefixEnd_1228698 := by exact prefixLift 1228698
  have htrace : WordTrace (prefixWord ++ tailWord_1228698) baseStart_1228698 baseEnd_1228698 := by
    simpa [prefixWord, tailWord_1228698, baseEnd_1228698] using wordTrace_append hprefix tailTrace_1228698
  have hstable : (prefixWord ++ tailWord_1228698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228698).length < 2 ^ (prefixWord ++ tailWord_1228698).sum := by decide
  have hdescent : baseEnd_1228698 < baseStart_1228698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228757 : List Nat := [1, 3, 2, 3, 2, 2, 1, 7]
def baseStart_1228757 : Nat := 118140960795 + 1228757 * 2 ^ 59
def prefixEnd_1228757 : Nat := 4983230072969 + 3 ^ 40 * 1228757 * 2
def baseEnd_1228757 : Nat := 93473029418778402412823

theorem tailTrace_1228757 : CollatzResearch.WordTrace tailWord_1228757 prefixEnd_1228757 93473029418778402412823 := by
  unfold tailWord_1228757
  simp only [CollatzResearch.WordTrace]
  refine ⟨44816449609430718833300525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29877633072953812555533683 44816449609430718833300525)
  ·
    refine ⟨16806168603536519562487697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44816449609430718833300525 16806168603536519562487697)
    ·
      refine ⟨12604626452652389671865773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16806168603536519562487697 12604626452652389671865773)
      ·
        refine ⟨4726734919744646126949665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12604626452652389671865773 4726734919744646126949665)
        ·
          refine ⟨3545051189808484595212249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4726734919744646126949665 3545051189808484595212249)
          ·
            refine ⟨2658788392356363446409187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3545051189808484595212249 2658788392356363446409187)
            ·
              refine ⟨3988182588534545169613781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2658788392356363446409187 3988182588534545169613781)
              ·
                refine ⟨93473029418778402412823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3988182588534545169613781 93473029418778402412823)
                ·
                  rfl

theorem cell21_1228757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 7].length) (baseStart_1228757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1228757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1228757 prefixEnd_1228757 := by exact prefixLift 1228757
  have htrace : WordTrace (prefixWord ++ tailWord_1228757) baseStart_1228757 baseEnd_1228757 := by
    simpa [prefixWord, tailWord_1228757, baseEnd_1228757] using wordTrace_append hprefix tailTrace_1228757
  have hstable : (prefixWord ++ tailWord_1228757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228757).length < 2 ^ (prefixWord ++ tailWord_1228757).sum := by decide
  have hdescent : baseEnd_1228757 < baseStart_1228757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228833 : List Nat := [1, 2, 3, 2, 5, 8]
def baseStart_1228833 : Nat := 118140960795 + 1228833 * 2 ^ 59
def prefixEnd_1228833 : Nat := 4983230072969 + 3 ^ 40 * 1228833 * 2
def baseEnd_1228833 : Nat := 10386534536732443110061

theorem tailTrace_1228833 : CollatzResearch.WordTrace tailWord_1228833 prefixEnd_1228833 10386534536732443110061 := by
  unfold tailWord_1228833
  simp only [CollatzResearch.WordTrace]
  refine ⟨44819221557155383813067153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29879481038103589208711435 44819221557155383813067153)
  ·
    refine ⟨33614416167866537859800365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44819221557155383813067153 33614416167866537859800365)
    ·
      refine ⟨12605406062949951697425137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33614416167866537859800365 12605406062949951697425137)
      ·
        refine ⟨9454054547212463773068853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12605406062949951697425137 9454054547212463773068853)
        ·
          refine ⟨886317613801168478725205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9454054547212463773068853 886317613801168478725205)
          ·
            refine ⟨10386534536732443110061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 886317613801168478725205 10386534536732443110061)
            ·
              rfl

theorem cell21_1228833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 8].length) (baseStart_1228833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1228833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1228833 prefixEnd_1228833 := by exact prefixLift 1228833
  have htrace : WordTrace (prefixWord ++ tailWord_1228833) baseStart_1228833 baseEnd_1228833 := by
    simpa [prefixWord, tailWord_1228833, baseEnd_1228833] using wordTrace_append hprefix tailTrace_1228833
  have hstable : (prefixWord ++ tailWord_1228833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228833).length < 2 ^ (prefixWord ++ tailWord_1228833).sum := by decide
  have hdescent : baseEnd_1228833 < baseStart_1228833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228836 : List Nat := [2, 3, 1, 4, 2, 1, 2, 2, 4]
def baseStart_1228836 : Nat := 118140960795 + 1228836 * 2 ^ 59
def prefixEnd_1228836 : Nat := 4983230072969 + 3 ^ 40 * 1228836 * 2
def baseEnd_1228836 : Nat := 280437117132648625421641

theorem tailTrace_1228836 : CollatzResearch.WordTrace tailWord_1228836 prefixEnd_1228836 280437117132648625421641 := by
  unfold tailWord_1228836
  simp only [CollatzResearch.WordTrace]
  refine ⟨22409665488072257662713181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29879553984096343550284241 22409665488072257662713181)
  ·
    refine ⟨8403624558027096623517443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22409665488072257662713181 8403624558027096623517443)
    ·
      refine ⟨12605436837040644935276165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8403624558027096623517443 12605436837040644935276165)
      ·
        refine ⟨2363519406945120925364281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12605436837040644935276165 2363519406945120925364281)
        ·
          refine ⟨1772639555208840694023211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2363519406945120925364281 1772639555208840694023211)
          ·
            refine ⟨2658959332813261041034817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1772639555208840694023211 2658959332813261041034817)
            ·
              refine ⟨1994219499609945780776113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2658959332813261041034817 1994219499609945780776113)
              ·
                refine ⟨1495664624707459335582085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1994219499609945780776113 1495664624707459335582085)
                ·
                  refine ⟨280437117132648625421641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1495664624707459335582085 280437117132648625421641)
                  ·
                    rfl

theorem cell21_1228836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_1228836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1228836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1228836 prefixEnd_1228836 := by exact prefixLift 1228836
  have htrace : WordTrace (prefixWord ++ tailWord_1228836) baseStart_1228836 baseEnd_1228836 := by
    simpa [prefixWord, tailWord_1228836, baseEnd_1228836] using wordTrace_append hprefix tailTrace_1228836
  have hstable : (prefixWord ++ tailWord_1228836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228836).length < 2 ^ (prefixWord ++ tailWord_1228836).sum := by decide
  have hdescent : baseEnd_1228836 < baseStart_1228836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228937 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 8]
def baseStart_1228937 : Nat := 118140960795 + 1228937 * 2 ^ 59
def prefixEnd_1228937 : Nat := 4983230072969 + 3 ^ 40 * 1228937 * 2
def baseEnd_1228937 : Nat := 280460166708694894238101

theorem tailTrace_1228937 : CollatzResearch.WordTrace tailWord_1228937 prefixEnd_1228937 280460166708694894238101 := by
  unfold tailWord_1228937
  simp only [CollatzResearch.WordTrace]
  refine ⟨44823014748778609574853065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29882009832519073049902043 44823014748778609574853065)
  ·
    refine ⟨33617261061583957181139799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44823014748778609574853065 33617261061583957181139799)
    ·
      refine ⟨50425891592375935771709699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33617261061583957181139799 50425891592375935771709699)
      ·
        refine ⟨75638837388563903657564549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50425891592375935771709699 75638837388563903657564549)
        ·
          refine ⟨14182282010355731935793353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75638837388563903657564549 14182282010355731935793353)
          ·
            refine ⟨10636711507766798951845015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14182282010355731935793353 10636711507766798951845015)
            ·
              refine ⟨15955067261650198427767523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10636711507766798951845015 15955067261650198427767523)
              ·
                refine ⟨23932600892475297641651285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15955067261650198427767523 23932600892475297641651285)
                ·
                  refine ⟨280460166708694894238101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23932600892475297641651285 280460166708694894238101)
                  ·
                    rfl

theorem cell21_1228937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_1228937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1228937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1228937 prefixEnd_1228937 := by exact prefixLift 1228937
  have htrace : WordTrace (prefixWord ++ tailWord_1228937) baseStart_1228937 baseEnd_1228937 := by
    simpa [prefixWord, tailWord_1228937, baseEnd_1228937] using wordTrace_append hprefix tailTrace_1228937
  have hstable : (prefixWord ++ tailWord_1228937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228937).length < 2 ^ (prefixWord ++ tailWord_1228937).sum := by decide
  have hdescent : baseEnd_1228937 < baseStart_1228937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229095 : List Nat := [1, 1, 8, 1, 1, 1, 1, 7]
def baseStart_1229095 : Nat := 118140960795 + 1229095 * 2 ^ 59
def prefixEnd_1229095 : Nat := 4983230072969 + 3 ^ 40 * 1229095 * 2
def baseEnd_1229095 : Nat := 93498741487107243534815

theorem tailTrace_1229095 : CollatzResearch.WordTrace tailWord_1229095 prefixEnd_1229095 93498741487107243534815 := by
  unfold tailWord_1229095
  simp only [CollatzResearch.WordTrace]
  refine ⟨44828777482206202559104739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29885851654804135039403159 44828777482206202559104739)
  ·
    refine ⟨67243166223309303838657109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44828777482206202559104739 67243166223309303838657109)
    ·
      refine ⟨788005854179405904359263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 67243166223309303838657109 788005854179405904359263)
      ·
        refine ⟨1182008781269108856538895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 788005854179405904359263 1182008781269108856538895)
        ·
          refine ⟨1773013171903663284808343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182008781269108856538895 1773013171903663284808343)
          ·
            refine ⟨2659519757855494927212515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1773013171903663284808343 2659519757855494927212515)
            ·
              refine ⟨3989279636783242390818773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2659519757855494927212515 3989279636783242390818773)
              ·
                refine ⟨93498741487107243534815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3989279636783242390818773 93498741487107243534815)
                ·
                  rfl

theorem cell21_1229095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 7].length) (baseStart_1229095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229095 prefixEnd_1229095 := by exact prefixLift 1229095
  have htrace : WordTrace (prefixWord ++ tailWord_1229095) baseStart_1229095 baseEnd_1229095 := by
    simpa [prefixWord, tailWord_1229095, baseEnd_1229095] using wordTrace_append hprefix tailTrace_1229095
  have hstable : (prefixWord ++ tailWord_1229095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229095).length < 2 ^ (prefixWord ++ tailWord_1229095).sum := by decide
  have hdescent : baseEnd_1229095 < baseStart_1229095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229140 : List Nat := [2, 4, 1, 1, 2, 4, 2, 1, 4]
def baseStart_1229140 : Nat := 118140960795 + 1229140 * 2 ^ 59
def prefixEnd_1229140 : Nat := 4983230072969 + 3 ^ 40 * 1229140 * 2
def baseEnd_1229140 : Nat := 280506494074411652354353

theorem tailTrace_1229140 : CollatzResearch.WordTrace tailWord_1229140 prefixEnd_1229140 280506494074411652354353 := by
  unfold tailWord_1229140
  simp only [CollatzResearch.WordTrace]
  refine ⟨22415209383521587622246437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29886945844695450162995249 22415209383521587622246437)
  ·
    refine ⟨4202851759410297679171207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22415209383521587622246437 4202851759410297679171207)
    ·
      refine ⟨6304277639115446518756811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4202851759410297679171207 6304277639115446518756811)
      ·
        refine ⟨9456416458673169778135217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6304277639115446518756811 9456416458673169778135217)
        ·
          refine ⟨7092312344004877333601413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9456416458673169778135217 7092312344004877333601413)
          ·
            refine ⟨1329808564500914500050265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7092312344004877333601413 1329808564500914500050265)
            ·
              refine ⟨997356423375685875037699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1329808564500914500050265 997356423375685875037699)
              ·
                refine ⟨1496034635063528812556549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997356423375685875037699 1496034635063528812556549)
                ·
                  refine ⟨280506494074411652354353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1496034635063528812556549 280506494074411652354353)
                  ·
                    rfl

theorem cell21_1229140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_1229140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229140 prefixEnd_1229140 := by exact prefixLift 1229140
  have htrace : WordTrace (prefixWord ++ tailWord_1229140) baseStart_1229140 baseEnd_1229140 := by
    simpa [prefixWord, tailWord_1229140, baseEnd_1229140] using wordTrace_append hprefix tailTrace_1229140
  have hstable : (prefixWord ++ tailWord_1229140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229140).length < 2 ^ (prefixWord ++ tailWord_1229140).sum := by decide
  have hdescent : baseEnd_1229140 < baseStart_1229140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229179 : List Nat := [1, 1, 1, 1, 1, 16]
def baseStart_1229179 : Nat := 118140960795 + 1229179 * 2 ^ 59
def prefixEnd_1229179 : Nat := 4983230072969 + 3 ^ 40 * 1229179 * 2
def baseEnd_1229179 : Nat := 10389459052065046340899

theorem tailTrace_1229179 : CollatzResearch.WordTrace tailWord_1229179 prefixEnd_1229179 10389459052065046340899 := by
  unfold tailWord_1229179
  simp only [CollatzResearch.WordTrace]
  refine ⟨44831841213901884905162591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29887894142601256603441727 44831841213901884905162591)
  ·
    refine ⟨67247761820852827357743887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44831841213901884905162591 67247761820852827357743887)
    ·
      refine ⟨100871642731279241036615831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67247761820852827357743887 100871642731279241036615831)
      ·
        refine ⟨151307464096918861554923747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100871642731279241036615831 151307464096918861554923747)
        ·
          refine ⟨226961196145378292332385621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151307464096918861554923747 226961196145378292332385621)
          ·
            refine ⟨10389459052065046340899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 226961196145378292332385621 10389459052065046340899)
            ·
              rfl

theorem cell21_1229179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 16].length) (baseStart_1229179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229179 prefixEnd_1229179 := by exact prefixLift 1229179
  have htrace : WordTrace (prefixWord ++ tailWord_1229179) baseStart_1229179 baseEnd_1229179 := by
    simpa [prefixWord, tailWord_1229179, baseEnd_1229179] using wordTrace_append hprefix tailTrace_1229179
  have hstable : (prefixWord ++ tailWord_1229179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229179).length < 2 ^ (prefixWord ++ tailWord_1229179).sum := by decide
  have hdescent : baseEnd_1229179 < baseStart_1229179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229185 : List Nat := [1, 2, 4, 3, 1, 2, 1, 4, 3]
def baseStart_1229185 : Nat := 118140960795 + 1229185 * 2 ^ 59
def prefixEnd_1229185 : Nat := 4983230072969 + 3 ^ 40 * 1229185 * 2
def baseEnd_1229185 : Nat := 280516763687501574104261

theorem tailTrace_1229185 : CollatzResearch.WordTrace tailWord_1229185 prefixEnd_1229185 280516763687501574104261 := by
  unfold tailWord_1229185
  simp only [CollatzResearch.WordTrace]
  refine ⟨44832060051880147929881009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29888040034586765286587339 44832060051880147929881009)
  ·
    refine ⟨33624045038910110947410757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44832060051880147929881009 33624045038910110947410757)
    ·
      refine ⟨6304508444795645802639517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33624045038910110947410757 6304508444795645802639517)
      ·
        refine ⟨2364190666798367175989819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6304508444795645802639517 2364190666798367175989819)
        ·
          refine ⟨3546286000197550763984729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2364190666798367175989819 3546286000197550763984729)
          ·
            refine ⟨2659714500148163072988547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3546286000197550763984729 2659714500148163072988547)
            ·
              refine ⟨3989571750222244609482821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2659714500148163072988547 3989571750222244609482821)
              ·
                refine ⟨748044703166670864278029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3989571750222244609482821 748044703166670864278029)
                ·
                  refine ⟨280516763687501574104261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748044703166670864278029 280516763687501574104261)
                  ·
                    rfl

theorem cell21_1229185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 3].length) (baseStart_1229185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229185 prefixEnd_1229185 := by exact prefixLift 1229185
  have htrace : WordTrace (prefixWord ++ tailWord_1229185) baseStart_1229185 baseEnd_1229185 := by
    simpa [prefixWord, tailWord_1229185, baseEnd_1229185] using wordTrace_append hprefix tailTrace_1229185
  have hstable : (prefixWord ++ tailWord_1229185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229185).length < 2 ^ (prefixWord ++ tailWord_1229185).sum := by decide
  have hdescent : baseEnd_1229185 < baseStart_1229185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229196 : List Nat := [2, 2, 1, 2, 1, 4, 3, 6]
def baseStart_1229196 : Nat := 118140960795 + 1229196 * 2 ^ 59
def prefixEnd_1229196 : Nat := 4983230072969 + 3 ^ 40 * 1229196 * 2
def baseEnd_1229196 : Nat := 93506424679122666473635

theorem tailTrace_1229196 : CollatzResearch.WordTrace tailWord_1229196 prefixEnd_1229196 93506424679122666473635 := by
  unfold tailWord_1229196
  simp only [CollatzResearch.WordTrace]
  refine ⟨22416230627420148404265721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29888307503226864539020961 22416230627420148404265721)
  ·
    refine ⟨16812172970565111303199291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22416230627420148404265721 16812172970565111303199291)
    ·
      refine ⟨25218259455847666954798937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16812172970565111303199291 25218259455847666954798937)
      ·
        refine ⟨18913694591885750216099203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25218259455847666954798937 18913694591885750216099203)
        ·
          refine ⟨28370541887828625324148805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18913694591885750216099203 28370541887828625324148805)
          ·
            refine ⟨5319476603967867248277901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28370541887828625324148805 5319476603967867248277901)
            ·
              refine ⟨1994803726487950218104213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5319476603967867248277901 1994803726487950218104213)
              ·
                refine ⟨93506424679122666473635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1994803726487950218104213 93506424679122666473635)
                ·
                  rfl

theorem cell21_1229196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 6].length) (baseStart_1229196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229196 prefixEnd_1229196 := by exact prefixLift 1229196
  have htrace : WordTrace (prefixWord ++ tailWord_1229196) baseStart_1229196 baseEnd_1229196 := by
    simpa [prefixWord, tailWord_1229196, baseEnd_1229196] using wordTrace_append hprefix tailTrace_1229196
  have hstable : (prefixWord ++ tailWord_1229196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229196).length < 2 ^ (prefixWord ++ tailWord_1229196).sum := by decide
  have hdescent : baseEnd_1229196 < baseStart_1229196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229244 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 5]
def baseStart_1229244 : Nat := 118140960795 + 1229244 * 2 ^ 59
def prefixEnd_1229244 : Nat := 4983230072969 + 3 ^ 40 * 1229244 * 2
def baseEnd_1229244 : Nat := 280530228291330582620807

theorem tailTrace_1229244 : CollatzResearch.WordTrace tailWord_1229244 prefixEnd_1229244 280530228291330582620807 := by
  unfold tailWord_1229244
  simp only [CollatzResearch.WordTrace]
  refine ⟨22417105979333200503139393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29889474639110934004185857 22417105979333200503139393)
  ·
    refine ⟨16812829484499900377354545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22417105979333200503139393 16812829484499900377354545)
    ·
      refine ⟨12609622113374925283015909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16812829484499900377354545 12609622113374925283015909)
      ·
        refine ⟨2364304146257798490565483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12609622113374925283015909 2364304146257798490565483)
        ·
          refine ⟨3546456219386697735848225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2364304146257798490565483 3546456219386697735848225)
          ·
            refine ⟨2659842164540023301886169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3546456219386697735848225 2659842164540023301886169)
            ·
              refine ⟨1994881623405017476414627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2659842164540023301886169 1994881623405017476414627)
              ·
                refine ⟨2992322435107526214621941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1994881623405017476414627 2992322435107526214621941)
                ·
                  refine ⟨280530228291330582620807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2992322435107526214621941 280530228291330582620807)
                  ·
                    rfl

theorem cell21_1229244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_1229244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229244 prefixEnd_1229244 := by exact prefixLift 1229244
  have htrace : WordTrace (prefixWord ++ tailWord_1229244) baseStart_1229244 baseEnd_1229244 := by
    simpa [prefixWord, tailWord_1229244, baseEnd_1229244] using wordTrace_append hprefix tailTrace_1229244
  have hstable : (prefixWord ++ tailWord_1229244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229244).length < 2 ^ (prefixWord ++ tailWord_1229244).sum := by decide
  have hdescent : baseEnd_1229244 < baseStart_1229244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229331 : List Nat := [1, 1, 1, 2, 1, 5, 1, 9]
def baseStart_1229331 : Nat := 118140960795 + 1229331 * 2 ^ 59
def prefixEnd_1229331 : Nat := 4983230072969 + 3 ^ 40 * 1229331 * 2
def baseEnd_1229331 : Nat := 93516694292212588223543

theorem tailTrace_1229331 : CollatzResearch.WordTrace tailWord_1229331 prefixEnd_1229331 93516694292212588223543 := by
  unfold tailWord_1229331
  simp only [CollatzResearch.WordTrace]
  refine ⟨44837385109351214864695847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29891590072900809909797231 44837385109351214864695847)
  ·
    refine ⟨67256077664026822297043771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44837385109351214864695847 67256077664026822297043771)
    ·
      refine ⟨100884116496040233445565657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67256077664026822297043771 100884116496040233445565657)
      ·
        refine ⟨75663087372030175084174243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100884116496040233445565657 75663087372030175084174243)
        ·
          refine ⟨113494631058045262626261365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75663087372030175084174243 113494631058045262626261365)
          ·
            refine ⟨10640121661691743371212003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113494631058045262626261365 10640121661691743371212003)
            ·
              refine ⟨15960182492537615056818005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10640121661691743371212003 15960182492537615056818005)
              ·
                refine ⟨93516694292212588223543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15960182492537615056818005 93516694292212588223543)
                ·
                  rfl

theorem cell21_1229331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 9].length) (baseStart_1229331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229331 prefixEnd_1229331 := by exact prefixLift 1229331
  have htrace : WordTrace (prefixWord ++ tailWord_1229331) baseStart_1229331 baseEnd_1229331 := by
    simpa [prefixWord, tailWord_1229331, baseEnd_1229331] using wordTrace_append hprefix tailTrace_1229331
  have hstable : (prefixWord ++ tailWord_1229331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229331).length < 2 ^ (prefixWord ++ tailWord_1229331).sum := by decide
  have hdescent : baseEnd_1229331 < baseStart_1229331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229348 : List Nat := [2, 3, 1, 5, 10]
def baseStart_1229348 : Nat := 118140960795 + 1229348 * 2 ^ 59
def prefixEnd_1229348 : Nat := 4983230072969 + 3 ^ 40 * 1229348 * 2
def baseEnd_1229348 : Nat := 3463629166768512504781

theorem tailTrace_1229348 : CollatzResearch.WordTrace tailWord_1229348 prefixEnd_1229348 3463629166768512504781 := by
  unfold tailWord_1229348
  simp only [CollatzResearch.WordTrace]
  refine ⟨22419002575144813384032349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29892003433526417845376465 22419002575144813384032349)
  ·
    refine ⟨8407125965679305019012131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22419002575144813384032349 8407125965679305019012131)
    ·
      refine ⟨12610688948518957528518197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8407125965679305019012131 12610688948518957528518197)
      ·
        refine ⟨1182252088923652268298581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12610688948518957528518197 1182252088923652268298581)
        ·
          refine ⟨3463629166768512504781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1182252088923652268298581 3463629166768512504781)
          ·
            rfl

theorem cell21_1229348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 10].length) (baseStart_1229348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229348 prefixEnd_1229348 := by exact prefixLift 1229348
  have htrace : WordTrace (prefixWord ++ tailWord_1229348) baseStart_1229348 baseEnd_1229348 := by
    simpa [prefixWord, tailWord_1229348, baseEnd_1229348] using wordTrace_append hprefix tailTrace_1229348
  have hstable : (prefixWord ++ tailWord_1229348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229348).length < 2 ^ (prefixWord ++ tailWord_1229348).sum := by decide
  have hdescent : baseEnd_1229348 < baseStart_1229348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229354 : List Nat := [3, 1, 4, 1, 1, 4, 2, 2, 3]
def baseStart_1229354 : Nat := 118140960795 + 1229354 * 2 ^ 59
def prefixEnd_1229354 : Nat := 4983230072969 + 3 ^ 40 * 1229354 * 2
def baseEnd_1229354 : Nat := 280555331789994835787249

theorem tailTrace_1229354 : CollatzResearch.WordTrace tailWord_1229354 prefixEnd_1229354 280555331789994835787249 := by
  unfold tailWord_1229354
  simp only [CollatzResearch.WordTrace]
  refine ⟨11209555997066972448195779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29892149325511926528522077 11209555997066972448195779)
  ·
    refine ⟨16814333995600458672293669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11209555997066972448195779 16814333995600458672293669)
    ·
      refine ⟨3152687624175086001055063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16814333995600458672293669 3152687624175086001055063)
      ·
        refine ⟨4729031436262629001582595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3152687624175086001055063 4729031436262629001582595)
        ·
          refine ⟨7093547154393943502373893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4729031436262629001582595 7093547154393943502373893)
          ·
            refine ⟨1330040091448864406695105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7093547154393943502373893 1330040091448864406695105)
            ·
              refine ⟨997530068586648305021329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1330040091448864406695105 997530068586648305021329)
              ·
                refine ⟨748147551439986228765997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 997530068586648305021329 748147551439986228765997)
                ·
                  refine ⟨280555331789994835787249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748147551439986228765997 280555331789994835787249)
                  ·
                    rfl

theorem cell21_1229354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_1229354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229354 prefixEnd_1229354 := by exact prefixLift 1229354
  have htrace : WordTrace (prefixWord ++ tailWord_1229354) baseStart_1229354 baseEnd_1229354 := by
    simpa [prefixWord, tailWord_1229354, baseEnd_1229354] using wordTrace_append hprefix tailTrace_1229354
  have hstable : (prefixWord ++ tailWord_1229354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229354).length < 2 ^ (prefixWord ++ tailWord_1229354).sum := by decide
  have hdescent : baseEnd_1229354 < baseStart_1229354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229396 : List Nat := [2, 4, 1, 1, 1, 3, 1, 5, 3]
def baseStart_1229396 : Nat := 118140960795 + 1229396 * 2 ^ 59
def prefixEnd_1229396 : Nat := 4983230072969 + 3 ^ 40 * 1229396 * 2
def baseEnd_1229396 : Nat := 280564916762212096087163

theorem tailTrace_1229396 : CollatzResearch.WordTrace tailWord_1229396 prefixEnd_1229396 280564916762212096087163 := by
  unfold tailWord_1229396
  simp only [CollatzResearch.WordTrace]
  refine ⟨22419877927057865482906021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29893170569410487310541361 22419877927057865482906021)
  ·
    refine ⟨4203727111323349778044879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22419877927057865482906021 4203727111323349778044879)
    ·
      refine ⟨6305590666985024667067319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4203727111323349778044879 6305590666985024667067319)
      ·
        refine ⟨9458386000477537000600979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6305590666985024667067319 9458386000477537000600979)
        ·
          refine ⟨14187579000716305500901469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9458386000477537000600979 14187579000716305500901469)
          ·
            refine ⟨5320342125268614562838051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14187579000716305500901469 5320342125268614562838051)
            ·
              refine ⟨7980513187902921844257077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5320342125268614562838051 7980513187902921844257077)
              ·
                refine ⟨748173111365898922899101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7980513187902921844257077 748173111365898922899101)
                ·
                  refine ⟨280564916762212096087163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748173111365898922899101 280564916762212096087163)
                  ·
                    rfl

theorem cell21_1229396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_1229396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229396 prefixEnd_1229396 := by exact prefixLift 1229396
  have htrace : WordTrace (prefixWord ++ tailWord_1229396) baseStart_1229396 baseEnd_1229396 := by
    simpa [prefixWord, tailWord_1229396, baseEnd_1229396] using wordTrace_append hprefix tailTrace_1229396
  have hstable : (prefixWord ++ tailWord_1229396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229396).length < 2 ^ (prefixWord ++ tailWord_1229396).sum := by decide
  have hdescent : baseEnd_1229396 < baseStart_1229396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229469 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 6]
def baseStart_1229469 : Nat := 118140960795 + 1229469 * 2 ^ 59
def prefixEnd_1229469 : Nat := 4983230072969 + 3 ^ 40 * 1229469 * 2
def baseEnd_1229469 : Nat := 280581576356780191370347

theorem tailTrace_1229469 : CollatzResearch.WordTrace tailWord_1229469 prefixEnd_1229469 280581576356780191370347 := by
  unfold tailWord_1229469
  simp only [CollatzResearch.WordTrace]
  refine ⟨44842418382851264433219461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29894945588567509622146307 44842418382851264433219461)
  ·
    refine ⟨8407953446784612081228649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44842418382851264433219461 8407953446784612081228649)
    ·
      refine ⟨6305965085088459060921487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8407953446784612081228649 6305965085088459060921487)
      ·
        refine ⟨9458947627632688591382231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6305965085088459060921487 9458947627632688591382231)
        ·
          refine ⟨14188421441449032887073347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9458947627632688591382231 14188421441449032887073347)
          ·
            refine ⟨21282632162173549330610021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14188421441449032887073347 21282632162173549330610021)
            ·
              refine ⟨3990493530407540499489379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21282632162173549330610021 3990493530407540499489379)
              ·
                refine ⟨5985740295611310749234069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3990493530407540499489379 5985740295611310749234069)
                ·
                  refine ⟨280581576356780191370347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5985740295611310749234069 280581576356780191370347)
                  ·
                    rfl

theorem cell21_1229469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_1229469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229469 prefixEnd_1229469 := by exact prefixLift 1229469
  have htrace : WordTrace (prefixWord ++ tailWord_1229469) baseStart_1229469 baseEnd_1229469 := by
    simpa [prefixWord, tailWord_1229469, baseEnd_1229469] using wordTrace_append hprefix tailTrace_1229469
  have hstable : (prefixWord ++ tailWord_1229469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229469).length < 2 ^ (prefixWord ++ tailWord_1229469).sum := by decide
  have hdescent : baseEnd_1229469 < baseStart_1229469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229472 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 5]
def baseStart_1229472 : Nat := 118140960795 + 1229472 * 2 ^ 59
def prefixEnd_1229472 : Nat := 4983230072969 + 3 ^ 40 * 1229472 * 2
def baseEnd_1229472 : Nat := 280582260997652852820341

theorem tailTrace_1229472 : CollatzResearch.WordTrace tailWord_1229472 prefixEnd_1229472 280582260997652852820341 := by
  unfold tailWord_1229472
  simp only [CollatzResearch.WordTrace]
  refine ⟨22421263900920197972789335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29895018534560263963719113 22421263900920197972789335)
  ·
    refine ⟨33631895851380296959184003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22421263900920197972789335 33631895851380296959184003)
    ·
      refine ⟨50447843777070445438776005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33631895851380296959184003 50447843777070445438776005)
      ·
        refine ⟨9458970708200708519770501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50447843777070445438776005 9458970708200708519770501)
        ·
          refine ⟨1773557007787632847456969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9458970708200708519770501 1773557007787632847456969)
          ·
            refine ⟨1330167755840724635592727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1773557007787632847456969 1330167755840724635592727)
            ·
              refine ⟨1995251633761086953389091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330167755840724635592727 1995251633761086953389091)
              ·
                refine ⟨2992877450641630430083637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995251633761086953389091 2992877450641630430083637)
                ·
                  refine ⟨280582260997652852820341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2992877450641630430083637 280582260997652852820341)
                  ·
                    rfl

theorem cell21_1229472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_1229472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229472 prefixEnd_1229472 := by exact prefixLift 1229472
  have htrace : WordTrace (prefixWord ++ tailWord_1229472) baseStart_1229472 baseEnd_1229472 := by
    simpa [prefixWord, tailWord_1229472, baseEnd_1229472] using wordTrace_append hprefix tailTrace_1229472
  have hstable : (prefixWord ++ tailWord_1229472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229472).length < 2 ^ (prefixWord ++ tailWord_1229472).sum := by decide
  have hdescent : baseEnd_1229472 < baseStart_1229472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229517 : List Nat := [1, 6, 2, 1, 2, 9]
def baseStart_1229517 : Nat := 118140960795 + 1229517 * 2 ^ 59
def prefixEnd_1229517 : Nat := 4983230072969 + 3 ^ 40 * 1229517 * 2
def baseEnd_1229517 : Nat := 10392315948546028687787

theorem tailTrace_1229517 : CollatzResearch.WordTrace tailWord_1229517 prefixEnd_1229517 10392315948546028687787 := by
  unfold tailWord_1229517
  simp only [CollatzResearch.WordTrace]
  refine ⟨44844169086677368630966805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29896112724451579087311203 44844169086677368630966805)
  ·
    refine ⟨2102070425938001654576569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44844169086677368630966805 2102070425938001654576569)
    ·
      refine ⟨1576552819453501240932427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2102070425938001654576569 1576552819453501240932427)
      ·
        refine ⟨2364829229180251861398641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1576552819453501240932427 2364829229180251861398641)
        ·
          refine ⟨1773621921885188896048981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2364829229180251861398641 1773621921885188896048981)
          ·
            refine ⟨10392315948546028687787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1773621921885188896048981 10392315948546028687787)
            ·
              rfl

theorem cell21_1229517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 9].length) (baseStart_1229517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229517 prefixEnd_1229517 := by exact prefixLift 1229517
  have htrace : WordTrace (prefixWord ++ tailWord_1229517) baseStart_1229517 baseEnd_1229517 := by
    simpa [prefixWord, tailWord_1229517, baseEnd_1229517] using wordTrace_append hprefix tailTrace_1229517
  have hstable : (prefixWord ++ tailWord_1229517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229517).length < 2 ^ (prefixWord ++ tailWord_1229517).sum := by decide
  have hdescent : baseEnd_1229517 < baseStart_1229517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229545 : List Nat := [1, 2, 1, 1, 1, 2, 6, 3, 4]
def baseStart_1229545 : Nat := 118140960795 + 1229545 * 2 ^ 59
def prefixEnd_1229545 : Nat := 4983230072969 + 3 ^ 40 * 1229545 * 2
def baseEnd_1229545 : Nat := 280598920592220948103525

theorem tailTrace_1229545 : CollatzResearch.WordTrace tailWord_1229545 prefixEnd_1229545 280598920592220948103525 := by
  unfold tailWord_1229545
  simp only [CollatzResearch.WordTrace]
  refine ⟨44845190330575929412986089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29896793553717286275324059 44845190330575929412986089)
  ·
    refine ⟨33633892747931947059739567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44845190330575929412986089 33633892747931947059739567)
    ·
      refine ⟨50450839121897920589609351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33633892747931947059739567 50450839121897920589609351)
      ·
        refine ⟨75676258682846880884414027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50450839121897920589609351 75676258682846880884414027)
        ·
          refine ⟨113514388024270321326621041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75676258682846880884414027 113514388024270321326621041)
          ·
            refine ⟨85135791018202740994965781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113514388024270321326621041 85135791018202740994965781)
            ·
              refine ⟨3990740203978253484139021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85135791018202740994965781 3990740203978253484139021)
              ·
                refine ⟨1496527576491845056552133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3990740203978253484139021 1496527576491845056552133)
                ·
                  refine ⟨280598920592220948103525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1496527576491845056552133 280598920592220948103525)
                  ·
                    rfl

theorem cell21_1229545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_1229545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229545 prefixEnd_1229545 := by exact prefixLift 1229545
  have htrace : WordTrace (prefixWord ++ tailWord_1229545) baseStart_1229545 baseEnd_1229545 := by
    simpa [prefixWord, tailWord_1229545, baseEnd_1229545] using wordTrace_append hprefix tailTrace_1229545
  have hstable : (prefixWord ++ tailWord_1229545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229545).length < 2 ^ (prefixWord ++ tailWord_1229545).sum := by decide
  have hdescent : baseEnd_1229545 < baseStart_1229545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229621 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 6]
def baseStart_1229621 : Nat := 118140960795 + 1229621 * 2 ^ 59
def prefixEnd_1229621 : Nat := 4983230072969 + 3 ^ 40 * 1229621 * 2
def baseEnd_1229621 : Nat := 280616264827661704836703

theorem tailTrace_1229621 : CollatzResearch.WordTrace tailWord_1229621 prefixEnd_1229621 280616264827661704836703 := by
  unfold tailWord_1229621
  simp only [CollatzResearch.WordTrace]
  refine ⟨44847962278300594392752717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29898641518867062928501811 44847962278300594392752717)
  ·
    refine ⟨16817985854362722897282269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44847962278300594392752717 16817985854362722897282269)
    ·
      refine ⟨6306744695386021086480851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16817985854362722897282269 6306744695386021086480851)
      ·
        refine ⟨9460117043079031629721277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6306744695386021086480851 9460117043079031629721277)
        ·
          refine ⟨3547543891154636861145479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9460117043079031629721277 3547543891154636861145479)
          ·
            refine ⟨5321315836731955291718219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3547543891154636861145479 5321315836731955291718219)
            ·
              refine ⟨7981973755097932937577329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5321315836731955291718219 7981973755097932937577329)
              ·
                refine ⟨5986480316323449703182997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7981973755097932937577329 5986480316323449703182997)
                ·
                  refine ⟨280616264827661704836703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5986480316323449703182997 280616264827661704836703)
                  ·
                    rfl

theorem cell21_1229621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_1229621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229621 prefixEnd_1229621 := by exact prefixLift 1229621
  have htrace : WordTrace (prefixWord ++ tailWord_1229621) baseStart_1229621 baseEnd_1229621 := by
    simpa [prefixWord, tailWord_1229621, baseEnd_1229621] using wordTrace_append hprefix tailTrace_1229621
  have hstable : (prefixWord ++ tailWord_1229621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229621).length < 2 ^ (prefixWord ++ tailWord_1229621).sum := by decide
  have hdescent : baseEnd_1229621 < baseStart_1229621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229655 : List Nat := [1, 1, 3, 2, 4, 3, 2, 1, 4]
def baseStart_1229655 : Nat := 118140960795 + 1229655 * 2 ^ 59
def prefixEnd_1229655 : Nat := 4983230072969 + 3 ^ 40 * 1229655 * 2
def baseEnd_1229655 : Nat := 280624024090885201269967

theorem tailTrace_1229655 : CollatzResearch.WordTrace tailWord_1229655 prefixEnd_1229655 280624024090885201269967 := by
  unfold tailWord_1229655
  simp only [CollatzResearch.WordTrace]
  refine ⟨44849202360177418199490419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29899468240118278799660279 44849202360177418199490419)
  ·
    refine ⟨67273803540266127299235629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44849202360177418199490419 67273803540266127299235629)
    ·
      refine ⟨25227676327599797737213361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67273803540266127299235629 25227676327599797737213361)
      ·
        refine ⟨18920757245699848302910021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25227676327599797737213361 18920757245699848302910021)
        ·
          refine ⟨3547641983568721556795629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18920757245699848302910021 3547641983568721556795629)
          ·
            refine ⟨1330365743838270583798361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3547641983568721556795629 1330365743838270583798361)
            ·
              refine ⟨997774307878702937848771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1330365743838270583798361 997774307878702937848771)
              ·
                refine ⟨1496661461818054406773157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997774307878702937848771 1496661461818054406773157)
                ·
                  refine ⟨280624024090885201269967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1496661461818054406773157 280624024090885201269967)
                  ·
                    rfl

theorem cell21_1229655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 4].length) (baseStart_1229655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229655 prefixEnd_1229655 := by exact prefixLift 1229655
  have htrace : WordTrace (prefixWord ++ tailWord_1229655) baseStart_1229655 baseEnd_1229655 := by
    simpa [prefixWord, tailWord_1229655, baseEnd_1229655] using wordTrace_append hprefix tailTrace_1229655
  have hstable : (prefixWord ++ tailWord_1229655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229655).length < 2 ^ (prefixWord ++ tailWord_1229655).sum := by decide
  have hdescent : baseEnd_1229655 < baseStart_1229655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229680 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 8]
def baseStart_1229680 : Nat := 118140960795 + 1229680 * 2 ^ 59
def prefixEnd_1229680 : Nat := 4983230072969 + 3 ^ 40 * 1229680 * 2
def baseEnd_1229680 : Nat := 280629729431490713353249

theorem tailTrace_1229680 : CollatzResearch.WordTrace tailWord_1229680 prefixEnd_1229680 280629729431490713353249 := by
  unfold tailWord_1229680
  simp only [CollatzResearch.WordTrace]
  refine ⟨22425057092543423734575247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29900076123391231646100329 22425057092543423734575247)
  ·
    refine ⟨33637585638815135601862871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22425057092543423734575247 33637585638815135601862871)
    ·
      refine ⟨50456378458222703402794307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33637585638815135601862871 50456378458222703402794307)
      ·
        refine ⟨75684567687334055104191461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50456378458222703402794307 75684567687334055104191461)
        ·
          refine ⟨14190856441375135332035899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75684567687334055104191461 14190856441375135332035899)
          ·
            refine ⟨21286284662062702998053849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14190856441375135332035899 21286284662062702998053849)
            ·
              refine ⟨15964713496547027248540387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21286284662062702998053849 15964713496547027248540387)
              ·
                refine ⟨23947070244820540872810581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15964713496547027248540387 23947070244820540872810581)
                ·
                  refine ⟨280629729431490713353249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23947070244820540872810581 280629729431490713353249)
                  ·
                    rfl

theorem cell21_1229680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_1229680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229680 prefixEnd_1229680 := by exact prefixLift 1229680
  have htrace : WordTrace (prefixWord ++ tailWord_1229680) baseStart_1229680 baseEnd_1229680 := by
    simpa [prefixWord, tailWord_1229680, baseEnd_1229680] using wordTrace_append hprefix tailTrace_1229680
  have hstable : (prefixWord ++ tailWord_1229680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229680).length < 2 ^ (prefixWord ++ tailWord_1229680).sum := by decide
  have hdescent : baseEnd_1229680 < baseStart_1229680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229748 : List Nat := [2, 5, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1229748 : Nat := 118140960795 + 1229748 * 2 ^ 59
def prefixEnd_1229748 : Nat := 4983230072969 + 3 ^ 40 * 1229748 * 2
def baseEnd_1229748 : Nat := 280645247957937706219777

theorem tailTrace_1229748 : CollatzResearch.WordTrace tailWord_1229748 prefixEnd_1229748 280645247957937706219777 := by
  unfold tailWord_1229748
  simp only [CollatzResearch.WordTrace]
  refine ⟨22426297174420247541312949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29901729565893663388417265 22426297174420247541312949)
  ·
    refine ⟨2102465360101898206998089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22426297174420247541312949 2102465360101898206998089)
    ·
      refine ⟨1576849020076423655248567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2102465360101898206998089 1576849020076423655248567)
      ·
        refine ⟨2365273530114635482872851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1576849020076423655248567 2365273530114635482872851)
        ·
          refine ⟨3547910295171953224309277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2365273530114635482872851 3547910295171953224309277)
          ·
            refine ⟨1330466360689482459115979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3547910295171953224309277 1330466360689482459115979)
            ·
              refine ⟨1995699541034223688673969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330466360689482459115979 1995699541034223688673969)
              ·
                refine ⟨1496774655775667766505477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1995699541034223688673969 1496774655775667766505477)
                ·
                  refine ⟨280645247957937706219777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1496774655775667766505477 280645247957937706219777)
                  ·
                    rfl

theorem cell21_1229748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1229748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229748 prefixEnd_1229748 := by exact prefixLift 1229748
  have htrace : WordTrace (prefixWord ++ tailWord_1229748) baseStart_1229748 baseEnd_1229748 := by
    simpa [prefixWord, tailWord_1229748, baseEnd_1229748] using wordTrace_append hprefix tailTrace_1229748
  have hstable : (prefixWord ++ tailWord_1229748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229748).length < 2 ^ (prefixWord ++ tailWord_1229748).sum := by decide
  have hdescent : baseEnd_1229748 < baseStart_1229748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229810 : List Nat := [3, 2, 1, 5, 1, 1, 3, 2, 3]
def baseStart_1229810 : Nat := 118140960795 + 1229810 * 2 ^ 59
def prefixEnd_1229810 : Nat := 4983230072969 + 3 ^ 40 * 1229810 * 2
def baseEnd_1229810 : Nat := 280659397202639376186317

theorem tailTrace_1229810 : CollatzResearch.WordTrace tailWord_1229810 prefixEnd_1229810 280659397202639376186317 := by
  unfold tailWord_1229810
  simp only [CollatzResearch.WordTrace]
  refine ⟨11213713918653969917845721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29903237116410586447588589 11213713918653969917845721)
  ·
    refine ⟨8410285438990477438384291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11213713918653969917845721 8410285438990477438384291)
    ·
      refine ⟨12615428158485716157576437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8410285438990477438384291 12615428158485716157576437)
      ·
        refine ⟨1182696389858035889772791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12615428158485716157576437 1182696389858035889772791)
        ·
          refine ⟨1774044584787053834659187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182696389858035889772791 1774044584787053834659187)
          ·
            refine ⟨2661066877180580751988781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774044584787053834659187 2661066877180580751988781)
            ·
              refine ⟨997900078942717781995793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2661066877180580751988781 997900078942717781995793)
              ·
                refine ⟨748425059207038336496845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 997900078942717781995793 748425059207038336496845)
                ·
                  refine ⟨280659397202639376186317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748425059207038336496845 280659397202639376186317)
                  ·
                    rfl

theorem cell21_1229810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_1229810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229810 prefixEnd_1229810 := by exact prefixLift 1229810
  have htrace : WordTrace (prefixWord ++ tailWord_1229810) baseStart_1229810 baseEnd_1229810 := by
    simpa [prefixWord, tailWord_1229810, baseEnd_1229810] using wordTrace_append hprefix tailTrace_1229810
  have hstable : (prefixWord ++ tailWord_1229810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229810).length < 2 ^ (prefixWord ++ tailWord_1229810).sum := by decide
  have hdescent : baseEnd_1229810 < baseStart_1229810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229880 : List Nat := [2, 1, 2, 1, 5, 3, 1, 6]
def baseStart_1229880 : Nat := 118140960795 + 1229880 * 2 ^ 59
def prefixEnd_1229880 : Nat := 4983230072969 + 3 ^ 40 * 1229880 * 2
def baseEnd_1229880 : Nat := 93558457385444936673169

theorem tailTrace_1229880 : CollatzResearch.WordTrace tailWord_1229880 prefixEnd_1229880 93558457385444936673169 := by
  unfold tailWord_1229880
  simp only [CollatzResearch.WordTrace]
  refine ⟨22428704392181140813215547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29904939189574854417620729 22428704392181140813215547)
  ·
    refine ⟨33643056588271711219823321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22428704392181140813215547 33643056588271711219823321)
    ·
      refine ⟨25232292441203783414867491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33643056588271711219823321 25232292441203783414867491)
      ·
        refine ⟨37848438661805675122301237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25232292441203783414867491 37848438661805675122301237)
        ·
          refine ⟨3548291124544282042715741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37848438661805675122301237 3548291124544282042715741)
          ·
            refine ⟨1330609171704105766018403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3548291124544282042715741 1330609171704105766018403)
            ·
              refine ⟨1995913757556158649027605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330609171704105766018403 1995913757556158649027605)
              ·
                refine ⟨93558457385444936673169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1995913757556158649027605 93558457385444936673169)
                ·
                  rfl

theorem cell21_1229880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 6].length) (baseStart_1229880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229880 prefixEnd_1229880 := by exact prefixLift 1229880
  have htrace : WordTrace (prefixWord ++ tailWord_1229880) baseStart_1229880 baseEnd_1229880 := by
    simpa [prefixWord, tailWord_1229880, baseEnd_1229880] using wordTrace_append hprefix tailTrace_1229880
  have hstable : (prefixWord ++ tailWord_1229880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229880).length < 2 ^ (prefixWord ++ tailWord_1229880).sum := by decide
  have hdescent : baseEnd_1229880 < baseStart_1229880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229928 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 5]
def baseStart_1229928 : Nat := 118140960795 + 1229928 * 2 ^ 59
def prefixEnd_1229928 : Nat := 4983230072969 + 3 ^ 40 * 1229928 * 2
def baseEnd_1229928 : Nat := 280686326410297393219409

theorem tailTrace_1229928 : CollatzResearch.WordTrace tailWord_1229928 prefixEnd_1229928 280686326410297393219409 := by
  unfold tailWord_1229928
  simp only [CollatzResearch.WordTrace]
  refine ⟨22429579744094192912089219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29906106325458923882785625 22429579744094192912089219)
  ·
    refine ⟨33644369616141289368133829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22429579744094192912089219 33644369616141289368133829)
    ·
      refine ⟨6308319303026491756525093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33644369616141289368133829 6308319303026491756525093)
      ·
        refine ⟨1182809869317467204348455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6308319303026491756525093 1182809869317467204348455)
        ·
          refine ⟨1774214803976200806522683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182809869317467204348455 1774214803976200806522683)
          ·
            refine ⟨2661322205964301209784025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774214803976200806522683 2661322205964301209784025)
            ·
              refine ⟨1995991654473225907338019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2661322205964301209784025 1995991654473225907338019)
              ·
                refine ⟨2993987481709838861007029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995991654473225907338019 2993987481709838861007029)
                ·
                  refine ⟨280686326410297393219409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2993987481709838861007029 280686326410297393219409)
                  ·
                    rfl

theorem cell21_1229928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_1229928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229928 prefixEnd_1229928 := by exact prefixLift 1229928
  have htrace : WordTrace (prefixWord ++ tailWord_1229928) baseStart_1229928 baseEnd_1229928 := by
    simpa [prefixWord, tailWord_1229928, baseEnd_1229928] using wordTrace_append hprefix tailTrace_1229928
  have hstable : (prefixWord ++ tailWord_1229928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229928).length < 2 ^ (prefixWord ++ tailWord_1229928).sum := by decide
  have hdescent : baseEnd_1229928 < baseStart_1229928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229956 : List Nat := [2, 3, 2, 1, 2, 2, 4, 5]
def baseStart_1229956 : Nat := 118140960795 + 1229956 * 2 ^ 59
def prefixEnd_1229956 : Nat := 4983230072969 + 3 ^ 40 * 1229956 * 2
def baseEnd_1229956 : Nat := 93564238797258522250895

theorem tailTrace_1229956 : CollatzResearch.WordTrace tailWord_1229956 prefixEnd_1229956 93564238797258522250895 := by
  unfold tailWord_1229956
  simp only [CollatzResearch.WordTrace]
  refine ⟨22430090366043473303098861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29906787154724631070798481 22430090366043473303098861)
  ·
    refine ⟨8411283887266302488662073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22430090366043473303098861 8411283887266302488662073)
    ·
      refine ⟨6308462915449726866496555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8411283887266302488662073 6308462915449726866496555)
      ·
        refine ⟨9462694373174590299744833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6308462915449726866496555 9462694373174590299744833)
        ·
          refine ⟨7097020779880942724808625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9462694373174590299744833 7097020779880942724808625)
          ·
            refine ⟨5322765584910707043606469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7097020779880942724808625 5322765584910707043606469)
            ·
              refine ⟨998018547170757570676213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5322765584910707043606469 998018547170757570676213)
              ·
                refine ⟨93564238797258522250895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 998018547170757570676213 93564238797258522250895)
                ·
                  rfl

theorem cell21_1229956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 5].length) (baseStart_1229956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229956 prefixEnd_1229956 := by exact prefixLift 1229956
  have htrace : WordTrace (prefixWord ++ tailWord_1229956) baseStart_1229956 baseEnd_1229956 := by
    simpa [prefixWord, tailWord_1229956, baseEnd_1229956] using wordTrace_append hprefix tailTrace_1229956
  have hstable : (prefixWord ++ tailWord_1229956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229956).length < 2 ^ (prefixWord ++ tailWord_1229956).sum := by decide
  have hdescent : baseEnd_1229956 < baseStart_1229956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229984 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 6]
def baseStart_1229984 : Nat := 118140960795 + 1229984 * 2 ^ 59
def prefixEnd_1229984 : Nat := 4983230072969 + 3 ^ 40 * 1229984 * 2
def baseEnd_1229984 : Nat := 280699106373253740285961

theorem tailTrace_1229984 : CollatzResearch.WordTrace tailWord_1229984 prefixEnd_1229984 280699106373253740285961 := by
  unfold tailWord_1229984
  simp only [CollatzResearch.WordTrace]
  refine ⟨22430600987992753694108503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29907467983990338258811337 22430600987992753694108503)
  ·
    refine ⟨33645901481989130541162755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22430600987992753694108503 33645901481989130541162755)
    ·
      refine ⟨50468852222983695811744133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33645901481989130541162755 50468852222983695811744133)
      ·
        refine ⟨9462909791809442964702025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50468852222983695811744133 9462909791809442964702025)
        ·
          refine ⟨7097182343857082223526519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9462909791809442964702025 7097182343857082223526519)
          ·
            refine ⟨10645773515785623335289779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7097182343857082223526519 10645773515785623335289779)
            ·
              refine ⟨15968660273678435002934669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10645773515785623335289779 15968660273678435002934669)
              ·
                refine ⟨5988247602629413126100501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15968660273678435002934669 5988247602629413126100501)
                ·
                  refine ⟨280699106373253740285961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5988247602629413126100501 280699106373253740285961)
                  ·
                    rfl

theorem cell21_1229984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_1229984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1229984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1229984 prefixEnd_1229984 := by exact prefixLift 1229984
  have htrace : WordTrace (prefixWord ++ tailWord_1229984) baseStart_1229984 baseEnd_1229984 := by
    simpa [prefixWord, tailWord_1229984, baseEnd_1229984] using wordTrace_append hprefix tailTrace_1229984
  have hstable : (prefixWord ++ tailWord_1229984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229984).length < 2 ^ (prefixWord ++ tailWord_1229984).sum := by decide
  have hdescent : baseEnd_1229984 < baseStart_1229984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230094 : List Nat := [4, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_1230094 : Nat := 118140960795 + 1230094 * 2 ^ 59
def prefixEnd_1230094 : Nat := 4983230072969 + 3 ^ 40 * 1230094 * 2
def baseEnd_1230094 : Nat := 280724209871917993452403

theorem tailTrace_1230094 : CollatzResearch.WordTrace tailWord_1230094 prefixEnd_1230094 280724209871917993452403 := by
  unfold tailWord_1230094
  simp only [CollatzResearch.WordTrace]
  refine ⟨5608151750698374521840167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29910142670391330783147557 5608151750698374521840167)
  ·
    refine ⟨8412227626047561782760251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5608151750698374521840167 8412227626047561782760251)
    ·
      refine ⟨12618341439071342674140377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8412227626047561782760251 12618341439071342674140377)
      ·
        refine ⟨9463756079303507005605283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12618341439071342674140377 9463756079303507005605283)
        ·
          refine ⟨14195634118955260508407925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9463756079303507005605283 14195634118955260508407925)
          ·
            refine ⟨1330840698652055672663243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14195634118955260508407925 1330840698652055672663243)
            ·
              refine ⟨1996261047978083508994865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330840698652055672663243 1996261047978083508994865)
              ·
                refine ⟨1497195785983562631746149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1996261047978083508994865 1497195785983562631746149)
                ·
                  refine ⟨280724209871917993452403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1497195785983562631746149 280724209871917993452403)
                  ·
                    rfl

theorem cell21_1230094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_1230094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230094 prefixEnd_1230094 := by exact prefixLift 1230094
  have htrace : WordTrace (prefixWord ++ tailWord_1230094) baseStart_1230094 baseEnd_1230094 := by
    simpa [prefixWord, tailWord_1230094, baseEnd_1230094] using wordTrace_append hprefix tailTrace_1230094
  have hstable : (prefixWord ++ tailWord_1230094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230094).length < 2 ^ (prefixWord ++ tailWord_1230094).sum := by decide
  have hdescent : baseEnd_1230094 < baseStart_1230094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230125 : List Nat := [1, 5, 3, 1, 1, 1, 4, 5]
def baseStart_1230125 : Nat := 118140960795 + 1230125 * 2 ^ 59
def prefixEnd_1230125 : Nat := 4983230072969 + 3 ^ 40 * 1230125 * 2
def baseEnd_1230125 : Nat := 93577094831422942811891

theorem tailTrace_1230125 : CollatzResearch.WordTrace tailWord_1230125 prefixEnd_1230125 93577094831422942811891 := by
  unfold tailWord_1230125
  simp only [CollatzResearch.WordTrace]
  refine ⟨44866344668474688469099829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29910896445649792312733219 44866344668474688469099829)
  ·
    refine ⟨4206219812669502043978109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44866344668474688469099829 4206219812669502043978109)
    ·
      refine ⟨1577332429751063266491791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4206219812669502043978109 1577332429751063266491791)
      ·
        refine ⟨2365998644626594899737687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1577332429751063266491791 2365998644626594899737687)
        ·
          refine ⟨3548997966939892349606531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2365998644626594899737687 3548997966939892349606531)
          ·
            refine ⟨5323496950409838524409797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548997966939892349606531 5323496950409838524409797)
            ·
              refine ⟨998155678201844723326837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5323496950409838524409797 998155678201844723326837)
              ·
                refine ⟨93577094831422942811891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 998155678201844723326837 93577094831422942811891)
                ·
                  rfl

theorem cell21_1230125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 5].length) (baseStart_1230125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230125 prefixEnd_1230125 := by exact prefixLift 1230125
  have htrace : WordTrace (prefixWord ++ tailWord_1230125) baseStart_1230125 baseEnd_1230125 := by
    simpa [prefixWord, tailWord_1230125, baseEnd_1230125] using wordTrace_append hprefix tailTrace_1230125
  have hstable : (prefixWord ++ tailWord_1230125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230125).length < 2 ^ (prefixWord ++ tailWord_1230125).sum := by decide
  have hdescent : baseEnd_1230125 < baseStart_1230125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230156 : List Nat := [2, 2, 1, 3, 2, 3, 3, 2, 3]
def baseStart_1230156 : Nat := 118140960795 + 1230156 * 2 ^ 59
def prefixEnd_1230156 : Nat := 4983230072969 + 3 ^ 40 * 1230156 * 2
def baseEnd_1230156 : Nat := 280738359116619663418943

theorem tailTrace_1230156 : CollatzResearch.WordTrace tailWord_1230156 prefixEnd_1230156 280738359116619663418943 := by
  unfold tailWord_1230156
  simp only [CollatzResearch.WordTrace]
  refine ⟨22433737665681190381739161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29911650220908253842318881 22433737665681190381739161)
  ·
    refine ⟨16825303249260892786304371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22433737665681190381739161 16825303249260892786304371)
    ·
      refine ⟨25237954873891339179456557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16825303249260892786304371 25237954873891339179456557)
      ·
        refine ⟨9464233077709252192296209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25237954873891339179456557 9464233077709252192296209)
        ·
          refine ⟨7098174808281939144222157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9464233077709252192296209 7098174808281939144222157)
          ·
            refine ⟨2661815553105727179083309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7098174808281939144222157 2661815553105727179083309)
            ·
              refine ⟨998180832414647692156241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2661815553105727179083309 998180832414647692156241)
              ·
                refine ⟨748635624310985769117181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 998180832414647692156241 748635624310985769117181)
                ·
                  refine ⟨280738359116619663418943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748635624310985769117181 280738359116619663418943)
                  ·
                    rfl

theorem cell21_1230156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_1230156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230156 prefixEnd_1230156 := by exact prefixLift 1230156
  have htrace : WordTrace (prefixWord ++ tailWord_1230156) baseStart_1230156 baseEnd_1230156 := by
    simpa [prefixWord, tailWord_1230156, baseEnd_1230156] using wordTrace_append hprefix tailTrace_1230156
  have hstable : (prefixWord ++ tailWord_1230156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230156).length < 2 ^ (prefixWord ++ tailWord_1230156).sum := by decide
  have hdescent : baseEnd_1230156 < baseStart_1230156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230167 : List Nat := [1, 1, 3, 2, 3, 3, 2, 6]
def baseStart_1230167 : Nat := 118140960795 + 1230167 * 2 ^ 59
def prefixEnd_1230167 : Nat := 4983230072969 + 3 ^ 40 * 1230167 * 2
def baseEnd_1230167 : Nat := 93580289822162029578529

theorem tailTrace_1230167 : CollatzResearch.WordTrace tailWord_1230167 prefixEnd_1230167 93580289822162029578529 := by
  unfold tailWord_1230167
  simp only [CollatzResearch.WordTrace]
  refine ⟨44867876534322529642128755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29911917689548353094752503 44867876534322529642128755)
  ·
    refine ⟨67301814801483794463193133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44867876534322529642128755 67301814801483794463193133)
    ·
      refine ⟨25238180550556422923697425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67301814801483794463193133 25238180550556422923697425)
      ·
        refine ⟨18928635412917317192773069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25238180550556422923697425 18928635412917317192773069)
        ·
          refine ⟨7098238279843993947289901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18928635412917317192773069 7098238279843993947289901)
          ·
            refine ⟨2661839354941497730233713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7098238279843993947289901 2661839354941497730233713)
            ·
              refine ⟨1996379516206123297675285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2661839354941497730233713 1996379516206123297675285)
              ·
                refine ⟨93580289822162029578529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1996379516206123297675285 93580289822162029578529)
                ·
                  rfl

theorem cell21_1230167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 6].length) (baseStart_1230167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230167 prefixEnd_1230167 := by exact prefixLift 1230167
  have htrace : WordTrace (prefixWord ++ tailWord_1230167) baseStart_1230167 baseEnd_1230167 := by
    simpa [prefixWord, tailWord_1230167, baseEnd_1230167] using wordTrace_append hprefix tailTrace_1230167
  have hstable : (prefixWord ++ tailWord_1230167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230167).length < 2 ^ (prefixWord ++ tailWord_1230167).sum := by decide
  have hdescent : baseEnd_1230167 < baseStart_1230167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230181 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 7]
def baseStart_1230181 : Nat := 118140960795 + 1230181 * 2 ^ 59
def prefixEnd_1230181 : Nat := 4983230072969 + 3 ^ 40 * 1230181 * 2
def baseEnd_1230181 : Nat := 280744064457225175502225

theorem tailTrace_1230181 : CollatzResearch.WordTrace tailWord_1230181 prefixEnd_1230181 280744064457225175502225 := by
  unfold tailWord_1230181
  simp only [CollatzResearch.WordTrace]
  refine ⟨44868387156271810033138397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29912258104181206688758931 44868387156271810033138397)
  ·
    refine ⟨16825645183601928762426899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44868387156271810033138397 16825645183601928762426899)
    ·
      refine ⟨25238467775402893143640349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16825645183601928762426899 25238467775402893143640349)
      ·
        refine ⟨9464425415776084928865131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25238467775402893143640349 9464425415776084928865131)
        ·
          refine ⟨14196638123664127393297697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9464425415776084928865131 14196638123664127393297697)
          ·
            refine ⟨10647478592748095544973273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14196638123664127393297697 10647478592748095544973273)
            ·
              refine ⟨7985608944561071658729955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10647478592748095544973273 7985608944561071658729955)
              ·
                refine ⟨11978413416841607488094933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7985608944561071658729955 11978413416841607488094933)
                ·
                  refine ⟨280744064457225175502225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11978413416841607488094933 280744064457225175502225)
                  ·
                    rfl

theorem cell21_1230181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_1230181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230181 prefixEnd_1230181 := by exact prefixLift 1230181
  have htrace : WordTrace (prefixWord ++ tailWord_1230181) baseStart_1230181 baseEnd_1230181 := by
    simpa [prefixWord, tailWord_1230181, baseEnd_1230181] using wordTrace_append hprefix tailTrace_1230181
  have hstable : (prefixWord ++ tailWord_1230181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230181).length < 2 ^ (prefixWord ++ tailWord_1230181).sum := by decide
  have hdescent : baseEnd_1230181 < baseStart_1230181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230215 : List Nat := [1, 1, 4, 2, 2, 3, 1, 4, 3]
def baseStart_1230215 : Nat := 118140960795 + 1230215 * 2 ^ 59
def prefixEnd_1230215 : Nat := 4983230072969 + 3 ^ 40 * 1230215 * 2
def baseEnd_1230215 : Nat := 280751823720448671935489

theorem tailTrace_1230215 : CollatzResearch.WordTrace tailWord_1230215 prefixEnd_1230215 280751823720448671935489 := by
  unfold tailWord_1230215
  simp only [CollatzResearch.WordTrace]
  refine ⟨44869627238148633839876099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29913084825432422559917399 44869627238148633839876099)
  ·
    refine ⟨67304440857222950759814149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44869627238148633839876099 67304440857222950759814149)
    ·
      refine ⟨12619582660729303267465153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67304440857222950759814149 12619582660729303267465153)
      ·
        refine ⟨9464686995546977450598865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12619582660729303267465153 9464686995546977450598865)
        ·
          refine ⟨7098515246660233087949149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9464686995546977450598865 7098515246660233087949149)
          ·
            refine ⟨2661943217497587407980931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7098515246660233087949149 2661943217497587407980931)
            ·
              refine ⟨3992914826246381111971397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2661943217497587407980931 3992914826246381111971397)
              ·
                refine ⟨748671529921196458494637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3992914826246381111971397 748671529921196458494637)
                ·
                  refine ⟨280751823720448671935489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748671529921196458494637 280751823720448671935489)
                  ·
                    rfl

theorem cell21_1230215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 3].length) (baseStart_1230215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230215 prefixEnd_1230215 := by exact prefixLift 1230215
  have htrace : WordTrace (prefixWord ++ tailWord_1230215) baseStart_1230215 baseEnd_1230215 := by
    simpa [prefixWord, tailWord_1230215, baseEnd_1230215] using wordTrace_append hprefix tailTrace_1230215
  have hstable : (prefixWord ++ tailWord_1230215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230215).length < 2 ^ (prefixWord ++ tailWord_1230215).sum := by decide
  have hdescent : baseEnd_1230215 < baseStart_1230215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230243 : List Nat := [1, 1, 1, 4, 1, 3, 5, 5]
def baseStart_1230243 : Nat := 118140960795 + 1230243 * 2 ^ 59
def prefixEnd_1230243 : Nat := 4983230072969 + 3 ^ 40 * 1230243 * 2
def baseEnd_1230243 : Nat := 93586071233975615156255

theorem tailTrace_1230243 : CollatzResearch.WordTrace tailWord_1230243 prefixEnd_1230243 93586071233975615156255 := by
  unfold tailWord_1230243
  simp only [CollatzResearch.WordTrace]
  refine ⟨44870648482047194621895383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29913765654698129747930255 44870648482047194621895383)
  ·
    refine ⟨67305972723070791932843075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44870648482047194621895383 67305972723070791932843075)
    ·
      refine ⟨100958959084606187899264613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67305972723070791932843075 100958959084606187899264613)
      ·
        refine ⟨18929804828363660231112115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100958959084606187899264613 18929804828363660231112115)
        ·
          refine ⟨28394707242545490346668173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18929804828363660231112115 28394707242545490346668173)
          ·
            refine ⟨10648015215954558880000565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28394707242545490346668173 10648015215954558880000565)
            ·
              refine ⟨998251426495739895000053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10648015215954558880000565 998251426495739895000053)
              ·
                refine ⟨93586071233975615156255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 998251426495739895000053 93586071233975615156255)
                ·
                  rfl

theorem cell21_1230243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 5].length) (baseStart_1230243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230243 prefixEnd_1230243 := by exact prefixLift 1230243
  have htrace : WordTrace (prefixWord ++ tailWord_1230243) baseStart_1230243 baseEnd_1230243 := by
    simpa [prefixWord, tailWord_1230243, baseEnd_1230243] using wordTrace_append hprefix tailTrace_1230243
  have hstable : (prefixWord ++ tailWord_1230243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230243).length < 2 ^ (prefixWord ++ tailWord_1230243).sum := by decide
  have hdescent : baseEnd_1230243 < baseStart_1230243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230257 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 7]
def baseStart_1230257 : Nat := 118140960795 + 1230257 * 2 ^ 59
def prefixEnd_1230257 : Nat := 4983230072969 + 3 ^ 40 * 1230257 * 2
def baseEnd_1230257 : Nat := 280761408692665932235403

theorem tailTrace_1230257 : CollatzResearch.WordTrace tailWord_1230257 prefixEnd_1230257 280761408692665932235403 := by
  unfold tailWord_1230257
  simp only [CollatzResearch.WordTrace]
  refine ⟨44871159103996475012905025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29914106069330983341936683 44871159103996475012905025)
  ·
    refine ⟨33653369327997356259678769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44871159103996475012905025 33653369327997356259678769)
    ·
      refine ⟨25240026995998017194759077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33653369327997356259678769 25240026995998017194759077)
      ·
        refine ⟨4732505061749628224017327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25240026995998017194759077 4732505061749628224017327)
        ·
          refine ⟨7098757592624442336025991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4732505061749628224017327 7098757592624442336025991)
          ·
            refine ⟨10648136388936663504038987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7098757592624442336025991 10648136388936663504038987)
            ·
              refine ⟨15972204583404995256058481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10648136388936663504038987 15972204583404995256058481)
              ·
                refine ⟨11979153437553746442043861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15972204583404995256058481 11979153437553746442043861)
                ·
                  refine ⟨280761408692665932235403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11979153437553746442043861 280761408692665932235403)
                  ·
                    rfl

theorem cell21_1230257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_1230257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230257 prefixEnd_1230257 := by exact prefixLift 1230257
  have htrace : WordTrace (prefixWord ++ tailWord_1230257) baseStart_1230257 baseEnd_1230257 := by
    simpa [prefixWord, tailWord_1230257, baseEnd_1230257] using wordTrace_append hprefix tailTrace_1230257
  have hstable : (prefixWord ++ tailWord_1230257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230257).length < 2 ^ (prefixWord ++ tailWord_1230257).sum := by decide
  have hdescent : baseEnd_1230257 < baseStart_1230257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230325 : List Nat := [1, 3, 5, 1, 1, 2, 3, 2, 3]
def baseStart_1230325 : Nat := 118140960795 + 1230325 * 2 ^ 59
def prefixEnd_1230325 : Nat := 4983230072969 + 3 ^ 40 * 1230325 * 2
def baseEnd_1230325 : Nat := 280776927219112925101931

theorem tailTrace_1230325 : CollatzResearch.WordTrace tailWord_1230325 prefixEnd_1230325 280776927219112925101931 := by
  unfold tailWord_1230325
  simp only [CollatzResearch.WordTrace]
  refine ⟨44873639267750122626380429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29915759511833415084253619 44873639267750122626380429)
  ·
    refine ⟨16827614725406295984892661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44873639267750122626380429 16827614725406295984892661)
    ·
      refine ⟨1577588880506840248583687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16827614725406295984892661 1577588880506840248583687)
      ·
        refine ⟨2366383320760260372875531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1577588880506840248583687 2366383320760260372875531)
        ·
          refine ⟨3549574981140390559313297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2366383320760260372875531 3549574981140390559313297)
          ·
            refine ⟨2662181235855292919484973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3549574981140390559313297 2662181235855292919484973)
            ·
              refine ⟨998317963445734844806865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2662181235855292919484973 998317963445734844806865)
              ·
                refine ⟨748738472584301133605149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 998317963445734844806865 748738472584301133605149)
                ·
                  refine ⟨280776927219112925101931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748738472584301133605149 280776927219112925101931)
                  ·
                    rfl

theorem cell21_1230325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_1230325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230325 prefixEnd_1230325 := by exact prefixLift 1230325
  have htrace : WordTrace (prefixWord ++ tailWord_1230325) baseStart_1230325 baseEnd_1230325 := by
    simpa [prefixWord, tailWord_1230325, baseEnd_1230325] using wordTrace_append hprefix tailTrace_1230325
  have hstable : (prefixWord ++ tailWord_1230325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230325).length < 2 ^ (prefixWord ++ tailWord_1230325).sum := by decide
  have hdescent : baseEnd_1230325 < baseStart_1230325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230457 : List Nat := [1, 2, 1, 3, 3, 1, 5, 1, 4]
def baseStart_1230457 : Nat := 118140960795 + 1230457 * 2 ^ 59
def prefixEnd_1230457 : Nat := 4983230072969 + 3 ^ 40 * 1230457 * 2
def baseEnd_1230457 : Nat := 280807051417510028901661

theorem tailTrace_1230457 : CollatzResearch.WordTrace tailWord_1230457 prefixEnd_1230457 280807051417510028901661 := by
  unfold tailWord_1230457
  simp only [CollatzResearch.WordTrace]
  refine ⟨44878453703271909170185625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29918969135514606113457083 44878453703271909170185625)
  ·
    refine ⟨33658840277453931877639219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44878453703271909170185625 33658840277453931877639219)
    ·
      refine ⟨50488260416180897816458829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33658840277453931877639219 50488260416180897816458829)
      ·
        refine ⟨18933097656067836681172061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50488260416180897816458829 18933097656067836681172061)
        ·
          refine ⟨7099911621025438755439523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18933097656067836681172061 7099911621025438755439523)
          ·
            refine ⟨10649867431538158133159285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7099911621025438755439523 10649867431538158133159285)
            ·
              refine ⟨998425071706702324983683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10649867431538158133159285 998425071706702324983683)
              ·
                refine ⟨1497637607560053487475525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998425071706702324983683 1497637607560053487475525)
                ·
                  refine ⟨280807051417510028901661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1497637607560053487475525 280807051417510028901661)
                  ·
                    rfl

theorem cell21_1230457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 4].length) (baseStart_1230457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230457 prefixEnd_1230457 := by exact prefixLift 1230457
  have htrace : WordTrace (prefixWord ++ tailWord_1230457) baseStart_1230457 baseEnd_1230457 := by
    simpa [prefixWord, tailWord_1230457, baseEnd_1230457] using wordTrace_append hprefix tailTrace_1230457
  have hstable : (prefixWord ++ tailWord_1230457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230457).length < 2 ^ (prefixWord ++ tailWord_1230457).sum := by decide
  have hdescent : baseEnd_1230457 < baseStart_1230457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230471 : List Nat := [1, 1, 4, 2, 1, 3, 4, 5]
def baseStart_1230471 : Nat := 118140960795 + 1230471 * 2 ^ 59
def prefixEnd_1230471 : Nat := 4983230072969 + 3 ^ 40 * 1230471 * 2
def baseEnd_1230471 : Nat := 93603415469416371889433

theorem tailTrace_1230471 : CollatzResearch.WordTrace tailWord_1230471 prefixEnd_1230471 93603415469416371889433 := by
  unfold tailWord_1230471
  simp only [CollatzResearch.WordTrace]
  refine ⟨44878964325221189561195267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29919309550147459707463511 44878964325221189561195267)
  ·
    refine ⟨67318446487831784341792901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44878964325221189561195267 67318446487831784341792901)
    ·
      refine ⟨12622208716468459564086169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67318446487831784341792901 12622208716468459564086169)
      ·
        refine ⟨9466656537351344673064627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12622208716468459564086169 9466656537351344673064627)
        ·
          refine ⟨14199984806027017009596941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9466656537351344673064627 14199984806027017009596941)
          ·
            refine ⟨5324994302260131378598853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14199984806027017009596941 5324994302260131378598853)
            ·
              refine ⟨998436431673774633487285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5324994302260131378598853 998436431673774633487285)
              ·
                refine ⟨93603415469416371889433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 998436431673774633487285 93603415469416371889433)
                ·
                  rfl

theorem cell21_1230471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 5].length) (baseStart_1230471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230471 prefixEnd_1230471 := by exact prefixLift 1230471
  have htrace : WordTrace (prefixWord ++ tailWord_1230471) baseStart_1230471 baseEnd_1230471 := by
    simpa [prefixWord, tailWord_1230471, baseEnd_1230471] using wordTrace_append hprefix tailTrace_1230471
  have hstable : (prefixWord ++ tailWord_1230471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230471).length < 2 ^ (prefixWord ++ tailWord_1230471).sum := by decide
  have hdescent : baseEnd_1230471 < baseStart_1230471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230499 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 6]
def baseStart_1230499 : Nat := 118140960795 + 1230499 * 2 ^ 59
def prefixEnd_1230499 : Nat := 4983230072969 + 3 ^ 40 * 1230499 * 2
def baseEnd_1230499 : Nat := 280816636389727289201575

theorem tailTrace_1230499 : CollatzResearch.WordTrace tailWord_1230499 prefixEnd_1230499 280816636389727289201575 := by
  unfold tailWord_1230499
  simp only [CollatzResearch.WordTrace]
  refine ⟨44879985569119750343214551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29919990379413166895476367 44879985569119750343214551)
  ·
    refine ⟨67319978353679625514821827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44879985569119750343214551 67319978353679625514821827)
    ·
      refine ⟨100979967530519438272232741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67319978353679625514821827 100979967530519438272232741)
      ·
        refine ⟨18933743911972394676043639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100979967530519438272232741 18933743911972394676043639)
        ·
          refine ⟨28400615867958592014065459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18933743911972394676043639 28400615867958592014065459)
          ·
            refine ⟨42600923801937888021098189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28400615867958592014065459 42600923801937888021098189)
            ·
              refine ⟨15975346425726708007911821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42600923801937888021098189 15975346425726708007911821)
              ·
                refine ⟨5990754909647515502966933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15975346425726708007911821 5990754909647515502966933)
                ·
                  refine ⟨280816636389727289201575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5990754909647515502966933 280816636389727289201575)
                  ·
                    rfl

theorem cell21_1230499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 6].length) (baseStart_1230499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230499 prefixEnd_1230499 := by exact prefixLift 1230499
  have htrace : WordTrace (prefixWord ++ tailWord_1230499) baseStart_1230499 baseEnd_1230499 := by
    simpa [prefixWord, tailWord_1230499, baseEnd_1230499] using wordTrace_append hprefix tailTrace_1230499
  have hstable : (prefixWord ++ tailWord_1230499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230499).length < 2 ^ (prefixWord ++ tailWord_1230499).sum := by decide
  have hdescent : baseEnd_1230499 < baseStart_1230499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230544 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 9]
def baseStart_1230544 : Nat := 118140960795 + 1230544 * 2 ^ 59
def prefixEnd_1230544 : Nat := 4983230072969 + 3 ^ 40 * 1230544 * 2
def baseEnd_1230544 : Nat := 280826906002817210951483

theorem tailTrace_1230544 : CollatzResearch.WordTrace tailWord_1230544 prefixEnd_1230544 280826906002817210951483 := by
  unfold tailWord_1230544
  simp only [CollatzResearch.WordTrace]
  refine ⟨22440813426978361514301343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29921084569304482019068457 22440813426978361514301343)
  ·
    refine ⟨33661220140467542271452015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22440813426978361514301343 33661220140467542271452015)
    ·
      refine ⟨50491830210701313407178023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33661220140467542271452015 50491830210701313407178023)
      ·
        refine ⟨75737745316051970110767035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50491830210701313407178023 75737745316051970110767035)
        ·
          refine ⟨113606617974077955166150553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75737745316051970110767035 113606617974077955166150553)
          ·
            refine ⟨85204963480558466374612915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113606617974077955166150553 85204963480558466374612915)
            ·
              refine ⟨127807445220837699561919373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85204963480558466374612915 127807445220837699561919373)
              ·
                refine ⟨47927791957814137335719765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127807445220837699561919373 47927791957814137335719765)
                ·
                  refine ⟨280826906002817210951483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47927791957814137335719765 280826906002817210951483)
                  ·
                    rfl

theorem cell21_1230544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_1230544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230544 prefixEnd_1230544 := by exact prefixLift 1230544
  have htrace : WordTrace (prefixWord ++ tailWord_1230544) baseStart_1230544 baseEnd_1230544 := by
    simpa [prefixWord, tailWord_1230544, baseEnd_1230544] using wordTrace_append hprefix tailTrace_1230544
  have hstable : (prefixWord ++ tailWord_1230544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230544).length < 2 ^ (prefixWord ++ tailWord_1230544).sum := by decide
  have hdescent : baseEnd_1230544 < baseStart_1230544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230682 : List Nat := [3, 1, 1, 2, 1, 3, 4, 6]
def baseStart_1230682 : Nat := 118140960795 + 1230682 * 2 ^ 59
def prefixEnd_1230682 : Nat := 4983230072969 + 3 ^ 40 * 1230682 * 2
def baseEnd_1230682 : Nat := 93619466494319879217067

theorem tailTrace_1230682 : CollatzResearch.WordTrace tailWord_1230682 prefixEnd_1230682 93619466494319879217067 := by
  unfold tailWord_1230682
  simp only [CollatzResearch.WordTrace]
  refine ⟨11221665031864193149281575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29924440084971181731417533 11221665031864193149281575)
  ·
    refine ⟨16832497547796289723922363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11221665031864193149281575 16832497547796289723922363)
    ·
      refine ⟨25248746321694434585883545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16832497547796289723922363 25248746321694434585883545)
      ·
        refine ⟨18936559741270825939412659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25248746321694434585883545 18936559741270825939412659)
        ·
          refine ⟨28404839611906238909118989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18936559741270825939412659 28404839611906238909118989)
          ·
            refine ⟨10651814854464839590919621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28404839611906238909118989 10651814854464839590919621)
            ·
              refine ⟨1997215285212157423297429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10651814854464839590919621 1997215285212157423297429)
              ·
                refine ⟨93619466494319879217067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1997215285212157423297429 93619466494319879217067)
                ·
                  rfl

theorem cell21_1230682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_1230682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230682 prefixEnd_1230682 := by exact prefixLift 1230682
  have htrace : WordTrace (prefixWord ++ tailWord_1230682) baseStart_1230682 baseEnd_1230682 := by
    simpa [prefixWord, tailWord_1230682, baseEnd_1230682] using wordTrace_append hprefix tailTrace_1230682
  have hstable : (prefixWord ++ tailWord_1230682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230682).length < 2 ^ (prefixWord ++ tailWord_1230682).sum := by decide
  have hdescent : baseEnd_1230682 < baseStart_1230682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230848 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 5]
def baseStart_1230848 : Nat := 118140960795 + 1230848 * 2 ^ 59
def prefixEnd_1230848 : Nat := 4983230072969 + 3 ^ 40 * 1230848 * 2
def baseEnd_1230848 : Nat := 280896282944580237884195

theorem tailTrace_1230848 : CollatzResearch.WordTrace tailWord_1230848 prefixEnd_1230848 280896282944580237884195 := by
  unfold tailWord_1230848
  simp only [CollatzResearch.WordTrace]
  refine ⟨22446357322427691473834599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29928476429903588631779465 22446357322427691473834599)
  ·
    refine ⟨33669535983641537210751899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22446357322427691473834599 33669535983641537210751899)
    ·
      refine ⟨50504303975462305816127849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33669535983641537210751899 50504303975462305816127849)
      ·
        refine ⟨37878227981596729362095887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50504303975462305816127849 37878227981596729362095887)
        ·
          refine ⟨56817341972395094043143831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37878227981596729362095887 56817341972395094043143831)
          ·
            refine ⟨85226012958592641064715747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56817341972395094043143831 85226012958592641064715747)
            ·
              refine ⟨127839019437888961597073621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85226012958592641064715747 127839019437888961597073621)
              ·
                refine ⟨2996227018075522537431413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 127839019437888961597073621 2996227018075522537431413)
                ·
                  refine ⟨280896282944580237884195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2996227018075522537431413 280896282944580237884195)
                  ·
                    rfl

theorem cell21_1230848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_1230848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230848 prefixEnd_1230848 := by exact prefixLift 1230848
  have htrace : WordTrace (prefixWord ++ tailWord_1230848) baseStart_1230848 baseEnd_1230848 := by
    simpa [prefixWord, tailWord_1230848, baseEnd_1230848] using wordTrace_append hprefix tailTrace_1230848
  have hstable : (prefixWord ++ tailWord_1230848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230848).length < 2 ^ (prefixWord ++ tailWord_1230848).sum := by decide
  have hdescent : baseEnd_1230848 < baseStart_1230848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230882 : List Nat := [3, 3, 1, 1, 1, 2, 2, 5, 3]
def baseStart_1230882 : Nat := 118140960795 + 1230882 * 2 ^ 59
def prefixEnd_1230882 : Nat := 4983230072969 + 3 ^ 40 * 1230882 * 2
def baseEnd_1230882 : Nat := 280904042207803734317459

theorem tailTrace_1230882 : CollatzResearch.WordTrace tailWord_1230882 prefixEnd_1230882 280904042207803734317459 := by
  unfold tailWord_1230882
  simp only [CollatzResearch.WordTrace]
  refine ⟨11223488681683051688601725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29929303151154804502937933 11223488681683051688601725)
  ·
    refine ⟨4208808255631144383225647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11223488681683051688601725 4208808255631144383225647)
    ·
      refine ⟨6313212383446716574838471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4208808255631144383225647 6313212383446716574838471)
      ·
        refine ⟨9469818575170074862257707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6313212383446716574838471 9469818575170074862257707)
        ·
          refine ⟨14204727862755112293386561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9469818575170074862257707 14204727862755112293386561)
          ·
            refine ⟨10653545897066334220039921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14204727862755112293386561 10653545897066334220039921)
            ·
              refine ⟨7990159422799750665029941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10653545897066334220039921 7990159422799750665029941)
              ·
                refine ⟨749077445887476624846557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7990159422799750665029941 749077445887476624846557)
                ·
                  refine ⟨280904042207803734317459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 749077445887476624846557 280904042207803734317459)
                  ·
                    rfl

theorem cell21_1230882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_1230882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230882 prefixEnd_1230882 := by exact prefixLift 1230882
  have htrace : WordTrace (prefixWord ++ tailWord_1230882) baseStart_1230882 baseEnd_1230882 := by
    simpa [prefixWord, tailWord_1230882, baseEnd_1230882] using wordTrace_append hprefix tailTrace_1230882
  have hstable : (prefixWord ++ tailWord_1230882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230882).length < 2 ^ (prefixWord ++ tailWord_1230882).sum := by decide
  have hdescent : baseEnd_1230882 < baseStart_1230882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230893 : List Nat := [1, 5, 15]
def baseStart_1230893 : Nat := 118140960795 + 1230893 * 2 ^ 59
def prefixEnd_1230893 : Nat := 4983230072969 + 3 ^ 40 * 1230893 * 2
def baseEnd_1230893 : Nat := 385331347815734101007

theorem tailTrace_1230893 : CollatzResearch.WordTrace tailWord_1230893 prefixEnd_1230893 385331347815734101007 := by
  unfold tailWord_1230893
  simp only [CollatzResearch.WordTrace]
  refine ⟨44894355929692355633057333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29929570619794903755371555 44894355929692355633057333)
  ·
    refine ⟨4208845868408658340599125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44894355929692355633057333 4208845868408658340599125)
    ·
      refine ⟨385331347815734101007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 4208845868408658340599125 385331347815734101007)
      ·
        rfl

theorem cell21_1230893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 15].length) (baseStart_1230893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230893 prefixEnd_1230893 := by exact prefixLift 1230893
  have htrace : WordTrace (prefixWord ++ tailWord_1230893) baseStart_1230893 baseEnd_1230893 := by
    simpa [prefixWord, tailWord_1230893, baseEnd_1230893] using wordTrace_append hprefix tailTrace_1230893
  have hstable : (prefixWord ++ tailWord_1230893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230893).length < 2 ^ (prefixWord ++ tailWord_1230893).sum := by decide
  have hdescent : baseEnd_1230893 < baseStart_1230893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230896 : List Nat := [2, 1, 1, 1, 2, 6, 2, 2, 4]
def baseStart_1230896 : Nat := 118140960795 + 1230896 * 2 ^ 59
def prefixEnd_1230896 : Nat := 4983230072969 + 3 ^ 40 * 1230896 * 2
def baseEnd_1230896 : Nat := 280907237198542821084097

theorem tailTrace_1230896 : CollatzResearch.WordTrace tailWord_1230896 prefixEnd_1230896 280907237198542821084097 := by
  unfold tailWord_1230896
  simp only [CollatzResearch.WordTrace]
  refine ⟨22447232674340743572708271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29929643565787658096944361 22447232674340743572708271)
  ·
    refine ⟨33670849011511115359062407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22447232674340743572708271 33670849011511115359062407)
    ·
      refine ⟨50506273517266673038593611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33670849011511115359062407 50506273517266673038593611)
      ·
        refine ⟨75759410275900009557890417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50506273517266673038593611 75759410275900009557890417)
        ·
          refine ⟨56819557706925007168417813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75759410275900009557890417 56819557706925007168417813)
          ·
            refine ⟨2663416767512109711019585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56819557706925007168417813 2663416767512109711019585)
            ·
              refine ⟨1997562575634082283264689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2663416767512109711019585 1997562575634082283264689)
              ·
                refine ⟨1498171931725561712448517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1997562575634082283264689 1498171931725561712448517)
                ·
                  refine ⟨280907237198542821084097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1498171931725561712448517 280907237198542821084097)
                  ·
                    rfl

theorem cell21_1230896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_1230896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230896 prefixEnd_1230896 := by exact prefixLift 1230896
  have htrace : WordTrace (prefixWord ++ tailWord_1230896) baseStart_1230896 baseEnd_1230896 := by
    simpa [prefixWord, tailWord_1230896, baseEnd_1230896] using wordTrace_append hprefix tailTrace_1230896
  have hstable : (prefixWord ++ tailWord_1230896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230896).length < 2 ^ (prefixWord ++ tailWord_1230896).sum := by decide
  have hdescent : baseEnd_1230896 < baseStart_1230896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230924 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 7]
def baseStart_1230924 : Nat := 118140960795 + 1230924 * 2 ^ 59
def prefixEnd_1230924 : Nat := 4983230072969 + 3 ^ 40 * 1230924 * 2
def baseEnd_1230924 : Nat := 280913627180020994617373

theorem tailTrace_1230924 : CollatzResearch.WordTrace tailWord_1230924 prefixEnd_1230924 280913627180020994617373 := by
  unfold tailWord_1230924
  simp only [CollatzResearch.WordTrace]
  refine ⟨22447743296290023963717913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29930324395053365284957217 22447743296290023963717913)
  ·
    refine ⟨16835807472217517972788435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22447743296290023963717913 16835807472217517972788435)
    ·
      refine ⟨25253711208326276959182653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16835807472217517972788435 25253711208326276959182653)
      ·
        refine ⟨9470141703122353859693495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25253711208326276959182653 9470141703122353859693495)
        ·
          refine ⟨14205212554683530789540243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9470141703122353859693495 14205212554683530789540243)
          ·
            refine ⟨21307818832025296184310365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14205212554683530789540243 21307818832025296184310365)
            ·
              refine ⟨7990432062009486069116387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21307818832025296184310365 7990432062009486069116387)
              ·
                refine ⟨11985648093014229103674581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7990432062009486069116387 11985648093014229103674581)
                ·
                  refine ⟨280913627180020994617373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11985648093014229103674581 280913627180020994617373)
                  ·
                    rfl

theorem cell21_1230924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_1230924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230924 prefixEnd_1230924 := by exact prefixLift 1230924
  have htrace : WordTrace (prefixWord ++ tailWord_1230924) baseStart_1230924 baseEnd_1230924 := by
    simpa [prefixWord, tailWord_1230924, baseEnd_1230924] using wordTrace_append hprefix tailTrace_1230924
  have hstable : (prefixWord ++ tailWord_1230924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230924).length < 2 ^ (prefixWord ++ tailWord_1230924).sum := by decide
  have hdescent : baseEnd_1230924 < baseStart_1230924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230958 : List Nat := [4, 1, 2, 2, 1, 1, 1, 6, 3]
def baseStart_1230958 : Nat := 118140960795 + 1230958 * 2 ^ 59
def prefixEnd_1230958 : Nat := 4983230072969 + 3 ^ 40 * 1230958 * 2
def baseEnd_1230958 : Nat := 280921386443244491050637

theorem tailTrace_1230958 : CollatzResearch.WordTrace tailWord_1230958 prefixEnd_1230958 280921386443244491050637 := by
  unfold tailWord_1230958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5612090834307108966771691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29931151116304581156115685 5612090834307108966771691)
  ·
    refine ⟨8418136251460663450157537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5612090834307108966771691 8418136251460663450157537)
    ·
      refine ⟨6313602188595497587618153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8418136251460663450157537 6313602188595497587618153)
      ·
        refine ⟨4735201641446623190713615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6313602188595497587618153 4735201641446623190713615)
        ·
          refine ⟨7102802462169934786070423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4735201641446623190713615 7102802462169934786070423)
          ·
            refine ⟨10654203693254902179105635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7102802462169934786070423 10654203693254902179105635)
            ·
              refine ⟨15981305539882353268658453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10654203693254902179105635 15981305539882353268658453)
              ·
                refine ⟨749123697181985309468365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15981305539882353268658453 749123697181985309468365)
                ·
                  refine ⟨280921386443244491050637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 749123697181985309468365 280921386443244491050637)
                  ·
                    rfl

theorem cell21_1230958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_1230958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230958 prefixEnd_1230958 := by exact prefixLift 1230958
  have htrace : WordTrace (prefixWord ++ tailWord_1230958) baseStart_1230958 baseEnd_1230958 := by
    simpa [prefixWord, tailWord_1230958, baseEnd_1230958] using wordTrace_append hprefix tailTrace_1230958
  have hstable : (prefixWord ++ tailWord_1230958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230958).length < 2 ^ (prefixWord ++ tailWord_1230958).sum := by decide
  have hdescent : baseEnd_1230958 < baseStart_1230958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230986 : List Nat := [3, 1, 2, 3, 1, 3, 1, 7]
def baseStart_1230986 : Nat := 118140960795 + 1230986 * 2 ^ 59
def prefixEnd_1230986 : Nat := 4983230072969 + 3 ^ 40 * 1230986 * 2
def baseEnd_1230986 : Nat := 93642592141574221527971

theorem tailTrace_1230986 : CollatzResearch.WordTrace tailWord_1230986 prefixEnd_1230986 93642592141574221527971 := by
  unfold tailWord_1230986
  simp only [CollatzResearch.WordTrace]
  refine ⟨11224436979588858129048203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29931831945570288344128541 11224436979588858129048203)
  ·
    refine ⟨16836655469383287193572305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11224436979588858129048203 16836655469383287193572305)
    ·
      refine ⟨12627491602037465395179229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16836655469383287193572305 12627491602037465395179229)
      ·
        refine ⟨4735309350764049523192211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12627491602037465395179229 4735309350764049523192211)
        ·
          refine ⟨7102964026146074284788317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4735309350764049523192211 7102964026146074284788317)
          ·
            refine ⟨2663611509804777856795619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7102964026146074284788317 2663611509804777856795619)
            ·
              refine ⟨3995417264707166785193429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2663611509804777856795619 3995417264707166785193429)
              ·
                refine ⟨93642592141574221527971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3995417264707166785193429 93642592141574221527971)
                ·
                  rfl

theorem cell21_1230986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_1230986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1230986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1230986 prefixEnd_1230986 := by exact prefixLift 1230986
  have htrace : WordTrace (prefixWord ++ tailWord_1230986) baseStart_1230986 baseEnd_1230986 := by
    simpa [prefixWord, tailWord_1230986, baseEnd_1230986] using wordTrace_append hprefix tailTrace_1230986
  have hstable : (prefixWord ++ tailWord_1230986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230986).length < 2 ^ (prefixWord ++ tailWord_1230986).sum := by decide
  have hdescent : baseEnd_1230986 < baseStart_1230986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231045 : List Nat := [1, 3, 1, 1, 1, 1, 6, 7]
def baseStart_1231045 : Nat := 118140960795 + 1231045 * 2 ^ 59
def prefixEnd_1231045 : Nat := 4983230072969 + 3 ^ 40 * 1231045 * 2
def baseEnd_1231045 : Nat := 93647080342850557700153

theorem tailTrace_1231045 : CollatzResearch.WordTrace tailWord_1231045 prefixEnd_1231045 93647080342850557700153 := by
  unfold tailWord_1231045
  simp only [CollatzResearch.WordTrace]
  refine ⟨44899899825141685592590589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29933266550094457061727059 44899899825141685592590589)
  ·
    refine ⟨16837462434428132097221471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44899899825141685592590589 16837462434428132097221471)
    ·
      refine ⟨25256193651642198145832207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16837462434428132097221471 25256193651642198145832207)
      ·
        refine ⟨37884290477463297218748311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25256193651642198145832207 37884290477463297218748311)
        ·
          refine ⟨56826435716194945828122467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37884290477463297218748311 56826435716194945828122467)
          ·
            refine ⟨85239653574292418742183701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56826435716194945828122467 85239653574292418742183701)
            ·
              refine ⟨3995608761294957128539861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85239653574292418742183701 3995608761294957128539861)
              ·
                refine ⟨93647080342850557700153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3995608761294957128539861 93647080342850557700153)
                ·
                  rfl

theorem cell21_1231045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 7].length) (baseStart_1231045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231045 prefixEnd_1231045 := by exact prefixLift 1231045
  have htrace : WordTrace (prefixWord ++ tailWord_1231045) baseStart_1231045 baseEnd_1231045 := by
    simpa [prefixWord, tailWord_1231045, baseEnd_1231045] using wordTrace_append hprefix tailTrace_1231045
  have hstable : (prefixWord ++ tailWord_1231045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231045).length < 2 ^ (prefixWord ++ tailWord_1231045).sum := by decide
  have hdescent : baseEnd_1231045 < baseStart_1231045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231068 : List Nat := [2, 2, 5, 2, 1, 1, 1, 4, 3]
def baseStart_1231068 : Nat := 118140960795 + 1231068 * 2 ^ 59
def prefixEnd_1231068 : Nat := 4983230072969 + 3 ^ 40 * 1231068 * 2
def baseEnd_1231068 : Nat := 280946489941908744217079

theorem tailTrace_1231068 : CollatzResearch.WordTrace tailWord_1231068 prefixEnd_1231068 280946489941908744217079 := by
  unfold tailWord_1231068
  simp only [CollatzResearch.WordTrace]
  refine ⟨22450369352029180260338929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29933825802705573680451905 22450369352029180260338929)
  ·
    refine ⟨16837777014021885195254197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22450369352029180260338929 16837777014021885195254197)
    ·
      refine ⟨1578541595064551737055081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16837777014021885195254197 1578541595064551737055081)
      ·
        refine ⟨1183906196298413802791311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1578541595064551737055081 1183906196298413802791311)
        ·
          refine ⟨1775859294447620704186967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183906196298413802791311 1775859294447620704186967)
          ·
            refine ⟨2663788941671431056280451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775859294447620704186967 2663788941671431056280451)
            ·
              refine ⟨3995683412507146584420677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2663788941671431056280451 3995683412507146584420677)
              ·
                refine ⟨749190639845089984578877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3995683412507146584420677 749190639845089984578877)
                ·
                  refine ⟨280946489941908744217079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 749190639845089984578877 280946489941908744217079)
                  ·
                    rfl

theorem cell21_1231068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_1231068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231068 prefixEnd_1231068 := by exact prefixLift 1231068
  have htrace : WordTrace (prefixWord ++ tailWord_1231068) baseStart_1231068 baseEnd_1231068 := by
    simpa [prefixWord, tailWord_1231068, baseEnd_1231068] using wordTrace_append hprefix tailTrace_1231068
  have hstable : (prefixWord ++ tailWord_1231068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231068).length < 2 ^ (prefixWord ++ tailWord_1231068).sum := by decide
  have hdescent : baseEnd_1231068 < baseStart_1231068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231076 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 5]
def baseStart_1231076 : Nat := 118140960795 + 1231076 * 2 ^ 59
def prefixEnd_1231076 : Nat := 4983230072969 + 3 ^ 40 * 1231076 * 2
def baseEnd_1231076 : Nat := 280948315650902508083729

theorem tailTrace_1231076 : CollatzResearch.WordTrace tailWord_1231076 prefixEnd_1231076 280948315650902508083729 := by
  unfold tailWord_1231076
  simp only [CollatzResearch.WordTrace]
  refine ⟨22450515244014688943484541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29934020325352918591312721 22450515244014688943484541)
  ·
    refine ⟨8418943216505508353806703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22450515244014688943484541 8418943216505508353806703)
    ·
      refine ⟨12628414824758262530710055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8418943216505508353806703 12628414824758262530710055)
      ·
        refine ⟨18942622237137393796065083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12628414824758262530710055 18942622237137393796065083)
        ·
          refine ⟨28413933355706090694097625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18942622237137393796065083 28413933355706090694097625)
          ·
            refine ⟨21310450016779568020573219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28413933355706090694097625 21310450016779568020573219)
            ·
              refine ⟨31965675025169352030859829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21310450016779568020573219 31965675025169352030859829)
              ·
                refine ⟨2996782033609626752893109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31965675025169352030859829 2996782033609626752893109)
                ·
                  refine ⟨280948315650902508083729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2996782033609626752893109 280948315650902508083729)
                  ·
                    rfl

theorem cell21_1231076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_1231076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231076 prefixEnd_1231076 := by exact prefixLift 1231076
  have htrace : WordTrace (prefixWord ++ tailWord_1231076) baseStart_1231076 baseEnd_1231076 := by
    simpa [prefixWord, tailWord_1231076, baseEnd_1231076] using wordTrace_append hprefix tailTrace_1231076
  have hstable : (prefixWord ++ tailWord_1231076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231076).length < 2 ^ (prefixWord ++ tailWord_1231076).sum := by decide
  have hdescent : baseEnd_1231076 < baseStart_1231076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231079 : List Nat := [1, 1, 5, 3, 1, 3, 1, 6]
def baseStart_1231079 : Nat := 118140960795 + 1231079 * 2 ^ 59
def prefixEnd_1231079 : Nat := 4983230072969 + 3 ^ 40 * 1231079 * 2
def baseEnd_1231079 : Nat := 93649666763925056511241

theorem tailTrace_1231079 : CollatzResearch.WordTrace tailWord_1231079 prefixEnd_1231079 93649666763925056511241 := by
  unfold tailWord_1231079
  simp only [CollatzResearch.WordTrace]
  refine ⟨44901139907018509399328291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29934093271345672932885527 44901139907018509399328291)
  ·
    refine ⟨67351709860527764098992437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44901139907018509399328291 67351709860527764098992437)
    ·
      refine ⟨6314222799424477884280541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67351709860527764098992437 6314222799424477884280541)
      ·
        refine ⟨2367833549784179206605203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6314222799424477884280541 2367833549784179206605203)
        ·
          refine ⟨3551750324676268809907805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2367833549784179206605203 3551750324676268809907805)
          ·
            refine ⟨1331906371753600803715427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3551750324676268809907805 1331906371753600803715427)
            ·
              refine ⟨1997859557630401205573141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331906371753600803715427 1997859557630401205573141)
              ·
                refine ⟨93649666763925056511241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1997859557630401205573141 93649666763925056511241)
                ·
                  rfl

theorem cell21_1231079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 6].length) (baseStart_1231079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231079 prefixEnd_1231079 := by exact prefixLift 1231079
  have htrace : WordTrace (prefixWord ++ tailWord_1231079) baseStart_1231079 baseEnd_1231079 := by
    simpa [prefixWord, tailWord_1231079, baseEnd_1231079] using wordTrace_append hprefix tailTrace_1231079
  have hstable : (prefixWord ++ tailWord_1231079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231079).length < 2 ^ (prefixWord ++ tailWord_1231079).sum := by decide
  have hdescent : baseEnd_1231079 < baseStart_1231079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231121 : List Nat := [1, 2, 2, 1, 1, 6, 8]
def baseStart_1231121 : Nat := 118140960795 + 1231121 * 2 ^ 59
def prefixEnd_1231121 : Nat := 4983230072969 + 3 ^ 40 * 1231121 * 2
def baseEnd_1231121 : Nat := 31217620584888047759293

theorem tailTrace_1231121 : CollatzResearch.WordTrace tailWord_1231121 prefixEnd_1231121 31217620584888047759293 := by
  unfold tailWord_1231121
  simp only [CollatzResearch.WordTrace]
  refine ⟨44902671772866350572357217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29935114515244233714904811 44902671772866350572357217)
  ·
    refine ⟨33677003829649762929267913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44902671772866350572357217 33677003829649762929267913)
    ·
      refine ⟨25257752872237322196950935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33677003829649762929267913 25257752872237322196950935)
      ·
        refine ⟨37886629308355983295426403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25257752872237322196950935 37886629308355983295426403)
        ·
          refine ⟨56829943962533974943139605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37886629308355983295426403 56829943962533974943139605)
          ·
            refine ⟨2663903623243780075459669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56829943962533974943139605 2663903623243780075459669)
            ·
              refine ⟨31217620584888047759293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2663903623243780075459669 31217620584888047759293)
              ·
                rfl

theorem cell21_1231121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 8].length) (baseStart_1231121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231121 prefixEnd_1231121 := by exact prefixLift 1231121
  have htrace : WordTrace (prefixWord ++ tailWord_1231121) baseStart_1231121 baseEnd_1231121 := by
    simpa [prefixWord, tailWord_1231121, baseEnd_1231121] using wordTrace_append hprefix tailTrace_1231121
  have hstable : (prefixWord ++ tailWord_1231121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231121).length < 2 ^ (prefixWord ++ tailWord_1231121).sum := by decide
  have hdescent : baseEnd_1231121 < baseStart_1231121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231141 : List Nat := [1, 3, 1, 2, 5, 1, 3, 1, 4]
def baseStart_1231141 : Nat := 118140960795 + 1231141 * 2 ^ 59
def prefixEnd_1231141 : Nat := 4983230072969 + 3 ^ 40 * 1231141 * 2
def baseEnd_1231141 : Nat := 280963149536476839500263

theorem tailTrace_1231141 : CollatzResearch.WordTrace tailWord_1231141 prefixEnd_1231141 280963149536476839500263 := by
  unfold tailWord_1231141
  simp only [CollatzResearch.WordTrace]
  refine ⟨44903401232793893988085277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29935600821862595992056851 44903401232793893988085277)
  ·
    refine ⟨16838775462297710245531979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44903401232793893988085277 16838775462297710245531979)
    ·
      refine ⟨25258163193446565368297969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16838775462297710245531979 25258163193446565368297969)
      ·
        refine ⟨18943622395084924026223477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25258163193446565368297969 18943622395084924026223477)
        ·
          refine ⟨1775964599539211627458451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18943622395084924026223477 1775964599539211627458451)
          ·
            refine ⟨2663946899308817441187677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775964599539211627458451 2663946899308817441187677)
            ·
              refine ⟨998980087240806540445379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2663946899308817441187677 998980087240806540445379)
              ·
                refine ⟨1498470130861209810668069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998980087240806540445379 1498470130861209810668069)
                ·
                  refine ⟨280963149536476839500263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1498470130861209810668069 280963149536476839500263)
                  ·
                    rfl

theorem cell21_1231141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_1231141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231141 prefixEnd_1231141 := by exact prefixLift 1231141
  have htrace : WordTrace (prefixWord ++ tailWord_1231141) baseStart_1231141 baseEnd_1231141 := by
    simpa [prefixWord, tailWord_1231141, baseEnd_1231141] using wordTrace_append hprefix tailTrace_1231141
  have hstable : (prefixWord ++ tailWord_1231141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231141).length < 2 ^ (prefixWord ++ tailWord_1231141).sum := by decide
  have hdescent : baseEnd_1231141 < baseStart_1231141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231172 : List Nat := [2, 3, 4, 1, 3, 1, 7]
def baseStart_1231172 : Nat := 118140960795 + 1231172 * 2 ^ 59
def prefixEnd_1231172 : Nat := 4983230072969 + 3 ^ 40 * 1231172 * 2
def baseEnd_1231172 : Nat := 31218913795425297164837

theorem tailTrace_1231172 : CollatzResearch.WordTrace tailWord_1231172 prefixEnd_1231172 31218913795425297164837 := by
  unfold tailWord_1231172
  simp only [CollatzResearch.WordTrace]
  refine ⟨22452265947840793141231885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29936354597121057521642513 22452265947840793141231885)
  ·
    refine ⟨8419599730440297427961957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22452265947840793141231885 8419599730440297427961957)
    ·
      refine ⟨1578674949457555767742867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8419599730440297427961957 1578674949457555767742867)
      ·
        refine ⟨2368012424186333651614301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1578674949457555767742867 2368012424186333651614301)
        ·
          refine ⟨888004659069875119355363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2368012424186333651614301 888004659069875119355363)
          ·
            refine ⟨1332006988604812679033045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888004659069875119355363 1332006988604812679033045)
            ·
              refine ⟨31218913795425297164837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1332006988604812679033045 31218913795425297164837)
              ·
                rfl

theorem cell21_1231172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 7].length) (baseStart_1231172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231172 prefixEnd_1231172 := by exact prefixLift 1231172
  have htrace : WordTrace (prefixWord ++ tailWord_1231172) baseStart_1231172 baseEnd_1231172 := by
    simpa [prefixWord, tailWord_1231172, baseEnd_1231172] using wordTrace_append hprefix tailTrace_1231172
  have hstable : (prefixWord ++ tailWord_1231172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231172).length < 2 ^ (prefixWord ++ tailWord_1231172).sum := by decide
  have hdescent : baseEnd_1231172 < baseStart_1231172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231200 : List Nat := [2, 1, 1, 3, 5, 1, 1, 3, 4]
def baseStart_1231200 : Nat := 118140960795 + 1231200 * 2 ^ 59
def prefixEnd_1231200 : Nat := 4983230072969 + 3 ^ 40 * 1231200 * 2
def baseEnd_1231200 : Nat := 280976614140305848016809

theorem tailTrace_1231200 : CollatzResearch.WordTrace tailWord_1231200 prefixEnd_1231200 280976614140305848016809 := by
  unfold tailWord_1231200
  simp only [CollatzResearch.WordTrace]
  refine ⟨22452776569790073532241527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29937035426386764709655369 22452776569790073532241527)
  ·
    refine ⟨33679164854685110298362291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22452776569790073532241527 33679164854685110298362291)
    ·
      refine ⟨50518747282027665447543437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33679164854685110298362291 50518747282027665447543437)
      ·
        refine ⟨18944530230760374542828789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50518747282027665447543437 18944530230760374542828789)
        ·
          refine ⟨1776049709133785113390199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18944530230760374542828789 1776049709133785113390199)
          ·
            refine ⟨2664074563700677670085299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776049709133785113390199 2664074563700677670085299)
            ·
              refine ⟨3996111845551016505127949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2664074563700677670085299 3996111845551016505127949)
              ·
                refine ⟨1498541942081631189422981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3996111845551016505127949 1498541942081631189422981)
                ·
                  refine ⟨280976614140305848016809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1498541942081631189422981 280976614140305848016809)
                  ·
                    rfl

theorem cell21_1231200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_1231200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231200 prefixEnd_1231200 := by exact prefixLift 1231200
  have htrace : WordTrace (prefixWord ++ tailWord_1231200) baseStart_1231200 baseEnd_1231200 := by
    simpa [prefixWord, tailWord_1231200, baseEnd_1231200] using wordTrace_append hprefix tailTrace_1231200
  have hstable : (prefixWord ++ tailWord_1231200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231200).length < 2 ^ (prefixWord ++ tailWord_1231200).sum := by decide
  have hdescent : baseEnd_1231200 < baseStart_1231200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231234 : List Nat := [3, 4, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1231234 : Nat := 118140960795 + 1231234 * 2 ^ 59
def prefixEnd_1231234 : Nat := 4983230072969 + 3 ^ 40 * 1231234 * 2
def baseEnd_1231234 : Nat := 280984373403529344450073

theorem tailTrace_1231234 : CollatzResearch.WordTrace tailWord_1231234 prefixEnd_1231234 280984373403529344450073 := by
  unfold tailWord_1231234
  simp only [CollatzResearch.WordTrace]
  refine ⟨11226698305364242717805189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29937862147637980580813837 11226698305364242717805189)
  ·
    refine ⟨2105005932255795509588473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11226698305364242717805189 2105005932255795509588473)
    ·
      refine ⟨1578754449191846632191355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2105005932255795509588473 1578754449191846632191355)
      ·
        refine ⟨2368131673787769948287033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1578754449191846632191355 2368131673787769948287033)
        ·
          refine ⟨1776098755340827461215275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2368131673787769948287033 1776098755340827461215275)
          ·
            refine ⟨2664148133011241191822913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776098755340827461215275 2664148133011241191822913)
            ·
              refine ⟨1998111099758430893867185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2664148133011241191822913 1998111099758430893867185)
              ·
                refine ⟨1498583324818823170400389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1998111099758430893867185 1498583324818823170400389)
                ·
                  refine ⟨280984373403529344450073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1498583324818823170400389 280984373403529344450073)
                  ·
                    rfl

theorem cell21_1231234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1231234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231234 prefixEnd_1231234 := by exact prefixLift 1231234
  have htrace : WordTrace (prefixWord ++ tailWord_1231234) baseStart_1231234 baseEnd_1231234 := by
    simpa [prefixWord, tailWord_1231234, baseEnd_1231234] using wordTrace_append hprefix tailTrace_1231234
  have hstable : (prefixWord ++ tailWord_1231234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231234).length < 2 ^ (prefixWord ++ tailWord_1231234).sum := by decide
  have hdescent : baseEnd_1231234 < baseStart_1231234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231262 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_1231262 : Nat := 118140960795 + 1231262 * 2 ^ 59
def prefixEnd_1231262 : Nat := 4983230072969 + 3 ^ 40 * 1231262 * 2
def baseEnd_1231262 : Nat := 280990763385007517983349

theorem tailTrace_1231262 : CollatzResearch.WordTrace tailWord_1231262 prefixEnd_1231262 280990763385007517983349 := by
  unfold tailWord_1231262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5613476808169441456655005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29938542976903687768826693 5613476808169441456655005)
  ·
    refine ⟨2105053803063540546245627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5613476808169441456655005 2105053803063540546245627)
    ·
      refine ⟨3157580704595310819368441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2105053803063540546245627 3157580704595310819368441)
      ·
        refine ⟨2368185528446483114526331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3157580704595310819368441 2368185528446483114526331)
        ·
          refine ⟨3552278292669724671789497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2368185528446483114526331 3552278292669724671789497)
          ·
            refine ⟨2664208719502293503842123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3552278292669724671789497 2664208719502293503842123)
            ·
              refine ⟨3996313079253440255763185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2664208719502293503842123 3996313079253440255763185)
              ·
                refine ⟨2997234809440080191822389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3996313079253440255763185 2997234809440080191822389)
                ·
                  refine ⟨280990763385007517983349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2997234809440080191822389 280990763385007517983349)
                  ·
                    rfl

theorem cell21_1231262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_1231262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231262 prefixEnd_1231262 := by exact prefixLift 1231262
  have htrace : WordTrace (prefixWord ++ tailWord_1231262) baseStart_1231262 baseEnd_1231262 := by
    simpa [prefixWord, tailWord_1231262, baseEnd_1231262] using wordTrace_append hprefix tailTrace_1231262
  have hstable : (prefixWord ++ tailWord_1231262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231262).length < 2 ^ (prefixWord ++ tailWord_1231262).sum := by decide
  have hdescent : baseEnd_1231262 < baseStart_1231262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231304 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 5]
def baseStart_1231304 : Nat := 118140960795 + 1231304 * 2 ^ 59
def prefixEnd_1231304 : Nat := 4983230072969 + 3 ^ 40 * 1231304 * 2
def baseEnd_1231304 : Nat := 281000348357224778283263

theorem tailTrace_1231304 : CollatzResearch.WordTrace tailWord_1231304 prefixEnd_1231304 281000348357224778283263 := by
  unfold tailWord_1231304
  simp only [CollatzResearch.WordTrace]
  refine ⟨22454673165601686413134483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29939564220802248550845977 22454673165601686413134483)
  ·
    refine ⟨33682009748402529619701725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22454673165601686413134483 33682009748402529619701725)
    ·
      refine ⟨12630753655650948607388147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33682009748402529619701725 12630753655650948607388147)
      ·
        refine ⟨18946130483476422911082221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12630753655650948607388147 18946130483476422911082221)
        ·
          refine ⟨7104798931303658591655833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18946130483476422911082221 7104798931303658591655833)
          ·
            refine ⟨5328599198477743943741875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7104798931303658591655833 5328599198477743943741875)
            ·
              refine ⟨7992898797716615915612813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5328599198477743943741875 7992898797716615915612813)
              ·
                refine ⟨2997337049143730968354805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7992898797716615915612813 2997337049143730968354805)
                ·
                  refine ⟨281000348357224778283263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2997337049143730968354805 281000348357224778283263)
                  ·
                    rfl

theorem cell21_1231304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_1231304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231304 prefixEnd_1231304 := by exact prefixLift 1231304
  have htrace : WordTrace (prefixWord ++ tailWord_1231304) baseStart_1231304 baseEnd_1231304 := by
    simpa [prefixWord, tailWord_1231304, baseEnd_1231304] using wordTrace_append hprefix tailTrace_1231304
  have hstable : (prefixWord ++ tailWord_1231304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231304).length < 2 ^ (prefixWord ++ tailWord_1231304).sum := by decide
  have hdescent : baseEnd_1231304 < baseStart_1231304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231338 : List Nat := [3, 1, 3, 1, 3, 1, 3, 3, 3]
def baseStart_1231338 : Nat := 118140960795 + 1231338 * 2 ^ 59
def prefixEnd_1231338 : Nat := 4983230072969 + 3 ^ 40 * 1231338 * 2
def baseEnd_1231338 : Nat := 281008107620448274716527

theorem tailTrace_1231338 : CollatzResearch.WordTrace tailWord_1231338 prefixEnd_1231338 281008107620448274716527 := by
  unfold tailWord_1231338
  simp only [CollatzResearch.WordTrace]
  refine ⟨11227646603270049158251667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29940390942053464422004445 11227646603270049158251667)
  ·
    refine ⟨16841469904905073737377501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11227646603270049158251667 16841469904905073737377501)
    ·
      refine ⟨6315551214339402651516563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16841469904905073737377501 6315551214339402651516563)
      ·
        refine ⟨9473326821509103977274845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6315551214339402651516563 9473326821509103977274845)
        ·
          refine ⟨3552497558065913991478067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9473326821509103977274845 3552497558065913991478067)
          ·
            refine ⟨5328746337098870987217101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3552497558065913991478067 5328746337098870987217101)
            ·
              refine ⟨1998279876412076620206413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5328746337098870987217101 1998279876412076620206413)
              ·
                refine ⟨749354953654528732577405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1998279876412076620206413 749354953654528732577405)
                ·
                  refine ⟨281008107620448274716527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 749354953654528732577405 281008107620448274716527)
                  ·
                    rfl

theorem cell21_1231338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_1231338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231338 prefixEnd_1231338 := by exact prefixLift 1231338
  have htrace : WordTrace (prefixWord ++ tailWord_1231338) baseStart_1231338 baseEnd_1231338 := by
    simpa [prefixWord, tailWord_1231338, baseEnd_1231338] using wordTrace_append hprefix tailTrace_1231338
  have hstable : (prefixWord ++ tailWord_1231338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231338).length < 2 ^ (prefixWord ++ tailWord_1231338).sum := by decide
  have hdescent : baseEnd_1231338 < baseStart_1231338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231411 : List Nat := [1, 1, 1, 2, 4, 2, 4, 2, 4]
def baseStart_1231411 : Nat := 118140960795 + 1231411 * 2 ^ 59
def prefixEnd_1231411 : Nat := 4983230072969 + 3 ^ 40 * 1231411 * 2
def baseEnd_1231411 : Nat := 281024767215016369999711

theorem tailTrace_1231411 : CollatzResearch.WordTrace tailWord_1231411 prefixEnd_1231411 281024767215016369999711 := by
  unfold tailWord_1231411
  simp only [CollatzResearch.WordTrace]
  refine ⟨44913248941815730100414087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29942165961210486733609391 44913248941815730100414087)
  ·
    refine ⟨67369873412723595150621131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44913248941815730100414087 67369873412723595150621131)
    ·
      refine ⟨101054810119085392725931697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67369873412723595150621131 101054810119085392725931697)
      ·
        refine ⟨75791107589314044544448773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101054810119085392725931697 75791107589314044544448773)
        ·
          refine ⟨14210832672996383352084145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75791107589314044544448773 14210832672996383352084145)
          ·
            refine ⟨10658124504747287514063109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14210832672996383352084145 10658124504747287514063109)
            ·
              refine ⟨1998398344640116408886833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10658124504747287514063109 1998398344640116408886833)
              ·
                refine ⟨1498798758480087306665125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1998398344640116408886833 1498798758480087306665125)
                ·
                  refine ⟨281024767215016369999711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1498798758480087306665125 281024767215016369999711)
                  ·
                    rfl

theorem cell21_1231411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 4].length) (baseStart_1231411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231411 prefixEnd_1231411 := by exact prefixLift 1231411
  have htrace : WordTrace (prefixWord ++ tailWord_1231411) baseStart_1231411 baseEnd_1231411 := by
    simpa [prefixWord, tailWord_1231411, baseEnd_1231411] using wordTrace_append hprefix tailTrace_1231411
  have hstable : (prefixWord ++ tailWord_1231411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231411).length < 2 ^ (prefixWord ++ tailWord_1231411).sum := by decide
  have hdescent : baseEnd_1231411 < baseStart_1231411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231439 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 7]
def baseStart_1231439 : Nat := 118140960795 + 1231439 * 2 ^ 59
def prefixEnd_1231439 : Nat := 4983230072969 + 3 ^ 40 * 1231439 * 2
def baseEnd_1231439 : Nat := 281031157196494543532987

theorem tailTrace_1231439 : CollatzResearch.WordTrace tailWord_1231439 prefixEnd_1231439 281031157196494543532987 := by
  unfold tailWord_1231439
  simp only [CollatzResearch.WordTrace]
  refine ⟨44914270185714290882433371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29942846790476193921622247 44914270185714290882433371)
  ·
    refine ⟨67371405278571436323650057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44914270185714290882433371 67371405278571436323650057)
    ·
      refine ⟨50528553958928577242737543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67371405278571436323650057 50528553958928577242737543)
      ·
        refine ⟨75792830938392865864106315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50528553958928577242737543 75792830938392865864106315)
        ·
          refine ⟨113689246407589298796159473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75792830938392865864106315 113689246407589298796159473)
          ·
            refine ⟨85266934805691974097119605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113689246407589298796159473 85266934805691974097119605)
            ·
              refine ⟨7993775138033622571604963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85266934805691974097119605 7993775138033622571604963)
              ·
                refine ⟨11990662707050433857407445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7993775138033622571604963 11990662707050433857407445)
                ·
                  refine ⟨281031157196494543532987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11990662707050433857407445 281031157196494543532987)
                  ·
                    rfl

theorem cell21_1231439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 7].length) (baseStart_1231439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231439 prefixEnd_1231439 := by exact prefixLift 1231439
  have htrace : WordTrace (prefixWord ++ tailWord_1231439) baseStart_1231439 baseEnd_1231439 := by
    simpa [prefixWord, tailWord_1231439, baseEnd_1231439] using wordTrace_append hprefix tailTrace_1231439
  have hstable : (prefixWord ++ tailWord_1231439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231439).length < 2 ^ (prefixWord ++ tailWord_1231439).sum := by decide
  have hdescent : baseEnd_1231439 < baseStart_1231439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231442 : List Nat := [3, 2, 2, 1, 2, 1, 5, 5]
def baseStart_1231442 : Nat := 118140960795 + 1231442 * 2 ^ 59
def prefixEnd_1231442 : Nat := 4983230072969 + 3 ^ 40 * 1231442 * 2
def baseEnd_1231442 : Nat := 93677280612455734994327

theorem tailTrace_1231442 : CollatzResearch.WordTrace tailWord_1231442 prefixEnd_1231442 93677280612455734994327 := by
  unfold tailWord_1231442
  simp only [CollatzResearch.WordTrace]
  refine ⟨11228594901175855598698145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29942919736468948263195053 11228594901175855598698145)
  ·
    refine ⟨8421446175881891699023609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11228594901175855598698145 8421446175881891699023609)
    ·
      refine ⟨6316084631911418774267707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8421446175881891699023609 6316084631911418774267707)
      ·
        refine ⟨9474126947867128161401561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6316084631911418774267707 9474126947867128161401561)
        ·
          refine ⟨7105595210900346121051171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9474126947867128161401561 7105595210900346121051171)
          ·
            refine ⟨10658392816350519181576757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7105595210900346121051171 10658392816350519181576757)
            ·
              refine ⟨999224326532861173272821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10658392816350519181576757 999224326532861173272821)
              ·
                refine ⟨93677280612455734994327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 999224326532861173272821 93677280612455734994327)
                ·
                  rfl

theorem cell21_1231442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_1231442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231442 prefixEnd_1231442 := by exact prefixLift 1231442
  have htrace : WordTrace (prefixWord ++ tailWord_1231442) baseStart_1231442 baseEnd_1231442 := by
    simpa [prefixWord, tailWord_1231442, baseEnd_1231442] using wordTrace_append hprefix tailTrace_1231442
  have hstable : (prefixWord ++ tailWord_1231442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231442).length < 2 ^ (prefixWord ++ tailWord_1231442).sum := by decide
  have hdescent : baseEnd_1231442 < baseStart_1231442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231580 : List Nat := [2, 2, 5, 1, 1, 1, 1, 4, 4]
def baseStart_1231580 : Nat := 118140960795 + 1231580 * 2 ^ 59
def prefixEnd_1231580 : Nat := 4983230072969 + 3 ^ 40 * 1231580 * 2
def baseEnd_1231580 : Nat := 281063335317509631682699

theorem tailTrace_1231580 : CollatzResearch.WordTrace tailWord_1231580 prefixEnd_1231580 281063335317509631682699 := by
  unfold tailWord_1231580
  simp only [CollatzResearch.WordTrace]
  refine ⟨22459706439101735981658097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29946275252135647975544129 22459706439101735981658097)
  ·
    refine ⟨16844779829326301986243573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22459706439101735981658097 16844779829326301986243573)
    ·
      refine ⟨1579198108999340811210335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16844779829326301986243573 1579198108999340811210335)
      ·
        refine ⟨2368797163499011216815503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1579198108999340811210335 2368797163499011216815503)
        ·
          refine ⟨3553195745248516825223255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2368797163499011216815503 3553195745248516825223255)
          ·
            refine ⟨5329793617872775237834883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3553195745248516825223255 5329793617872775237834883)
            ·
              refine ⟨7994690426809162856752325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5329793617872775237834883 7994690426809162856752325)
              ·
                refine ⟨1499004455026718035641061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7994690426809162856752325 1499004455026718035641061)
                ·
                  refine ⟨281063335317509631682699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1499004455026718035641061 281063335317509631682699)
                  ·
                    rfl

theorem cell21_1231580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_1231580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231580 prefixEnd_1231580 := by exact prefixLift 1231580
  have htrace : WordTrace (prefixWord ++ tailWord_1231580) baseStart_1231580 baseEnd_1231580 := by
    simpa [prefixWord, tailWord_1231580, baseEnd_1231580] using wordTrace_append hprefix tailTrace_1231580
  have hstable : (prefixWord ++ tailWord_1231580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231580).length < 2 ^ (prefixWord ++ tailWord_1231580).sum := by decide
  have hdescent : baseEnd_1231580 < baseStart_1231580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231639 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 6]
def baseStart_1231639 : Nat := 118140960795 + 1231639 * 2 ^ 59
def prefixEnd_1231639 : Nat := 4983230072969 + 3 ^ 40 * 1231639 * 2
def baseEnd_1231639 : Nat := 281076799921338640199245

theorem tailTrace_1231639 : CollatzResearch.WordTrace tailWord_1231639 prefixEnd_1231639 281076799921338640199245 := by
  unfold tailWord_1231639
  simp only [CollatzResearch.WordTrace]
  refine ⟨44921564784989725039713971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29947709856659816693142647 44921564784989725039713971)
  ·
    refine ⟨67382347177484587559570957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44921564784989725039713971 67382347177484587559570957)
    ·
      refine ⟨25268380191556720334839109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67382347177484587559570957 25268380191556720334839109)
      ·
        refine ⟨4737821285916885062782333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25268380191556720334839109 4737821285916885062782333)
        ·
          refine ⟨1776682982218831898543375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4737821285916885062782333 1776682982218831898543375)
          ·
            refine ⟨2665024473328247847815063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776682982218831898543375 2665024473328247847815063)
            ·
              refine ⟨3997536709992371771722595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2665024473328247847815063 3997536709992371771722595)
              ·
                refine ⟨5996305064988557657583893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3997536709992371771722595 5996305064988557657583893)
                ·
                  refine ⟨281076799921338640199245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5996305064988557657583893 281076799921338640199245)
                  ·
                    rfl

theorem cell21_1231639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 6].length) (baseStart_1231639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231639 prefixEnd_1231639 := by exact prefixLift 1231639
  have htrace : WordTrace (prefixWord ++ tailWord_1231639) baseStart_1231639 baseEnd_1231639 := by
    simpa [prefixWord, tailWord_1231639, baseEnd_1231639] using wordTrace_append hprefix tailTrace_1231639
  have hstable : (prefixWord ++ tailWord_1231639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231639).length < 2 ^ (prefixWord ++ tailWord_1231639).sum := by decide
  have hdescent : baseEnd_1231639 < baseStart_1231639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231656 : List Nat := [2, 1, 5, 1, 1, 1, 5, 1, 4]
def baseStart_1231656 : Nat := 118140960795 + 1231656 * 2 ^ 59
def prefixEnd_1231656 : Nat := 4983230072969 + 3 ^ 40 * 1231656 * 2
def baseEnd_1231656 : Nat := 281080679552950388415877

theorem tailTrace_1231656 : CollatzResearch.WordTrace tailWord_1231656 prefixEnd_1231656 281080679552950388415877 := by
  unfold tailWord_1231656
  simp only [CollatzResearch.WordTrace]
  refine ⟨22461092412964068471541411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29948123217285424628721881 22461092412964068471541411)
  ·
    refine ⟨33691638619446102707312117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22461092412964068471541411 33691638619446102707312117)
    ·
      refine ⟨3158591120573072128810511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33691638619446102707312117 3158591120573072128810511)
      ·
        refine ⟨4737886680859608193215767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3158591120573072128810511 4737886680859608193215767)
        ·
          refine ⟨7106830021289412289823651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4737886680859608193215767 7106830021289412289823651)
          ·
            refine ⟨10660245031934118434735477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7106830021289412289823651 10660245031934118434735477)
            ·
              refine ⟨999397971743823603256451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10660245031934118434735477 999397971743823603256451)
              ·
                refine ⟨1499096957615735404884677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 999397971743823603256451 1499096957615735404884677)
                ·
                  refine ⟨281080679552950388415877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1499096957615735404884677 281080679552950388415877)
                  ·
                    rfl

theorem cell21_1231656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 4].length) (baseStart_1231656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231656 prefixEnd_1231656 := by exact prefixLift 1231656
  have htrace : WordTrace (prefixWord ++ tailWord_1231656) baseStart_1231656 baseEnd_1231656 := by
    simpa [prefixWord, tailWord_1231656, baseEnd_1231656] using wordTrace_append hprefix tailTrace_1231656
  have hstable : (prefixWord ++ tailWord_1231656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231656).length < 2 ^ (prefixWord ++ tailWord_1231656).sum := by decide
  have hdescent : baseEnd_1231656 < baseStart_1231656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231698 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 6]
def baseStart_1231698 : Nat := 118140960795 + 1231698 * 2 ^ 59
def prefixEnd_1231698 : Nat := 4983230072969 + 3 ^ 40 * 1231698 * 2
def baseEnd_1231698 : Nat := 281090264525167648715791

theorem tailTrace_1231698 : CollatzResearch.WordTrace tailWord_1231698 prefixEnd_1231698 281090264525167648715791 := by
  unfold tailWord_1231698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11230929172943994529027937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29949144461183985410741165 11230929172943994529027937)
  ·
    refine ⟨8423196879707995896770953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11230929172943994529027937 8423196879707995896770953)
    ·
      refine ⟨6317397659780996922578215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8423196879707995896770953 6317397659780996922578215)
      ·
        refine ⟨9476096489671495383867323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6317397659780996922578215 9476096489671495383867323)
        ·
          refine ⟨14214144734507243075800985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9476096489671495383867323 14214144734507243075800985)
          ·
            refine ⟨10660608550880432306850739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14214144734507243075800985 10660608550880432306850739)
            ·
              refine ⟨15990912826320648460276109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10660608550880432306850739 15990912826320648460276109)
              ·
                refine ⟨5996592309870243172603541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15990912826320648460276109 5996592309870243172603541)
                ·
                  refine ⟨281090264525167648715791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5996592309870243172603541 281090264525167648715791)
                  ·
                    rfl

theorem cell21_1231698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_1231698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231698 prefixEnd_1231698 := by exact prefixLift 1231698
  have htrace : WordTrace (prefixWord ++ tailWord_1231698) baseStart_1231698 baseEnd_1231698 := by
    simpa [prefixWord, tailWord_1231698, baseEnd_1231698] using wordTrace_append hprefix tailTrace_1231698
  have hstable : (prefixWord ++ tailWord_1231698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231698).length < 2 ^ (prefixWord ++ tailWord_1231698).sum := by decide
  have hdescent : baseEnd_1231698 < baseStart_1231698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231715 : List Nat := [1, 1, 1, 5, 3, 2, 1, 3, 4]
def baseStart_1231715 : Nat := 118140960795 + 1231715 * 2 ^ 59
def prefixEnd_1231715 : Nat := 4983230072969 + 3 ^ 40 * 1231715 * 2
def baseEnd_1231715 : Nat := 281094144156779396932423

theorem tailTrace_1231715 : CollatzResearch.WordTrace tailWord_1231715 prefixEnd_1231715 281094144156779396932423 := by
  unfold tailWord_1231715
  simp only [CollatzResearch.WordTrace]
  refine ⟨44924336732714390019480599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29949557821809593346320399 44924336732714390019480599)
  ·
    refine ⟨67386505099071585029220899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44924336732714390019480599 67386505099071585029220899)
    ·
      refine ⟨101079757648607377543831349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67386505099071585029220899 101079757648607377543831349)
      ·
        refine ⟨9476227279556941644734189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101079757648607377543831349 9476227279556941644734189)
        ·
          refine ⟨3553585229833853116775321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9476227279556941644734189 3553585229833853116775321)
          ·
            refine ⟨2665188922375389837581491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3553585229833853116775321 2665188922375389837581491)
            ·
              refine ⟨3997783383563084756372237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2665188922375389837581491 3997783383563084756372237)
              ·
                refine ⟨1499168768836156783639589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3997783383563084756372237 1499168768836156783639589)
                ·
                  refine ⟨281094144156779396932423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1499168768836156783639589 281094144156779396932423)
                  ·
                    rfl

theorem cell21_1231715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 4].length) (baseStart_1231715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231715 prefixEnd_1231715 := by exact prefixLift 1231715
  have htrace : WordTrace (prefixWord ++ tailWord_1231715) baseStart_1231715 baseEnd_1231715 := by
    simpa [prefixWord, tailWord_1231715, baseEnd_1231715] using wordTrace_append hprefix tailTrace_1231715
  have hstable : (prefixWord ++ tailWord_1231715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231715).length < 2 ^ (prefixWord ++ tailWord_1231715).sum := by decide
  have hdescent : baseEnd_1231715 < baseStart_1231715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231746 : List Nat := [3, 4, 2, 2, 10]
def baseStart_1231746 : Nat := 118140960795 + 1231746 * 2 ^ 59
def prefixEnd_1231746 : Nat := 4983230072969 + 3 ^ 40 * 1231746 * 2
def baseEnd_1231746 : Nat := 3470385417026299159453

theorem tailTrace_1231746 : CollatzResearch.WordTrace tailWord_1231746 prefixEnd_1231746 3470385417026299159453 := by
  unfold tailWord_1231746
  simp only [CollatzResearch.WordTrace]
  refine ⟨11231366848900520578464773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29950311597068054875906061 11231366848900520578464773)
  ·
    refine ⟨2105881284168847608462145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11231366848900520578464773 2105881284168847608462145)
    ·
      refine ⟨1579410963126635706346609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2105881284168847608462145 1579410963126635706346609)
      ·
        refine ⟨1184558222344976779759957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1579410963126635706346609 1184558222344976779759957)
        ·
          refine ⟨3470385417026299159453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1184558222344976779759957 3470385417026299159453)
          ·
            rfl

theorem cell21_1231746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 10].length) (baseStart_1231746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231746 prefixEnd_1231746 := by exact prefixLift 1231746
  have htrace : WordTrace (prefixWord ++ tailWord_1231746) baseStart_1231746 baseEnd_1231746 := by
    simpa [prefixWord, tailWord_1231746, baseEnd_1231746] using wordTrace_append hprefix tailTrace_1231746
  have hstable : (prefixWord ++ tailWord_1231746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231746).length < 2 ^ (prefixWord ++ tailWord_1231746).sum := by decide
  have hdescent : baseEnd_1231746 < baseStart_1231746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231805 : List Nat := [1, 4, 1, 2, 4, 1, 8]
def baseStart_1231805 : Nat := 118140960795 + 1231805 * 2 ^ 59
def prefixEnd_1231805 : Nat := 4983230072969 + 3 ^ 40 * 1231805 * 2
def baseEnd_1231805 : Nat := 31234964820328804492471

theorem tailTrace_1231805 : CollatzResearch.WordTrace tailWord_1231805 prefixEnd_1231805 31234964820328804492471 := by
  unfold tailWord_1231805
  simp only [CollatzResearch.WordTrace]
  refine ⟨44927619302388335390256869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29951746201592223593504579 44927619302388335390256869)
  ·
    refine ⟨8423928619197812885673163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44927619302388335390256869 8423928619197812885673163)
    ·
      refine ⟨12635892928796719328509745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8423928619197812885673163 12635892928796719328509745)
      ·
        refine ⟨9476919696597539496382309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12635892928796719328509745 9476919696597539496382309)
        ·
          refine ⟨1776922443112038655571683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9476919696597539496382309 1776922443112038655571683)
          ·
            refine ⟨2665383664668057983357525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776922443112038655571683 2665383664668057983357525)
            ·
              refine ⟨31234964820328804492471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2665383664668057983357525 31234964820328804492471)
              ·
                rfl

theorem cell21_1231805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 8].length) (baseStart_1231805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231805 prefixEnd_1231805 := by exact prefixLift 1231805
  have htrace : WordTrace (prefixWord ++ tailWord_1231805) baseStart_1231805 baseEnd_1231805 := by
    simpa [prefixWord, tailWord_1231805, baseEnd_1231805] using wordTrace_append hprefix tailTrace_1231805
  have hstable : (prefixWord ++ tailWord_1231805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231805).length < 2 ^ (prefixWord ++ tailWord_1231805).sum := by decide
  have hdescent : baseEnd_1231805 < baseStart_1231805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231819 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 5]
def baseStart_1231819 : Nat := 118140960795 + 1231819 * 2 ^ 59
def prefixEnd_1231819 : Nat := 4983230072969 + 3 ^ 40 * 1231819 * 2
def baseEnd_1231819 : Nat := 281117878373698327198877

theorem tailTrace_1231819 : CollatzResearch.WordTrace tailWord_1231819 prefixEnd_1231819 281117878373698327198877 := by
  unfold tailWord_1231819
  simp only [CollatzResearch.WordTrace]
  refine ⟨44928129924337615781266511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29952086616225077187511007 44928129924337615781266511)
  ·
    refine ⟨67392194886506423671899767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44928129924337615781266511 67392194886506423671899767)
    ·
      refine ⟨101088292329759635507849651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67392194886506423671899767 101088292329759635507849651)
      ·
        refine ⟨151632438494639453261774477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101088292329759635507849651 151632438494639453261774477)
        ·
          refine ⟨56862164435489794973165429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151632438494639453261774477 56862164435489794973165429)
          ·
            refine ⟨5330827915827168278734259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56862164435489794973165429 5330827915827168278734259)
            ·
              refine ⟨7996241873740752418101389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5330827915827168278734259 7996241873740752418101389)
              ·
                refine ⟨2998590702652782156788021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7996241873740752418101389 2998590702652782156788021)
                ·
                  refine ⟨281117878373698327198877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2998590702652782156788021 281117878373698327198877)
                  ·
                    rfl

theorem cell21_1231819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 5].length) (baseStart_1231819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231819 prefixEnd_1231819 := by exact prefixLift 1231819
  have htrace : WordTrace (prefixWord ++ tailWord_1231819) baseStart_1231819 baseEnd_1231819 := by
    simpa [prefixWord, tailWord_1231819, baseEnd_1231819] using wordTrace_append hprefix tailTrace_1231819
  have hstable : (prefixWord ++ tailWord_1231819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231819).length < 2 ^ (prefixWord ++ tailWord_1231819).sum := by decide
  have hdescent : baseEnd_1231819 < baseStart_1231819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231839 : List Nat := [1, 1, 2, 3, 6, 1, 2, 5]
def baseStart_1231839 : Nat := 118140960795 + 1231839 * 2 ^ 59
def prefixEnd_1231839 : Nat := 4983230072969 + 3 ^ 40 * 1231839 * 2
def baseEnd_1231839 : Nat := 93707480882060912288501

theorem tailTrace_1231839 : CollatzResearch.WordTrace tailWord_1231839 prefixEnd_1231839 93707480882060912288501 := by
  unfold tailWord_1231839
  simp only [CollatzResearch.WordTrace]
  refine ⟨44928859384265159196994571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29952572922843439464663047 44928859384265159196994571)
  ·
    refine ⟨67393289076397738795491857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44928859384265159196994571 67393289076397738795491857)
    ·
      refine ⟨50544966807298304096618893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67393289076397738795491857 50544966807298304096618893)
      ·
        refine ⟨18954362552736864036232085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50544966807298304096618893 18954362552736864036232085)
        ·
          refine ⟨888485744659540501698379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18954362552736864036232085 888485744659540501698379)
          ·
            refine ⟨1332728616989310752547569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888485744659540501698379 1332728616989310752547569)
            ·
              refine ⟨999546462741983064410677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1332728616989310752547569 999546462741983064410677)
              ·
                refine ⟨93707480882060912288501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 999546462741983064410677 93707480882060912288501)
                ·
                  rfl

theorem cell21_1231839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 5].length) (baseStart_1231839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231839 prefixEnd_1231839 := by exact prefixLift 1231839
  have htrace : WordTrace (prefixWord ++ tailWord_1231839) baseStart_1231839 baseEnd_1231839 := by
    simpa [prefixWord, tailWord_1231839, baseEnd_1231839] using wordTrace_append hprefix tailTrace_1231839
  have hstable : (prefixWord ++ tailWord_1231839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231839).length < 2 ^ (prefixWord ++ tailWord_1231839).sum := by decide
  have hdescent : baseEnd_1231839 < baseStart_1231839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231850 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 6]
def baseStart_1231850 : Nat := 118140960795 + 1231850 * 2 ^ 59
def prefixEnd_1231850 : Nat := 4983230072969 + 3 ^ 40 * 1231850 * 2
def baseEnd_1231850 : Nat := 281124952996049162182147

theorem tailTrace_1231850 : CollatzResearch.WordTrace tailWord_1231850 prefixEnd_1231850 281124952996049162182147 := by
  unfold tailWord_1231850
  simp only [CollatzResearch.WordTrace]
  refine ⟨11232315146806327018911251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29952840391483538717096669 11232315146806327018911251)
  ·
    refine ⟨16848472720209490528366877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11232315146806327018911251 16848472720209490528366877)
    ·
      refine ⟨6318177270078558948137579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16848472720209490528366877 6318177270078558948137579)
      ·
        refine ⟨9477265905117838422206369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6318177270078558948137579 9477265905117838422206369)
        ·
          refine ⟨7107949428838378816654777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9477265905117838422206369 7107949428838378816654777)
          ·
            refine ⟨5330962071628784112491083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7107949428838378816654777 5330962071628784112491083)
            ·
              refine ⟨7996443107443176168736625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5330962071628784112491083 7996443107443176168736625)
              ·
                refine ⟨5997332330582382126552469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7996443107443176168736625 5997332330582382126552469)
                ·
                  refine ⟨281124952996049162182147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5997332330582382126552469 281124952996049162182147)
                  ·
                    rfl

theorem cell21_1231850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_1231850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231850 prefixEnd_1231850 := by exact prefixLift 1231850
  have htrace : WordTrace (prefixWord ++ tailWord_1231850) baseStart_1231850 baseEnd_1231850 := by
    simpa [prefixWord, tailWord_1231850, baseEnd_1231850] using wordTrace_append hprefix tailTrace_1231850
  have hstable : (prefixWord ++ tailWord_1231850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231850).length < 2 ^ (prefixWord ++ tailWord_1231850).sum := by decide
  have hdescent : baseEnd_1231850 < baseStart_1231850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231870 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_1231870 : Nat := 118140960795 + 1231870 * 2 ^ 59
def prefixEnd_1231870 : Nat := 4983230072969 + 3 ^ 40 * 1231870 * 2
def baseEnd_1231870 : Nat := 281129517268533571848773

theorem tailTrace_1231870 : CollatzResearch.WordTrace tailWord_1231870 prefixEnd_1231870 281129517268533571848773 := by
  unfold tailWord_1231870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5616248755894106436421633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29953326698101900994248709 5616248755894106436421633)
  ·
    refine ⟨4212186566920579827316225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5616248755894106436421633 4212186566920579827316225)
    ·
      refine ⟨3159139925190434870487169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4212186566920579827316225 3159139925190434870487169)
      ·
        refine ⟨2369354943892826152865377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3159139925190434870487169 2369354943892826152865377)
        ·
          refine ⟨1777016207919619614649033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2369354943892826152865377 1777016207919619614649033)
          ·
            refine ⟨1332762155939714710986775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1777016207919619614649033 1332762155939714710986775)
            ·
              refine ⟨1999143233909572066480163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1332762155939714710986775 1999143233909572066480163)
              ·
                refine ⟨2998714850864358099720245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1999143233909572066480163 2998714850864358099720245)
                ·
                  refine ⟨281129517268533571848773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2998714850864358099720245 281129517268533571848773)
                  ·
                    rfl

theorem cell21_1231870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_1231870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231870 prefixEnd_1231870 := by exact prefixLift 1231870
  have htrace : WordTrace (prefixWord ++ tailWord_1231870) baseStart_1231870 baseEnd_1231870 := by
    simpa [prefixWord, tailWord_1231870, baseEnd_1231870] using wordTrace_append hprefix tailTrace_1231870
  have hstable : (prefixWord ++ tailWord_1231870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231870).length < 2 ^ (prefixWord ++ tailWord_1231870).sum := by decide
  have hdescent : baseEnd_1231870 < baseStart_1231870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231884 : List Nat := [2, 2, 1, 2, 3, 4, 2, 1, 4]
def baseStart_1231884 : Nat := 118140960795 + 1231884 * 2 ^ 59
def prefixEnd_1231884 : Nat := 4983230072969 + 3 ^ 40 * 1231884 * 2
def baseEnd_1231884 : Nat := 281132712259272658615411

theorem tailTrace_1231884 : CollatzResearch.WordTrace tailWord_1231884 prefixEnd_1231884 281132712259272658615411 := by
  unfold tailWord_1231884
  simp only [CollatzResearch.WordTrace]
  refine ⟨22465250334551065941191353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29953667112734754588255137 22465250334551065941191353)
  ·
    refine ⟨16848937750913299455893515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22465250334551065941191353 16848937750913299455893515)
    ·
      refine ⟨25273406626369949183840273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16848937750913299455893515 25273406626369949183840273)
      ·
        refine ⟨18955054969777461887880205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25273406626369949183840273 18955054969777461887880205)
        ·
          refine ⟨7108145613666548207955077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18955054969777461887880205 7108145613666548207955077)
          ·
            refine ⟨1332777302562477788991577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7108145613666548207955077 1332777302562477788991577)
            ·
              refine ⟨999582976921858341743683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1332777302562477788991577 999582976921858341743683)
              ·
                refine ⟨1499374465382787512615525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 999582976921858341743683 1499374465382787512615525)
                ·
                  refine ⟨281132712259272658615411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1499374465382787512615525 281132712259272658615411)
                  ·
                    rfl

theorem cell21_1231884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_1231884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231884 prefixEnd_1231884 := by exact prefixLift 1231884
  have htrace : WordTrace (prefixWord ++ tailWord_1231884) baseStart_1231884 baseEnd_1231884 := by
    simpa [prefixWord, tailWord_1231884, baseEnd_1231884] using wordTrace_append hprefix tailTrace_1231884
  have hstable : (prefixWord ++ tailWord_1231884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231884).length < 2 ^ (prefixWord ++ tailWord_1231884).sum := by decide
  have hdescent : baseEnd_1231884 < baseStart_1231884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231929 : List Nat := [1, 2, 1, 5, 2, 2, 1, 4, 3]
def baseStart_1231929 : Nat := 118140960795 + 1231929 * 2 ^ 59
def prefixEnd_1231929 : Nat := 4983230072969 + 3 ^ 40 * 1231929 * 2
def baseEnd_1231929 : Nat := 281142981872362580365319

theorem tailTrace_1231929 : CollatzResearch.WordTrace tailWord_1231929 prefixEnd_1231929 281142981872362580365319 := by
  unfold tailWord_1231929
  simp only [CollatzResearch.WordTrace]
  refine ⟨44932141953939104567770841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29954761302626069711847227 44932141953939104567770841)
  ·
    refine ⟨33699106465454328425828131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44932141953939104567770841 33699106465454328425828131)
    ·
      refine ⟨50548659698181492638742197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33699106465454328425828131 50548659698181492638742197)
      ·
        refine ⟨4738936846704514934882081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50548659698181492638742197 4738936846704514934882081)
        ·
          refine ⟨3554202635028386201161561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4738936846704514934882081 3554202635028386201161561)
          ·
            refine ⟨2665651976271289650871171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3554202635028386201161561 2665651976271289650871171)
            ·
              refine ⟨3998477964406934476306757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2665651976271289650871171 3998477964406934476306757)
              ·
                refine ⟨749714618326300214307517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3998477964406934476306757 749714618326300214307517)
                ·
                  refine ⟨281142981872362580365319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 749714618326300214307517 281142981872362580365319)
                  ·
                    rfl

theorem cell21_1231929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 3].length) (baseStart_1231929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231929 prefixEnd_1231929 := by exact prefixLift 1231929
  have htrace : WordTrace (prefixWord ++ tailWord_1231929) baseStart_1231929 baseEnd_1231929 := by
    simpa [prefixWord, tailWord_1231929, baseEnd_1231929] using wordTrace_append hprefix tailTrace_1231929
  have hstable : (prefixWord ++ tailWord_1231929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231929).length < 2 ^ (prefixWord ++ tailWord_1231929).sum := by decide
  have hdescent : baseEnd_1231929 < baseStart_1231929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231957 : List Nat := [1, 3, 2, 2, 1, 2, 5, 5]
def baseStart_1231957 : Nat := 118140960795 + 1231957 * 2 ^ 59
def prefixEnd_1231957 : Nat := 4983230072969 + 3 ^ 40 * 1231957 * 2
def baseEnd_1231957 : Nat := 93716457284613584632865

theorem tailTrace_1231957 : CollatzResearch.WordTrace tailWord_1231957 prefixEnd_1231957 93716457284613584632865 := by
  unfold tailWord_1231957
  simp only [CollatzResearch.WordTrace]
  refine ⟨44933163197837665349790125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29955442131891776899860083 44933163197837665349790125)
  ·
    refine ⟨16849936199189124506171297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44933163197837665349790125 16849936199189124506171297)
    ·
      refine ⟨12637452149391843379628473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16849936199189124506171297 12637452149391843379628473)
      ·
        refine ⟨9478089112043882534721355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12637452149391843379628473 9478089112043882534721355)
        ·
          refine ⟨14217133668065823802082033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9478089112043882534721355 14217133668065823802082033)
          ·
            refine ⟨10662850251049367851561525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14217133668065823802082033 10662850251049367851561525)
            ·
              refine ⟨999642211035878236083893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10662850251049367851561525 999642211035878236083893)
              ·
                refine ⟨93716457284613584632865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 999642211035878236083893 93716457284613584632865)
                ·
                  rfl

theorem cell21_1231957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 5].length) (baseStart_1231957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1231957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1231957 prefixEnd_1231957 := by exact prefixLift 1231957
  have htrace : WordTrace (prefixWord ++ tailWord_1231957) baseStart_1231957 baseEnd_1231957 := by
    simpa [prefixWord, tailWord_1231957, baseEnd_1231957] using wordTrace_append hprefix tailTrace_1231957
  have hstable : (prefixWord ++ tailWord_1231957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231957).length < 2 ^ (prefixWord ++ tailWord_1231957).sum := by decide
  have hdescent : baseEnd_1231957 < baseStart_1231957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232047 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 5]
def baseStart_1232047 : Nat := 118140960795 + 1232047 * 2 ^ 59
def prefixEnd_1232047 : Nat := 4983230072969 + 3 ^ 40 * 1232047 * 2
def baseEnd_1232047 : Nat := 281169911080020597398411

theorem tailTrace_1232047 : CollatzResearch.WordTrace tailWord_1232047 prefixEnd_1232047 281169911080020597398411 := by
  unfold tailWord_1232047
  simp only [CollatzResearch.WordTrace]
  refine ⟨44936445767511610720566395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29957630511674407147044263 44936445767511610720566395)
  ·
    refine ⟨67404668651267416080849593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44936445767511610720566395 67404668651267416080849593)
    ·
      refine ⟨50553501488450562060637195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67404668651267416080849593 50553501488450562060637195)
      ·
        refine ⟨75830252232675843090955793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50553501488450562060637195 75830252232675843090955793)
        ·
          refine ⟨56872689174506882318216845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75830252232675843090955793 56872689174506882318216845)
          ·
            refine ⟨21327258440440080869331317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56872689174506882318216845 21327258440440080869331317)
            ·
              refine ⟨1999430478791257581499811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21327258440440080869331317 1999430478791257581499811)
              ·
                refine ⟨2999145718186886372249717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1999430478791257581499811 2999145718186886372249717)
                ·
                  refine ⟨281169911080020597398411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2999145718186886372249717 281169911080020597398411)
                  ·
                    rfl

theorem cell21_1232047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 5].length) (baseStart_1232047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232047 prefixEnd_1232047 := by exact prefixLift 1232047
  have htrace : WordTrace (prefixWord ++ tailWord_1232047) baseStart_1232047 baseEnd_1232047 := by
    simpa [prefixWord, tailWord_1232047, baseEnd_1232047] using wordTrace_append hprefix tailTrace_1232047
  have hstable : (prefixWord ++ tailWord_1232047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232047).length < 2 ^ (prefixWord ++ tailWord_1232047).sum := by decide
  have hdescent : baseEnd_1232047 < baseStart_1232047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232092 : List Nat := [2, 2, 5, 12]
def baseStart_1232092 : Nat := 118140960795 + 1232092 * 2 ^ 59
def prefixEnd_1232092 : Nat := 4983230072969 + 3 ^ 40 * 1232092 * 2
def baseEnd_1232092 : Nat := 1157120085156833412133

theorem tailTrace_1232092 : CollatzResearch.WordTrace tailWord_1232092 prefixEnd_1232092 1157120085156833412133 := by
  unfold tailWord_1232092
  simp only [CollatzResearch.WordTrace]
  refine ⟨22469043526174291702977265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29958724701565722270636353 22469043526174291702977265)
  ·
    refine ⟨16851782644630718777232949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22469043526174291702977265 16851782644630718777232949)
    ·
      refine ⟨1579854622934129885365589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16851782644630718777232949 1579854622934129885365589)
      ·
        refine ⟨1157120085156833412133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1579854622934129885365589 1157120085156833412133)
        ·
          rfl

theorem cell21_1232092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 12].length) (baseStart_1232092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232092 prefixEnd_1232092 := by exact prefixLift 1232092
  have htrace : WordTrace (prefixWord ++ tailWord_1232092) baseStart_1232092 baseEnd_1232092 := by
    simpa [prefixWord, tailWord_1232092, baseEnd_1232092] using wordTrace_append hprefix tailTrace_1232092
  have hstable : (prefixWord ++ tailWord_1232092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232092).length < 2 ^ (prefixWord ++ tailWord_1232092).sum := by decide
  have hdescent : baseEnd_1232092 < baseStart_1232092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232109 : List Nat := [1, 5, 1, 2, 2, 1, 3, 6]
def baseStart_1232109 : Nat := 118140960795 + 1232109 * 2 ^ 59
def prefixEnd_1232109 : Nat := 4983230072969 + 3 ^ 40 * 1232109 * 2
def baseEnd_1232109 : Nat := 93728020108240755788317

theorem tailTrace_1232109 : CollatzResearch.WordTrace tailWord_1232109 prefixEnd_1232109 93728020108240755788317 := by
  unfold tailWord_1232109
  simp only [CollatzResearch.WordTrace]
  refine ⟨44938707093286995309323381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29959138062191330206215587 44938707093286995309323381)
  ·
    refine ⟨4213003789995655810249067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44938707093286995309323381 4213003789995655810249067)
    ·
      refine ⟨6319505684993483715373601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4213003789995655810249067 6319505684993483715373601)
      ·
        refine ⟨4739629263745112786530201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6319505684993483715373601 4739629263745112786530201)
        ·
          refine ⟨3554721947808834589897651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4739629263745112786530201 3554721947808834589897651)
          ·
            refine ⟨5332082921713251884846477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3554721947808834589897651 5332082921713251884846477)
            ·
              refine ⟨1999531095642469456817429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5332082921713251884846477 1999531095642469456817429)
              ·
                refine ⟨93728020108240755788317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1999531095642469456817429 93728020108240755788317)
                ·
                  rfl

theorem cell21_1232109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 6].length) (baseStart_1232109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232109 prefixEnd_1232109 := by exact prefixLift 1232109
  have htrace : WordTrace (prefixWord ++ tailWord_1232109) baseStart_1232109 baseEnd_1232109 := by
    simpa [prefixWord, tailWord_1232109, baseEnd_1232109] using wordTrace_append hprefix tailTrace_1232109
  have hstable : (prefixWord ++ tailWord_1232109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232109).length < 2 ^ (prefixWord ++ tailWord_1232109).sum := by decide
  have hdescent : baseEnd_1232109 < baseStart_1232109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232126 : List Nat := [4, 2, 2, 1, 1, 3, 3, 5]
def baseStart_1232126 : Nat := 118140960795 + 1232126 * 2 ^ 59
def prefixEnd_1232126 : Nat := 4983230072969 + 3 ^ 40 * 1232126 * 2
def baseEnd_1232126 : Nat := 93729313318778005193861

theorem tailTrace_1232126 : CollatzResearch.WordTrace tailWord_1232126 prefixEnd_1232126 93729313318778005193861 := by
  unfold tailWord_1232126
  simp only [CollatzResearch.WordTrace]
  refine ⟨5617415891778175901586529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29959551422816938141794821 5617415891778175901586529)
  ·
    refine ⟨4213061918833631926189897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5617415891778175901586529 4213061918833631926189897)
    ·
      refine ⟨3159796439125223944642423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4213061918833631926189897 3159796439125223944642423)
      ·
        refine ⟨4739694658687835916963635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3159796439125223944642423 4739694658687835916963635)
        ·
          refine ⟨7109541988031753875445453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4739694658687835916963635 7109541988031753875445453)
          ·
            refine ⟨2666078245511907703292045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7109541988031753875445453 2666078245511907703292045)
            ·
              refine ⟨999779342066965388734517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2666078245511907703292045 999779342066965388734517)
              ·
                refine ⟨93729313318778005193861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 999779342066965388734517 93729313318778005193861)
                ·
                  rfl

theorem cell21_1232126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_1232126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232126 prefixEnd_1232126 := by exact prefixLift 1232126
  have htrace : WordTrace (prefixWord ++ tailWord_1232126) baseStart_1232126 baseEnd_1232126 := by
    simpa [prefixWord, tailWord_1232126, baseEnd_1232126] using wordTrace_append hprefix tailTrace_1232126
  have hstable : (prefixWord ++ tailWord_1232126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232126).length < 2 ^ (prefixWord ++ tailWord_1232126).sum := by decide
  have hdescent : baseEnd_1232126 < baseStart_1232126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232137 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 6]
def baseStart_1232137 : Nat := 118140960795 + 1232137 * 2 ^ 59
def prefixEnd_1232137 : Nat := 4983230072969 + 3 ^ 40 * 1232137 * 2
def baseEnd_1232137 : Nat := 281190450306200440898227

theorem tailTrace_1232137 : CollatzResearch.WordTrace tailWord_1232137 prefixEnd_1232137 281190450306200440898227 := by
  unfold tailWord_1232137
  simp only [CollatzResearch.WordTrace]
  refine ⟨44939728337185556091342665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29959818891457037394228443 44939728337185556091342665)
  ·
    refine ⟨33704796252889167068506999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44939728337185556091342665 33704796252889167068506999)
    ·
      refine ⟨50557194379333750602760499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33704796252889167068506999 50557194379333750602760499)
      ·
        refine ⟨75835791569000625904140749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50557194379333750602760499 75835791569000625904140749)
        ·
          refine ⟨28438421838375234714052781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75835791569000625904140749 28438421838375234714052781)
          ·
            refine ⟨10664408189390713017769793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28438421838375234714052781 10664408189390713017769793)
            ·
              refine ⟨7998306142043034763327345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10664408189390713017769793 7998306142043034763327345)
              ·
                refine ⟨5998729606532276072495509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7998306142043034763327345 5998729606532276072495509)
                ·
                  refine ⟨281190450306200440898227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5998729606532276072495509 281190450306200440898227)
                  ·
                    rfl

theorem cell21_1232137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_1232137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232137 prefixEnd_1232137 := by exact prefixLift 1232137
  have htrace : WordTrace (prefixWord ++ tailWord_1232137) baseStart_1232137 baseEnd_1232137 := by
    simpa [prefixWord, tailWord_1232137, baseEnd_1232137] using wordTrace_append hprefix tailTrace_1232137
  have hstable : (prefixWord ++ tailWord_1232137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232137).length < 2 ^ (prefixWord ++ tailWord_1232137).sum := by decide
  have hdescent : baseEnd_1232137 < baseStart_1232137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232140 : List Nat := [2, 2, 1, 2, 2, 3, 1, 5, 3]
def baseStart_1232140 : Nat := 118140960795 + 1232140 * 2 ^ 59
def prefixEnd_1232140 : Nat := 4983230072969 + 3 ^ 40 * 1232140 * 2
def baseEnd_1232140 : Nat := 281191134947073102348221

theorem tailTrace_1232140 : CollatzResearch.WordTrace tailWord_1232140 prefixEnd_1232140 281191134947073102348221 := by
  unfold tailWord_1232140
  simp only [CollatzResearch.WordTrace]
  refine ⟨22469918878087343801850937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29959891837449791735801249 22469918878087343801850937)
  ·
    refine ⟨16852439158565507851388203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22469918878087343801850937 16852439158565507851388203)
    ·
      refine ⟨25278658737848261777082305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16852439158565507851388203 25278658737848261777082305)
      ·
        refine ⟨18958994053386196332811729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25278658737848261777082305 18958994053386196332811729)
        ·
          refine ⟨14219245540039647249608797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18958994053386196332811729 14219245540039647249608797)
          ·
            refine ⟨5332217077514867718603299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14219245540039647249608797 5332217077514867718603299)
            ·
              refine ⟨7998325616272301577904949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5332217077514867718603299 7998325616272301577904949)
              ·
                refine ⟨749843026525528272928589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7998325616272301577904949 749843026525528272928589)
                ·
                  refine ⟨281191134947073102348221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 749843026525528272928589 281191134947073102348221)
                  ·
                    rfl

theorem cell21_1232140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_1232140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232140 prefixEnd_1232140 := by exact prefixLift 1232140
  have htrace : WordTrace (prefixWord ++ tailWord_1232140) baseStart_1232140 baseEnd_1232140 := by
    simpa [prefixWord, tailWord_1232140, baseEnd_1232140] using wordTrace_append hprefix tailTrace_1232140
  have hstable : (prefixWord ++ tailWord_1232140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232140).length < 2 ^ (prefixWord ++ tailWord_1232140).sum := by decide
  have hdescent : baseEnd_1232140 < baseStart_1232140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232146 : List Nat := [3, 2, 4, 2, 2, 1, 1, 2, 4]
def baseStart_1232146 : Nat := 118140960795 + 1232146 * 2 ^ 59
def prefixEnd_1232146 : Nat := 4983230072969 + 3 ^ 40 * 1232146 * 2
def baseEnd_1232146 : Nat := 281192504228818425248209

theorem tailTrace_1232146 : CollatzResearch.WordTrace tailWord_1232146 prefixEnd_1232146 281192504228818425248209 := by
  unfold tailWord_1232146
  simp only [CollatzResearch.WordTrace]
  refine ⟨11235014148538237657105073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29960037729435300418946861 11235014148538237657105073)
  ·
    refine ⟨8426260611403678242828805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11235014148538237657105073 8426260611403678242828805)
    ·
      refine ⟨1579923864638189670530401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8426260611403678242828805 1579923864638189670530401)
      ·
        refine ⟨1184942898478642252897801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1579923864638189670530401 1184942898478642252897801)
        ·
          refine ⟨888707173858981689673351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1184942898478642252897801 888707173858981689673351)
          ·
            refine ⟨1333060760788472534510027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888707173858981689673351 1333060760788472534510027)
            ·
              refine ⟨1999591141182708801765041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333060760788472534510027 1999591141182708801765041)
              ·
                refine ⟨1499693355887031601323781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1999591141182708801765041 1499693355887031601323781)
                ·
                  refine ⟨281192504228818425248209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1499693355887031601323781 281192504228818425248209)
                  ·
                    rfl

theorem cell21_1232146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_1232146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232146 prefixEnd_1232146 := by exact prefixLift 1232146
  have htrace : WordTrace (prefixWord ++ tailWord_1232146) baseStart_1232146 baseEnd_1232146 := by
    simpa [prefixWord, tailWord_1232146, baseEnd_1232146] using wordTrace_append hprefix tailTrace_1232146
  have hstable : (prefixWord ++ tailWord_1232146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232146).length < 2 ^ (prefixWord ++ tailWord_1232146).sum := by decide
  have hdescent : baseEnd_1232146 < baseStart_1232146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232154 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 6]
def baseStart_1232154 : Nat := 118140960795 + 1232154 * 2 ^ 59
def prefixEnd_1232154 : Nat := 4983230072969 + 3 ^ 40 * 1232154 * 2
def baseEnd_1232154 : Nat := 281194329937812189114859

theorem tailTrace_1232154 : CollatzResearch.WordTrace tailWord_1232154 prefixEnd_1232154 281194329937812189114859 := by
  unfold tailWord_1232154
  simp only [CollatzResearch.WordTrace]
  refine ⟨11235087094530991998677879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29960232252082645329807677 11235087094530991998677879)
  ·
    refine ⟨16852630641796487998016819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11235087094530991998677879 16852630641796487998016819)
    ·
      refine ⟨25278945962694731997025229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16852630641796487998016819 25278945962694731997025229)
      ·
        refine ⟨9479604736010524498884461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25278945962694731997025229 9479604736010524498884461)
        ·
          refine ⟨3554851776003946687081673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9479604736010524498884461 3554851776003946687081673)
          ·
            refine ⟨2666138832002960015311255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3554851776003946687081673 2666138832002960015311255)
            ·
              refine ⟨3999208248004440022966883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2666138832002960015311255 3999208248004440022966883)
              ·
                refine ⟨5998812372006660034450325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3999208248004440022966883 5998812372006660034450325)
                ·
                  refine ⟨281194329937812189114859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5998812372006660034450325 281194329937812189114859)
                  ·
                    rfl

theorem cell21_1232154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_1232154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232154 prefixEnd_1232154 := by exact prefixLift 1232154
  have htrace : WordTrace (prefixWord ++ tailWord_1232154) baseStart_1232154 baseEnd_1232154 := by
    simpa [prefixWord, tailWord_1232154, baseEnd_1232154] using wordTrace_append hprefix tailTrace_1232154
  have hstable : (prefixWord ++ tailWord_1232154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232154).length < 2 ^ (prefixWord ++ tailWord_1232154).sum := by decide
  have hdescent : baseEnd_1232154 < baseStart_1232154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232157 : List Nat := [1, 4, 2, 3, 1, 1, 2, 4, 3]
def baseStart_1232157 : Nat := 118140960795 + 1232157 * 2 ^ 59
def prefixEnd_1232157 : Nat := 4983230072969 + 3 ^ 40 * 1232157 * 2
def baseEnd_1232157 : Nat := 281195014578684850564853

theorem tailTrace_1232157 : CollatzResearch.WordTrace tailWord_1232157 prefixEnd_1232157 281195014578684850564853 := by
  unfold tailWord_1232157
  simp only [CollatzResearch.WordTrace]
  refine ⟨44940457797113099507070725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29960305198075399671380483 44940457797113099507070725)
  ·
    refine ⟨8426335836958706157575761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44940457797113099507070725 8426335836958706157575761)
    ·
      refine ⟨6319751877719029618181821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8426335836958706157575761 6319751877719029618181821)
      ·
        refine ⟨2369906954144636106818183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6319751877719029618181821 2369906954144636106818183)
        ·
          refine ⟨3554860431216954160227275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2369906954144636106818183 3554860431216954160227275)
          ·
            refine ⟨5332290646825431240340913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3554860431216954160227275 5332290646825431240340913)
            ·
              refine ⟨3999217985119073430255685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5332290646825431240340913 3999217985119073430255685)
              ·
                refine ⟨749853372209826268172941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3999217985119073430255685 749853372209826268172941)
                ·
                  refine ⟨281195014578684850564853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 749853372209826268172941 281195014578684850564853)
                  ·
                    rfl

theorem cell21_1232157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_1232157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232157 prefixEnd_1232157 := by exact prefixLift 1232157
  have htrace : WordTrace (prefixWord ++ tailWord_1232157) baseStart_1232157 baseEnd_1232157 := by
    simpa [prefixWord, tailWord_1232157, baseEnd_1232157] using wordTrace_append hprefix tailTrace_1232157
  have hstable : (prefixWord ++ tailWord_1232157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232157).length < 2 ^ (prefixWord ++ tailWord_1232157).sum := by decide
  have hdescent : baseEnd_1232157 < baseStart_1232157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232185 : List Nat := [1, 2, 1, 6, 2, 1, 1, 7]
def baseStart_1232185 : Nat := 118140960795 + 1232185 * 2 ^ 59
def prefixEnd_1232185 : Nat := 4983230072969 + 3 ^ 40 * 1232185 * 2
def baseEnd_1232185 : Nat := 93733801520054341366043

theorem tailTrace_1232185 : CollatzResearch.WordTrace tailWord_1232185 prefixEnd_1232185 93733801520054341366043 := by
  unfold tailWord_1232185
  simp only [CollatzResearch.WordTrace]
  refine ⟨44941479041011660289090009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29960986027341106859393339 44941479041011660289090009)
  ·
    refine ⟨33706109280758745216817507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44941479041011660289090009 33706109280758745216817507)
    ·
      refine ⟨50559163921138117825226261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33706109280758745216817507 50559163921138117825226261)
      ·
        refine ⟨2369960808803349273057481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50559163921138117825226261 2369960808803349273057481)
        ·
          refine ⟨1777470606602511954793111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2369960808803349273057481 1777470606602511954793111)
          ·
            refine ⟨2666205909903767932189667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1777470606602511954793111 2666205909903767932189667)
            ·
              refine ⟨3999308864855651898284501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2666205909903767932189667 3999308864855651898284501)
              ·
                refine ⟨93733801520054341366043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3999308864855651898284501 93733801520054341366043)
                ·
                  rfl

theorem cell21_1232185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 7].length) (baseStart_1232185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232185 prefixEnd_1232185 := by exact prefixLift 1232185
  have htrace : WordTrace (prefixWord ++ tailWord_1232185) baseStart_1232185 baseEnd_1232185 := by
    simpa [prefixWord, tailWord_1232185, baseEnd_1232185] using wordTrace_append hprefix tailTrace_1232185
  have hstable : (prefixWord ++ tailWord_1232185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232185).length < 2 ^ (prefixWord ++ tailWord_1232185).sum := by decide
  have hdescent : baseEnd_1232185 < baseStart_1232185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232303 : List Nat := [1, 1, 2, 1, 2, 2, 1, 11]
def baseStart_1232303 : Nat := 118140960795 + 1232303 * 2 ^ 59
def prefixEnd_1232303 : Nat := 4983230072969 + 3 ^ 40 * 1232303 * 2
def baseEnd_1232303 : Nat := 93742777922607013710407

theorem tailTrace_1232303 : CollatzResearch.WordTrace tailWord_1232303 prefixEnd_1232303 93742777922607013710407 := by
  unfold tailWord_1232303
  simp only [CollatzResearch.WordTrace]
  refine ⟨44945782854584166441885563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29963855236389444294590375 44945782854584166441885563)
  ·
    refine ⟨67418674281876249662828345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44945782854584166441885563 67418674281876249662828345)
    ·
      refine ⟨50564005711407187247121259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67418674281876249662828345 50564005711407187247121259)
      ·
        refine ⟨75846008567110780870681889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50564005711407187247121259 75846008567110780870681889)
        ·
          refine ⟨56884506425333085653011417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75846008567110780870681889 56884506425333085653011417)
          ·
            refine ⟨42663379818999814239758563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56884506425333085653011417 42663379818999814239758563)
            ·
              refine ⟨63995069728499721359637845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42663379818999814239758563 63995069728499721359637845)
              ·
                refine ⟨93742777922607013710407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 63995069728499721359637845 93742777922607013710407)
                ·
                  rfl

theorem cell21_1232303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 11].length) (baseStart_1232303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232303 prefixEnd_1232303 := by exact prefixLift 1232303
  have htrace : WordTrace (prefixWord ++ tailWord_1232303) baseStart_1232303 baseEnd_1232303 := by
    simpa [prefixWord, tailWord_1232303, baseEnd_1232303] using wordTrace_append hprefix tailTrace_1232303
  have hstable : (prefixWord ++ tailWord_1232303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232303).length < 2 ^ (prefixWord ++ tailWord_1232303).sum := by decide
  have hdescent : baseEnd_1232303 < baseStart_1232303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232309 : List Nat := [1, 3, 3, 2, 2, 2, 2, 3, 3]
def baseStart_1232309 : Nat := 118140960795 + 1232309 * 2 ^ 59
def prefixEnd_1232309 : Nat := 4983230072969 + 3 ^ 40 * 1232309 * 2
def baseEnd_1232309 : Nat := 281229703049566364031209

theorem tailTrace_1232309 : CollatzResearch.WordTrace tailWord_1232309 prefixEnd_1232309 281229703049566364031209 := by
  unfold tailWord_1232309
  simp only [CollatzResearch.WordTrace]
  refine ⟨44946001692562429466603981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29964001128374952977735987 44946001692562429466603981)
  ·
    refine ⟨16854750634710911049976493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44946001692562429466603981 16854750634710911049976493)
    ·
      refine ⟨6320531488016591643741185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16854750634710911049976493 6320531488016591643741185)
      ·
        refine ⟨4740398616012443732805889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6320531488016591643741185 4740398616012443732805889)
        ·
          refine ⟨3555298962009332799604417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4740398616012443732805889 3555298962009332799604417)
          ·
            refine ⟨2666474221506999599703313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3555298962009332799604417 2666474221506999599703313)
            ·
              refine ⟨1999855666130249699777485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2666474221506999599703313 1999855666130249699777485)
              ·
                refine ⟨749945874798843637416557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1999855666130249699777485 749945874798843637416557)
                ·
                  refine ⟨281229703049566364031209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 749945874798843637416557 281229703049566364031209)
                  ·
                    rfl

theorem cell21_1232309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_1232309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232309 prefixEnd_1232309 := by exact prefixLift 1232309
  have htrace : WordTrace (prefixWord ++ tailWord_1232309) baseStart_1232309 baseEnd_1232309 := by
    simpa [prefixWord, tailWord_1232309, baseEnd_1232309] using wordTrace_append hprefix tailTrace_1232309
  have hstable : (prefixWord ++ tailWord_1232309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232309).length < 2 ^ (prefixWord ++ tailWord_1232309).sum := by decide
  have hdescent : baseEnd_1232309 < baseStart_1232309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232340 : List Nat := [2, 4, 1, 2, 3, 1, 3, 1, 4]
def baseStart_1232340 : Nat := 118140960795 + 1232340 * 2 ^ 59
def prefixEnd_1232340 : Nat := 4983230072969 + 3 ^ 40 * 1232340 * 2
def baseEnd_1232340 : Nat := 281236777671917199014479

theorem tailTrace_1232340 : CollatzResearch.WordTrace tailWord_1232340 prefixEnd_1232340 281236777671917199014479 := by
  unfold tailWord_1232340
  simp only [CollatzResearch.WordTrace]
  refine ⟨22473566177725060880491237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29964754903633414507321649 22473566177725060880491237)
  ·
    refine ⟨4213793658323448915092107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22473566177725060880491237 4213793658323448915092107)
    ·
      refine ⟨6320690487485173372638161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4213793658323448915092107 6320690487485173372638161)
      ·
        refine ⟨4740517865613880029478621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6320690487485173372638161 4740517865613880029478621)
        ·
          refine ⟨1777694199605205011054483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4740517865613880029478621 1777694199605205011054483)
          ·
            refine ⟨2666541299407807516581725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1777694199605205011054483 2666541299407807516581725)
            ·
              refine ⟨999952987277927818718147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2666541299407807516581725 999952987277927818718147)
              ·
                refine ⟨1499929480916891728077221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 999952987277927818718147 1499929480916891728077221)
                ·
                  refine ⟨281236777671917199014479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1499929480916891728077221 281236777671917199014479)
                  ·
                    rfl

theorem cell21_1232340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_1232340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232340 prefixEnd_1232340 := by exact prefixLift 1232340
  have htrace : WordTrace (prefixWord ++ tailWord_1232340) baseStart_1232340 baseEnd_1232340 := by
    simpa [prefixWord, tailWord_1232340, baseEnd_1232340] using wordTrace_append hprefix tailTrace_1232340
  have hstable : (prefixWord ++ tailWord_1232340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232340).length < 2 ^ (prefixWord ++ tailWord_1232340).sum := by decide
  have hdescent : baseEnd_1232340 < baseStart_1232340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232368 : List Nat := [2, 1, 1, 1, 3, 4, 3, 3, 3]
def baseStart_1232368 : Nat := 118140960795 + 1232368 * 2 ^ 59
def prefixEnd_1232368 : Nat := 4983230072969 + 3 ^ 40 * 1232368 * 2
def baseEnd_1232368 : Nat := 281243167653395372547755

theorem tailTrace_1232368 : CollatzResearch.WordTrace tailWord_1232368 prefixEnd_1232368 281243167653395372547755 := by
  unfold tailWord_1232368
  simp only [CollatzResearch.WordTrace]
  refine ⟨22474076799674341271500879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29965435732899121695334505 22474076799674341271500879)
  ·
    refine ⟨33711115199511511907251319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22474076799674341271500879 33711115199511511907251319)
    ·
      refine ⟨50566672799267267860876979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33711115199511511907251319 50566672799267267860876979)
      ·
        refine ⟨75850009198900901791315469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50566672799267267860876979 75850009198900901791315469)
        ·
          refine ⟨28443753449587838171743301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75850009198900901791315469 28443753449587838171743301)
          ·
            refine ⟨5333203771797719657201869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28443753449587838171743301 5333203771797719657201869)
            ·
              refine ⟨1999951414424144871450701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5333203771797719657201869 1999951414424144871450701)
              ·
                refine ⟨749981780409054326794013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1999951414424144871450701 749981780409054326794013)
                ·
                  refine ⟨281243167653395372547755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 749981780409054326794013 281243167653395372547755)
                  ·
                    rfl

theorem cell21_1232368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 3].length) (baseStart_1232368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232368 prefixEnd_1232368 := by exact prefixLift 1232368
  have htrace : WordTrace (prefixWord ++ tailWord_1232368) baseStart_1232368 baseEnd_1232368 := by
    simpa [prefixWord, tailWord_1232368, baseEnd_1232368] using wordTrace_append hprefix tailTrace_1232368
  have hstable : (prefixWord ++ tailWord_1232368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232368).length < 2 ^ (prefixWord ++ tailWord_1232368).sum := by decide
  have hdescent : baseEnd_1232368 < baseStart_1232368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232385 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 5]
def baseStart_1232385 : Nat := 118140960795 + 1232385 * 2 ^ 59
def prefixEnd_1232385 : Nat := 4983230072969 + 3 ^ 40 * 1232385 * 2
def baseEnd_1232385 : Nat := 281247047285007120764387

theorem tailTrace_1232385 : CollatzResearch.WordTrace tailWord_1232385 prefixEnd_1232385 281247047285007120764387 := by
  unfold tailWord_1232385
  simp only [CollatzResearch.WordTrace]
  refine ⟨44948773640287094446370609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29965849093524729630913739 44948773640287094446370609)
  ·
    refine ⟨33711580230215320834777957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44948773640287094446370609 33711580230215320834777957)
    ·
      refine ⟨6320921293165372656520867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33711580230215320834777957 6320921293165372656520867)
      ·
        refine ⟨9481381939748058984781301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6320921293165372656520867 9481381939748058984781301)
        ·
          refine ⟨888879556851380529823247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9481381939748058984781301 888879556851380529823247)
          ·
            refine ⟨1333319335277070794734871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888879556851380529823247 1333319335277070794734871)
            ·
              refine ⟨1999979002915606192102307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333319335277070794734871 1999979002915606192102307)
              ·
                refine ⟨2999968504373409288153461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1999979002915606192102307 2999968504373409288153461)
                ·
                  refine ⟨281247047285007120764387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2999968504373409288153461 281247047285007120764387)
                  ·
                    rfl

theorem cell21_1232385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 5].length) (baseStart_1232385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232385 prefixEnd_1232385 := by exact prefixLift 1232385
  have htrace : WordTrace (prefixWord ++ tailWord_1232385) baseStart_1232385 baseEnd_1232385 := by
    simpa [prefixWord, tailWord_1232385, baseEnd_1232385] using wordTrace_append hprefix tailTrace_1232385
  have hstable : (prefixWord ++ tailWord_1232385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232385).length < 2 ^ (prefixWord ++ tailWord_1232385).sum := by decide
  have hdescent : baseEnd_1232385 < baseStart_1232385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232410 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 7]
def baseStart_1232410 : Nat := 118140960795 + 1232410 * 2 ^ 59
def prefixEnd_1232410 : Nat := 4983230072969 + 3 ^ 40 * 1232410 * 2
def baseEnd_1232410 : Nat := 281252752625612632847669

theorem tailTrace_1232410 : CollatzResearch.WordTrace tailWord_1232410 prefixEnd_1232410 281252752625612632847669 := by
  unfold tailWord_1232410
  simp only [CollatzResearch.WordTrace]
  refine ⟨11237421366299130929007671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29966456976797682477353789 11237421366299130929007671)
  ·
    refine ⟨16856132049448696393511507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11237421366299130929007671 16856132049448696393511507)
    ·
      refine ⟨25284198074173044590267261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16856132049448696393511507 25284198074173044590267261)
      ·
        refine ⟨9481574277814891721350223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25284198074173044590267261 9481574277814891721350223)
        ·
          refine ⟨14222361416722337582025335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9481574277814891721350223 14222361416722337582025335)
          ·
            refine ⟨21333542125083506373038003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14222361416722337582025335 21333542125083506373038003)
            ·
              refine ⟨32000313187625259559557005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21333542125083506373038003 32000313187625259559557005)
              ·
                refine ⟨12000117445359472334833877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32000313187625259559557005 12000117445359472334833877)
                ·
                  refine ⟨281252752625612632847669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12000117445359472334833877 281252752625612632847669)
                  ·
                    rfl

theorem cell21_1232410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_1232410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232410 prefixEnd_1232410 := by exact prefixLift 1232410
  have htrace : WordTrace (prefixWord ++ tailWord_1232410) baseStart_1232410 baseEnd_1232410 := by
    simpa [prefixWord, tailWord_1232410, baseEnd_1232410] using wordTrace_append hprefix tailTrace_1232410
  have hstable : (prefixWord ++ tailWord_1232410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232410).length < 2 ^ (prefixWord ++ tailWord_1232410).sum := by decide
  have hdescent : baseEnd_1232410 < baseStart_1232410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232548 : List Nat := [2, 3, 1, 2, 2, 4, 7]
def baseStart_1232548 : Nat := 118140960795 + 1232548 * 2 ^ 59
def prefixEnd_1232548 : Nat := 4983230072969 + 3 ^ 40 * 1232548 * 2
def baseEnd_1232548 : Nat := 31253805122861673283043

theorem tailTrace_1232548 : CollatzResearch.WordTrace tailWord_1232548 prefixEnd_1232548 31253805122861673283043 := by
  unfold tailWord_1232548
  simp only [CollatzResearch.WordTrace]
  refine ⟨22477359369348286642277149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29969812492464382189702865 22477359369348286642277149)
  ·
    refine ⟨8429009763505607490853931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22477359369348286642277149 8429009763505607490853931)
    ·
      refine ⟨12643514645258411236280897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8429009763505607490853931 12643514645258411236280897)
      ·
        refine ⟨9482635983943808427210673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12643514645258411236280897 9482635983943808427210673)
        ·
          refine ⟨7111976987957856320408005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9482635983943808427210673 7111976987957856320408005)
          ·
            refine ⟨1333495685242098060076501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7111976987957856320408005 1333495685242098060076501)
            ·
              refine ⟨31253805122861673283043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1333495685242098060076501 31253805122861673283043)
              ·
                rfl

theorem cell21_1232548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 7].length) (baseStart_1232548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232548 prefixEnd_1232548 := by exact prefixLift 1232548
  have htrace : WordTrace (prefixWord ++ tailWord_1232548) baseStart_1232548 baseEnd_1232548 := by
    simpa [prefixWord, tailWord_1232548, baseEnd_1232548] using wordTrace_append hprefix tailTrace_1232548
  have hstable : (prefixWord ++ tailWord_1232548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232548).length < 2 ^ (prefixWord ++ tailWord_1232548).sum := by decide
  have hdescent : baseEnd_1232548 < baseStart_1232548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232565 : List Nat := [1, 3, 3, 3, 2, 1, 2, 6]
def baseStart_1232565 : Nat := 118140960795 + 1232565 * 2 ^ 59
def prefixEnd_1232565 : Nat := 4983230072969 + 3 ^ 40 * 1232565 * 2
def baseEnd_1232565 : Nat := 93762708579122269254673

theorem tailTrace_1232565 : CollatzResearch.WordTrace tailWord_1232565 prefixEnd_1232565 93762708579122269254673 := by
  unfold tailWord_1232565
  simp only [CollatzResearch.WordTrace]
  refine ⟨44955338779634985187923149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29970225853089990125282099 44955338779634985187923149)
  ·
    refine ⟨16858252042363119445471181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44955338779634985187923149 16858252042363119445471181)
    ·
      refine ⟨6321844515886169792051693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16858252042363119445471181 6321844515886169792051693)
      ·
        refine ⟨2370691693457313672019385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6321844515886169792051693 2370691693457313672019385)
        ·
          refine ⟨1778018770092985254014539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2370691693457313672019385 1778018770092985254014539)
          ·
            refine ⟨2667028155139477881021809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1778018770092985254014539 2667028155139477881021809)
            ·
              refine ⟨2000271116354608410766357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2667028155139477881021809 2000271116354608410766357)
              ·
                refine ⟨93762708579122269254673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2000271116354608410766357 93762708579122269254673)
                ·
                  rfl

theorem cell21_1232565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 6].length) (baseStart_1232565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232565 prefixEnd_1232565 := by exact prefixLift 1232565
  have htrace : WordTrace (prefixWord ++ tailWord_1232565) baseStart_1232565 baseEnd_1232565 := by
    simpa [prefixWord, tailWord_1232565, baseEnd_1232565] using wordTrace_append hprefix tailTrace_1232565
  have hstable : (prefixWord ++ tailWord_1232565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232565).length < 2 ^ (prefixWord ++ tailWord_1232565).sum := by decide
  have hdescent : baseEnd_1232565 < baseStart_1232565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232582 : List Nat := [6, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1232582 : Nat := 118140960795 + 1232582 * 2 ^ 59
def prefixEnd_1232582 : Nat := 4983230072969 + 3 ^ 40 * 1232582 * 2
def baseEnd_1232582 : Nat := 93764001789659518660217

theorem tailTrace_1232582 : CollatzResearch.WordTrace tailWord_1232582 prefixEnd_1232582 93764001789659518660217 := by
  unfold tailWord_1232582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1404873713142918659102875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29970639213715598060861333 1404873713142918659102875)
  ·
    refine ⟨2107310569714377988654313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1404873713142918659102875 2107310569714377988654313)
    ·
      refine ⟨1580482927285783491490735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2107310569714377988654313 1580482927285783491490735)
      ·
        refine ⟨2370724390928675237236103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1580482927285783491490735 2370724390928675237236103)
        ·
          refine ⟨3556086586393012855854155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2370724390928675237236103 3556086586393012855854155)
          ·
            refine ⟨5334129879589519283781233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3556086586393012855854155 5334129879589519283781233)
            ·
              refine ⟨4000597409692139462835925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5334129879589519283781233 4000597409692139462835925)
              ·
                refine ⟨93764001789659518660217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4000597409692139462835925 93764001789659518660217)
                ·
                  rfl

theorem cell21_1232582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1232582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232582 prefixEnd_1232582 := by exact prefixLift 1232582
  have htrace : WordTrace (prefixWord ++ tailWord_1232582) baseStart_1232582 baseEnd_1232582 := by
    simpa [prefixWord, tailWord_1232582, baseEnd_1232582] using wordTrace_append hprefix tailTrace_1232582
  have hstable : (prefixWord ++ tailWord_1232582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232582).length < 2 ^ (prefixWord ++ tailWord_1232582).sum := by decide
  have hdescent : baseEnd_1232582 < baseStart_1232582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232700 : List Nat := [2, 2, 2, 2, 1, 1, 6, 5]
def baseStart_1232700 : Nat := 118140960795 + 1232700 * 2 ^ 59
def prefixEnd_1232700 : Nat := 4983230072969 + 3 ^ 40 * 1232700 * 2
def baseEnd_1232700 : Nat := 93772978192212191004581

theorem tailTrace_1232700 : CollatzResearch.WordTrace tailWord_1232700 prefixEnd_1232700 93772978192212191004581 := by
  unfold tailWord_1232700
  simp only [CollatzResearch.WordTrace]
  refine ⟨22480131317072951622043777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29973508422763935496058369 22480131317072951622043777)
  ·
    refine ⟨16860098487804713716532833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22480131317072951622043777 16860098487804713716532833)
    ·
      refine ⟨12645073865853535287399625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16860098487804713716532833 12645073865853535287399625)
      ·
        refine ⟨9483805399390151465549719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12645073865853535287399625 9483805399390151465549719)
        ·
          refine ⟨14225708099085227198324579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9483805399390151465549719 14225708099085227198324579)
          ·
            refine ⟨21338562148627840797486869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14225708099085227198324579 21338562148627840797486869)
            ·
              refine ⟨1000245100716930037382197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21338562148627840797486869 1000245100716930037382197)
              ·
                refine ⟨93772978192212191004581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1000245100716930037382197 93772978192212191004581)
                ·
                  rfl

theorem cell21_1232700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 5].length) (baseStart_1232700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232700 prefixEnd_1232700 := by exact prefixLift 1232700
  have htrace : WordTrace (prefixWord ++ tailWord_1232700) baseStart_1232700 baseEnd_1232700 := by
    simpa [prefixWord, tailWord_1232700, baseEnd_1232700] using wordTrace_append hprefix tailTrace_1232700
  have hstable : (prefixWord ++ tailWord_1232700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232700).length < 2 ^ (prefixWord ++ tailWord_1232700).sum := by decide
  have hdescent : baseEnd_1232700 < baseStart_1232700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232717 : List Nat := [1, 6, 1, 2, 1, 3, 7]
def baseStart_1232717 : Nat := 118140960795 + 1232717 * 2 ^ 59
def prefixEnd_1232717 : Nat := 4983230072969 + 3 ^ 40 * 1232717 * 2
def baseEnd_1232717 : Nat := 31258090467583146803375

theorem tailTrace_1232717 : CollatzResearch.WordTrace tailWord_1232717 prefixEnd_1232717 31258090467583146803375 := by
  unfold tailWord_1232717
  simp only [CollatzResearch.WordTrace]
  refine ⟨44960882675084315147456405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29973921783389543431637603 44960882675084315147456405)
  ·
    refine ⟨2107541375394577272537019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44960882675084315147456405 2107541375394577272537019)
    ·
      refine ⟨3161312063091865908805529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2107541375394577272537019 3161312063091865908805529)
      ·
        refine ⟨2370984047318899431604147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3161312063091865908805529 2370984047318899431604147)
        ·
          refine ⟨3556476070978349147406221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2370984047318899431604147 3556476070978349147406221)
          ·
            refine ⟨1333678526616880930277333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3556476070978349147406221 1333678526616880930277333)
            ·
              refine ⟨31258090467583146803375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1333678526616880930277333 31258090467583146803375)
              ·
                rfl

theorem cell21_1232717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 7].length) (baseStart_1232717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232717 prefixEnd_1232717 := by exact prefixLift 1232717
  have htrace : WordTrace (prefixWord ++ tailWord_1232717) baseStart_1232717 baseEnd_1232717 := by
    simpa [prefixWord, tailWord_1232717, baseEnd_1232717] using wordTrace_append hprefix tailTrace_1232717
  have hstable : (prefixWord ++ tailWord_1232717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232717).length < 2 ^ (prefixWord ++ tailWord_1232717).sum := by decide
  have hdescent : baseEnd_1232717 < baseStart_1232717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232776 : List Nat := [2, 1, 3, 3, 4, 8]
def baseStart_1232776 : Nat := 118140960795 + 1232776 * 2 ^ 59
def prefixEnd_1232776 : Nat := 4983230072969 + 3 ^ 40 * 1232776 * 2
def baseEnd_1232776 : Nat := 10419862178225086286923

theorem tailTrace_1232776 : CollatzResearch.WordTrace tailWord_1232776 prefixEnd_1232776 10419862178225086286923 := by
  unfold tailWord_1232776
  simp only [CollatzResearch.WordTrace]
  refine ⟨22481517290935284111927091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29975356387913712149236121 22481517290935284111927091)
  ·
    refine ⟨33722275936402926167890637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22481517290935284111927091 33722275936402926167890637)
    ·
      refine ⟨12645853476151097312958989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33722275936402926167890637 12645853476151097312958989)
      ·
        refine ⟨4742195053556661492359621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12645853476151097312958989 4742195053556661492359621)
        ·
          refine ⟨889161572541874029817429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4742195053556661492359621 889161572541874029817429)
          ·
            refine ⟨10419862178225086286923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 889161572541874029817429 10419862178225086286923)
            ·
              rfl

theorem cell21_1232776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 8].length) (baseStart_1232776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232776 prefixEnd_1232776 := by exact prefixLift 1232776
  have htrace : WordTrace (prefixWord ++ tailWord_1232776) baseStart_1232776 baseEnd_1232776 := by
    simpa [prefixWord, tailWord_1232776, baseEnd_1232776] using wordTrace_append hprefix tailTrace_1232776
  have hstable : (prefixWord ++ tailWord_1232776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232776).length < 2 ^ (prefixWord ++ tailWord_1232776).sum := by decide
  have hdescent : baseEnd_1232776 < baseStart_1232776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232807 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 5]
def baseStart_1232807 : Nat := 118140960795 + 1232807 * 2 ^ 59
def prefixEnd_1232807 : Nat := 4983230072969 + 3 ^ 40 * 1232807 * 2
def baseEnd_1232807 : Nat := 281343353434428164730191

theorem tailTrace_1232807 : CollatzResearch.WordTrace tailWord_1232807 prefixEnd_1232807 281343353434428164730191 := by
  unfold tailWord_1232807
  simp only [CollatzResearch.WordTrace]
  refine ⟨44964165244758260518232675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29976110163172173678821783 44964165244758260518232675)
  ·
    refine ⟨67446247867137390777349013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44964165244758260518232675 67446247867137390777349013)
    ·
      refine ⟨3161542868772065192688235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67446247867137390777349013 3161542868772065192688235)
      ·
        refine ⟨4742314303158097789032353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3161542868772065192688235 4742314303158097789032353)
        ·
          refine ⟨3556735727368573341774265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4742314303158097789032353 3556735727368573341774265)
          ·
            refine ⟨2667551795526430006330699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3556735727368573341774265 2667551795526430006330699)
            ·
              refine ⟨4001327693289645009496049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2667551795526430006330699 4001327693289645009496049)
              ·
                refine ⟨3000995769967233757122037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4001327693289645009496049 3000995769967233757122037)
                ·
                  refine ⟨281343353434428164730191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3000995769967233757122037 281343353434428164730191)
                  ·
                    rfl

theorem cell21_1232807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 5].length) (baseStart_1232807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232807 prefixEnd_1232807 := by exact prefixLift 1232807
  have htrace : WordTrace (prefixWord ++ tailWord_1232807) baseStart_1232807 baseEnd_1232807 := by
    simpa [prefixWord, tailWord_1232807, baseEnd_1232807] using wordTrace_append hprefix tailTrace_1232807
  have hstable : (prefixWord ++ tailWord_1232807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232807).length < 2 ^ (prefixWord ++ tailWord_1232807).sum := by decide
  have hdescent : baseEnd_1232807 < baseStart_1232807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232880 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 6]
def baseStart_1232880 : Nat := 118140960795 + 1232880 * 2 ^ 59
def prefixEnd_1232880 : Nat := 4983230072969 + 3 ^ 40 * 1232880 * 2
def baseEnd_1232880 : Nat := 281360013028996260013375

theorem tailTrace_1232880 : CollatzResearch.WordTrace tailWord_1232880 prefixEnd_1232880 281360013028996260013375 := by
  unfold tailWord_1232880
  simp only [CollatzResearch.WordTrace]
  refine ⟨22483413886746896992820047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29977885182329195990426729 22483413886746896992820047)
  ·
    refine ⟨33725120830120345489230071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22483413886746896992820047 33725120830120345489230071)
    ·
      refine ⟨50587681245180518233845107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33725120830120345489230071 50587681245180518233845107)
      ·
        refine ⟨75881521867770777350767661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50587681245180518233845107 75881521867770777350767661)
        ·
          refine ⟨28455570700414041506537873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75881521867770777350767661 28455570700414041506537873)
          ·
            refine ⟨21341678025310531129903405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28455570700414041506537873 21341678025310531129903405)
            ·
              refine ⟨8003129259491449173713777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21341678025310531129903405 8003129259491449173713777)
              ·
                refine ⟨6002346944618586880285333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8003129259491449173713777 6002346944618586880285333)
                ·
                  refine ⟨281360013028996260013375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6002346944618586880285333 281360013028996260013375)
                  ·
                    rfl

theorem cell21_1232880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_1232880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232880 prefixEnd_1232880 := by exact prefixLift 1232880
  have htrace : WordTrace (prefixWord ++ tailWord_1232880) baseStart_1232880 baseEnd_1232880 := by
    simpa [prefixWord, tailWord_1232880, baseEnd_1232880] using wordTrace_append hprefix tailTrace_1232880
  have hstable : (prefixWord ++ tailWord_1232880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232880).length < 2 ^ (prefixWord ++ tailWord_1232880).sum := by decide
  have hdescent : baseEnd_1232880 < baseStart_1232880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232897 : List Nat := [1, 2, 4, 1, 2, 1, 2, 4, 4]
def baseStart_1232897 : Nat := 118140960795 + 1232897 * 2 ^ 59
def prefixEnd_1232897 : Nat := 4983230072969 + 3 ^ 40 * 1232897 * 2
def baseEnd_1232897 : Nat := 281363892660608008230007

theorem tailTrace_1232897 : CollatzResearch.WordTrace tailWord_1232897 prefixEnd_1232897 281363892660608008230007 := by
  unfold tailWord_1232897
  simp only [CollatzResearch.WordTrace]
  refine ⟨44967447814432205889008945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29978298542954803926005963 44967447814432205889008945)
  ·
    refine ⟨33725585860824154416756709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44967447814432205889008945 33725585860824154416756709)
    ·
      refine ⟨6323547348904528953141883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33725585860824154416756709 6323547348904528953141883)
      ·
        refine ⟨9485321023356793429712825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6323547348904528953141883 9485321023356793429712825)
        ·
          refine ⟨7113990767517595072284619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9485321023356793429712825 7113990767517595072284619)
          ·
            refine ⟨10670986151276392608426929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7113990767517595072284619 10670986151276392608426929)
            ·
              refine ⟨8003239613457294456320197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10670986151276392608426929 8003239613457294456320197)
              ·
                refine ⟨1500607427523242710560037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8003239613457294456320197 1500607427523242710560037)
                ·
                  refine ⟨281363892660608008230007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1500607427523242710560037 281363892660608008230007)
                  ·
                    rfl

theorem cell21_1232897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_1232897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1232897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1232897 prefixEnd_1232897 := by exact prefixLift 1232897
  have htrace : WordTrace (prefixWord ++ tailWord_1232897) baseStart_1232897 baseEnd_1232897 := by
    simpa [prefixWord, tailWord_1232897, baseEnd_1232897] using wordTrace_append hprefix tailTrace_1232897
  have hstable : (prefixWord ++ tailWord_1232897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232897).length < 2 ^ (prefixWord ++ tailWord_1232897).sum := by decide
  have hdescent : baseEnd_1232897 < baseStart_1232897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233001 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 7]
def baseStart_1233001 : Nat := 118140960795 + 1233001 * 2 ^ 59
def prefixEnd_1233001 : Nat := 4983230072969 + 3 ^ 40 * 1233001 * 2
def baseEnd_1233001 : Nat := 281387626877526938496461

theorem tailTrace_1233001 : CollatzResearch.WordTrace tailWord_1233001 prefixEnd_1233001 281387626877526938496461 := by
  unfold tailWord_1233001
  simp only [CollatzResearch.WordTrace]
  refine ⟨44971241006055431650794857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29980827337370287767196571 44971241006055431650794857)
  ·
    refine ⟨33728430754541573738096143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44971241006055431650794857 33728430754541573738096143)
    ·
      refine ⟨50592646131812360607144215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33728430754541573738096143 50592646131812360607144215)
      ·
        refine ⟨75888969197718540910716323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50592646131812360607144215 75888969197718540910716323)
        ·
          refine ⟨113833453796577811366074485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75888969197718540910716323 113833453796577811366074485)
          ·
            refine ⟨10671886293429169815569483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113833453796577811366074485 10671886293429169815569483)
            ·
              refine ⟨16007829440143754723354225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10671886293429169815569483 16007829440143754723354225)
              ·
                refine ⟨12005872080107816042515669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16007829440143754723354225 12005872080107816042515669)
                ·
                  refine ⟨281387626877526938496461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12005872080107816042515669 281387626877526938496461)
                  ·
                    rfl

theorem cell21_1233001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_1233001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233001 prefixEnd_1233001 := by exact prefixLift 1233001
  have htrace : WordTrace (prefixWord ++ tailWord_1233001) baseStart_1233001 baseEnd_1233001 := by
    simpa [prefixWord, tailWord_1233001, baseEnd_1233001] using wordTrace_append hprefix tailTrace_1233001
  have hstable : (prefixWord ++ tailWord_1233001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233001).length < 2 ^ (prefixWord ++ tailWord_1233001).sum := by decide
  have hdescent : baseEnd_1233001 < baseStart_1233001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233038 : List Nat := [4, 1, 1, 3, 4, 1, 2, 5]
def baseStart_1233038 : Nat := 118140960795 + 1233038 * 2 ^ 59
def prefixEnd_1233038 : Nat := 4983230072969 + 3 ^ 40 * 1233038 * 2
def baseEnd_1233038 : Nat := 93798690260541032126573

theorem tailTrace_1233038 : CollatzResearch.WordTrace tailWord_1233038 prefixEnd_1233038 93798690260541032126573 := by
  unfold tailWord_1233038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5621573813365173371236471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29981727004614257979927845 5621573813365173371236471)
  ·
    refine ⟨8432360720047760056854707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5621573813365173371236471 8432360720047760056854707)
    ·
      refine ⟨12648541080071640085282061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8432360720047760056854707 12648541080071640085282061)
      ·
        refine ⟨4743202905026865031980773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12648541080071640085282061 4743202905026865031980773)
        ·
          refine ⟨889350544692537193496395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4743202905026865031980773 889350544692537193496395)
          ·
            refine ⟨1334025817038805790244593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889350544692537193496395 1334025817038805790244593)
            ·
              refine ⟨1000519362779104342683445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1334025817038805790244593 1000519362779104342683445)
              ·
                refine ⟨93798690260541032126573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1000519362779104342683445 93798690260541032126573)
                ·
                  rfl

theorem cell21_1233038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_1233038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233038 prefixEnd_1233038 := by exact prefixLift 1233038
  have htrace : WordTrace (prefixWord ++ tailWord_1233038) baseStart_1233038 baseEnd_1233038 := by
    simpa [prefixWord, tailWord_1233038, baseEnd_1233038] using wordTrace_append hprefix tailTrace_1233038
  have hstable : (prefixWord ++ tailWord_1233038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233038).length < 2 ^ (prefixWord ++ tailWord_1233038).sum := by decide
  have hdescent : baseEnd_1233038 < baseStart_1233038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233069 : List Nat := [1, 5, 2, 1, 2, 2, 3, 2, 3]
def baseStart_1233069 : Nat := 118140960795 + 1233069 * 2 ^ 59
def prefixEnd_1233069 : Nat := 4983230072969 + 3 ^ 40 * 1233069 * 2
def baseEnd_1233069 : Nat := 281403145403973931362989

theorem tailTrace_1233069 : CollatzResearch.WordTrace tailWord_1233069 prefixEnd_1233069 281403145403973931362989 := by
  unfold tailWord_1233069
  simp only [CollatzResearch.WordTrace]
  refine ⟨44973721169809079264270261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29982480779872719509513507 44973721169809079264270261)
  ·
    refine ⟨4216286359669601181025337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44973721169809079264270261 4216286359669601181025337)
    ·
      refine ⟨3162214769752200885769003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4216286359669601181025337 3162214769752200885769003)
      ·
        refine ⟨4743322154628301328653505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3162214769752200885769003 4743322154628301328653505)
        ·
          refine ⟨3557491615971225996490129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4743322154628301328653505 3557491615971225996490129)
          ·
            refine ⟨2668118711978419497367597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3557491615971225996490129 2668118711978419497367597)
            ·
              refine ⟨1000544516991907311512849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2668118711978419497367597 1000544516991907311512849)
              ·
                refine ⟨750408387743930483634637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1000544516991907311512849 750408387743930483634637)
                ·
                  refine ⟨281403145403973931362989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750408387743930483634637 281403145403973931362989)
                  ·
                    rfl

theorem cell21_1233069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_1233069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233069 prefixEnd_1233069 := by exact prefixLift 1233069
  have htrace : WordTrace (prefixWord ++ tailWord_1233069) baseStart_1233069 baseEnd_1233069 := by
    simpa [prefixWord, tailWord_1233069, baseEnd_1233069] using wordTrace_append hprefix tailTrace_1233069
  have hstable : (prefixWord ++ tailWord_1233069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233069).length < 2 ^ (prefixWord ++ tailWord_1233069).sum := by decide
  have hdescent : baseEnd_1233069 < baseStart_1233069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233125 : List Nat := [1, 3, 1, 4, 2, 1, 1, 4, 4]
def baseStart_1233125 : Nat := 118140960795 + 1233125 * 2 ^ 59
def prefixEnd_1233125 : Nat := 4983230072969 + 3 ^ 40 * 1233125 * 2
def baseEnd_1233125 : Nat := 281415925366930278429541

theorem tailTrace_1233125 : CollatzResearch.WordTrace tailWord_1233125 prefixEnd_1233125 281415925366930278429541 := by
  unfold tailWord_1233125
  simp only [CollatzResearch.WordTrace]
  refine ⟨44975763657606200828308829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29983842438404133885539219 44975763657606200828308829)
  ·
    refine ⟨16865911371602325310615811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44975763657606200828308829 16865911371602325310615811)
    ·
      refine ⟨25298867057403487965923717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16865911371602325310615811 25298867057403487965923717)
      ·
        refine ⟨4743537573263153993610697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25298867057403487965923717 4743537573263153993610697)
        ·
          refine ⟨3557653179947365495208023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4743537573263153993610697 3557653179947365495208023)
          ·
            refine ⟨5336479769921048242812035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3557653179947365495208023 5336479769921048242812035)
            ·
              refine ⟨8004719654881572364218053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5336479769921048242812035 8004719654881572364218053)
              ·
                refine ⟨1500884935290294818290885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8004719654881572364218053 1500884935290294818290885)
                ·
                  refine ⟨281415925366930278429541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1500884935290294818290885 281415925366930278429541)
                  ·
                    rfl

theorem cell21_1233125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_1233125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233125 prefixEnd_1233125 := by exact prefixLift 1233125
  have htrace : WordTrace (prefixWord ++ tailWord_1233125) baseStart_1233125 baseEnd_1233125 := by
    simpa [prefixWord, tailWord_1233125, baseEnd_1233125] using wordTrace_append hprefix tailTrace_1233125
  have hstable : (prefixWord ++ tailWord_1233125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233125).length < 2 ^ (prefixWord ++ tailWord_1233125).sum := by decide
  have hdescent : baseEnd_1233125 < baseStart_1233125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233128 : List Nat := [2, 1, 4, 1, 2, 2, 4, 2, 3]
def baseStart_1233128 : Nat := 118140960795 + 1233128 * 2 ^ 59
def prefixEnd_1233128 : Nat := 4983230072969 + 3 ^ 40 * 1233128 * 2
def baseEnd_1233128 : Nat := 281416610007802939879535

theorem tailTrace_1233128 : CollatzResearch.WordTrace tailWord_1233128 prefixEnd_1233128 281416610007802939879535 := by
  unfold tailWord_1233128
  simp only [CollatzResearch.WordTrace]
  refine ⟨22487936538297666170334019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29983915384396888227112025 22487936538297666170334019)
  ·
    refine ⟨33731904807446499255501029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22487936538297666170334019 33731904807446499255501029)
    ·
      refine ⟨6324732151396218610406443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33731904807446499255501029 6324732151396218610406443)
      ·
        refine ⟨9487098227094327915609665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6324732151396218610406443 9487098227094327915609665)
        ·
          refine ⟨7115323670320745936707249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9487098227094327915609665 7115323670320745936707249)
          ·
            refine ⟨5336492752740559452530437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7115323670320745936707249 5336492752740559452530437)
            ·
              refine ⟨1000592391138854897349457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5336492752740559452530437 1000592391138854897349457)
              ·
                refine ⟨750444293354141173012093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1000592391138854897349457 750444293354141173012093)
                ·
                  refine ⟨281416610007802939879535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750444293354141173012093 281416610007802939879535)
                  ·
                    rfl

theorem cell21_1233128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 3].length) (baseStart_1233128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233128 prefixEnd_1233128 := by exact prefixLift 1233128
  have htrace : WordTrace (prefixWord ++ tailWord_1233128) baseStart_1233128 baseEnd_1233128 := by
    simpa [prefixWord, tailWord_1233128, baseEnd_1233128] using wordTrace_append hprefix tailTrace_1233128
  have hstable : (prefixWord ++ tailWord_1233128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233128).length < 2 ^ (prefixWord ++ tailWord_1233128).sum := by decide
  have hdescent : baseEnd_1233128 < baseStart_1233128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233294 : List Nat := [4, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_1233294 : Nat := 118140960795 + 1233294 * 2 ^ 59
def prefixEnd_1233294 : Nat := 4983230072969 + 3 ^ 40 * 1233294 * 2
def baseEnd_1233294 : Nat := 281454493469423540112529

theorem tailTrace_1233294 : CollatzResearch.WordTrace tailWord_1233294 prefixEnd_1233294 281454493469423540112529 := by
  unfold tailWord_1233294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5622740949249242836401367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29987951729329295127473957 5622740949249242836401367)
  ·
    refine ⟨8434111423873864254602051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5622740949249242836401367 8434111423873864254602051)
    ·
      refine ⟨12651167135810796381903077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8434111423873864254602051 12651167135810796381903077)
      ·
        refine ⟨2372093837964524321606827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12651167135810796381903077 2372093837964524321606827)
        ·
          refine ⟨3558140756946786482410241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2372093837964524321606827 3558140756946786482410241)
          ·
            refine ⟨2668605567710089861807681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3558140756946786482410241 2668605567710089861807681)
            ·
              refine ⟨2001454175782567396355761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2668605567710089861807681 2001454175782567396355761)
              ·
                refine ⟨1501090631836925547266821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2001454175782567396355761 1501090631836925547266821)
                ·
                  refine ⟨281454493469423540112529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1501090631836925547266821 281454493469423540112529)
                  ·
                    rfl

theorem cell21_1233294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_1233294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233294 prefixEnd_1233294 := by exact prefixLift 1233294
  have htrace : WordTrace (prefixWord ++ tailWord_1233294) baseStart_1233294 baseEnd_1233294 := by
    simpa [prefixWord, tailWord_1233294, baseEnd_1233294] using wordTrace_append hprefix tailTrace_1233294
  have hstable : (prefixWord ++ tailWord_1233294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233294).length < 2 ^ (prefixWord ++ tailWord_1233294).sum := by decide
  have hdescent : baseEnd_1233294 < baseStart_1233294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233305 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 5]
def baseStart_1233305 : Nat := 118140960795 + 1233305 * 2 ^ 59
def prefixEnd_1233305 : Nat := 4983230072969 + 3 ^ 40 * 1233305 * 2
def baseEnd_1233305 : Nat := 281457003819289965429173

theorem tailTrace_1233305 : CollatzResearch.WordTrace tailWord_1233305 prefixEnd_1233305 281457003819289965429173 := by
  unfold tailWord_1233305
  simp only [CollatzResearch.WordTrace]
  refine ⟨44982328796954091569861369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29988219197969394379907579 44982328796954091569861369)
  ·
    refine ⟨33736746597715568677396027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44982328796954091569861369 33736746597715568677396027)
    ·
      refine ⟨50605119896573353016094041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33736746597715568677396027 50605119896573353016094041)
      ·
        refine ⟨37953839922430014762070531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50605119896573353016094041 37953839922430014762070531)
        ·
          refine ⟨56930759883645022143105797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37953839922430014762070531 56930759883645022143105797)
          ·
            refine ⟨10674517478183441651832337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56930759883645022143105797 10674517478183441651832337)
            ·
              refine ⟨8005888108637581238874253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10674517478183441651832337 8005888108637581238874253)
              ·
                refine ⟨3002208040739092964577845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8005888108637581238874253 3002208040739092964577845)
                ·
                  refine ⟨281457003819289965429173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3002208040739092964577845 281457003819289965429173)
                  ·
                    rfl

theorem cell21_1233305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_1233305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233305 prefixEnd_1233305 := by exact prefixLift 1233305
  have htrace : WordTrace (prefixWord ++ tailWord_1233305) baseStart_1233305 baseEnd_1233305 := by
    simpa [prefixWord, tailWord_1233305, baseEnd_1233305] using wordTrace_append hprefix tailTrace_1233305
  have hstable : (prefixWord ++ tailWord_1233305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233305).length < 2 ^ (prefixWord ++ tailWord_1233305).sum := by decide
  have hdescent : baseEnd_1233305 < baseStart_1233305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233325 : List Nat := [1, 5, 2, 2, 2, 1, 3, 5]
def baseStart_1233325 : Nat := 118140960795 + 1233325 * 2 ^ 59
def prefixEnd_1233325 : Nat := 4983230072969 + 3 ^ 40 * 1233325 * 2
def baseEnd_1233325 : Nat := 93820522697258125031933

theorem tailTrace_1233325 : CollatzResearch.WordTrace tailWord_1233325 prefixEnd_1233325 93820522697258125031933 := by
  unfold tailWord_1233325
  simp only [CollatzResearch.WordTrace]
  refine ⟨44983058256881634985589429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29988705504587756657059619 44983058256881634985589429)
  ·
    refine ⟨4217161711582653279899009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44983058256881634985589429 4217161711582653279899009)
    ·
      refine ⟨3162871283686989959924257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4217161711582653279899009 3162871283686989959924257)
      ·
        refine ⟨2372153462765242469943193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3162871283686989959924257 2372153462765242469943193)
        ·
          refine ⟨1779115097073931852457395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2372153462765242469943193 1779115097073931852457395)
          ·
            refine ⟨2668672645610897778686093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779115097073931852457395 2668672645610897778686093)
            ·
              refine ⟨1000752242104086667007285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2668672645610897778686093 1000752242104086667007285)
              ·
                refine ⟨93820522697258125031933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1000752242104086667007285 93820522697258125031933)
                ·
                  rfl

theorem cell21_1233325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 5].length) (baseStart_1233325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233325 prefixEnd_1233325 := by exact prefixLift 1233325
  have htrace : WordTrace (prefixWord ++ tailWord_1233325) baseStart_1233325 baseEnd_1233325 := by
    simpa [prefixWord, tailWord_1233325, baseEnd_1233325] using wordTrace_append hprefix tailTrace_1233325
  have hstable : (prefixWord ++ tailWord_1233325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233325).length < 2 ^ (prefixWord ++ tailWord_1233325).sum := by decide
  have hdescent : baseEnd_1233325 < baseStart_1233325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233345 : List Nat := [1, 2, 7, 1, 2, 1, 1, 2, 4]
def baseStart_1233345 : Nat := 118140960795 + 1233345 * 2 ^ 59
def prefixEnd_1233345 : Nat := 4983230072969 + 3 ^ 40 * 1233345 * 2
def baseEnd_1233345 : Nat := 281466132364258784762425

theorem tailTrace_1233345 : CollatzResearch.WordTrace tailWord_1233345 prefixEnd_1233345 281466132364258784762425 := by
  unfold tailWord_1233345
  simp only [CollatzResearch.WordTrace]
  refine ⟨44983787716809178401317489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29989191811206118934211659 44983787716809178401317489)
  ·
    refine ⟨33737840787606883800988117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44983787716809178401317489 33737840787606883800988117)
    ·
      refine ⟨790730643459536339085659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 33737840787606883800988117 790730643459536339085659)
      ·
        refine ⟨1186095965189304508628489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790730643459536339085659 1186095965189304508628489)
        ·
          refine ⟨889571973891978381471367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1186095965189304508628489 889571973891978381471367)
          ·
            refine ⟨1334357960837967572207051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889571973891978381471367 1334357960837967572207051)
            ·
              refine ⟨2001536941256951358310577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1334357960837967572207051 2001536941256951358310577)
              ·
                refine ⟨1501152705942713518732933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2001536941256951358310577 1501152705942713518732933)
                ·
                  refine ⟨281466132364258784762425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1501152705942713518732933 281466132364258784762425)
                  ·
                    rfl

theorem cell21_1233345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 4].length) (baseStart_1233345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233345 prefixEnd_1233345 := by exact prefixLift 1233345
  have htrace : WordTrace (prefixWord ++ tailWord_1233345) baseStart_1233345 baseEnd_1233345 := by
    simpa [prefixWord, tailWord_1233345, baseEnd_1233345] using wordTrace_append hprefix tailTrace_1233345
  have hstable : (prefixWord ++ tailWord_1233345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233345).length < 2 ^ (prefixWord ++ tailWord_1233345).sum := by decide
  have hdescent : baseEnd_1233345 < baseStart_1233345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233384 : List Nat := [2, 1, 4, 1, 1, 5, 2, 5]
def baseStart_1233384 : Nat := 118140960795 + 1233384 * 2 ^ 59
def prefixEnd_1233384 : Nat := 4983230072969 + 3 ^ 40 * 1233384 * 2
def baseEnd_1233384 : Nat := 93825010898534461204115

theorem tailTrace_1233384 : CollatzResearch.WordTrace tailWord_1233384 prefixEnd_1233384 93825010898534461204115 := by
  unfold tailWord_1233384
  simp only [CollatzResearch.WordTrace]
  refine ⟨22492605081833944030993603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29990140109111925374658137 22492605081833944030993603)
  ·
    refine ⟨33738907622750916046490405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22492605081833944030993603 33738907622750916046490405)
    ·
      refine ⟨6326045179265796758716951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33738907622750916046490405 6326045179265796758716951)
      ·
        refine ⟨9489067768898695138075427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6326045179265796758716951 9489067768898695138075427)
        ·
          refine ⟨14233601653348042707113141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9489067768898695138075427 14233601653348042707113141)
          ·
            refine ⟨1334400155001379003791857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14233601653348042707113141 1334400155001379003791857)
            ·
              refine ⟨1000800116251034252843893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1334400155001379003791857 1000800116251034252843893)
              ·
                refine ⟨93825010898534461204115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1000800116251034252843893 93825010898534461204115)
                ·
                  rfl

theorem cell21_1233384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 5].length) (baseStart_1233384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233384 prefixEnd_1233384 := by exact prefixLift 1233384
  have htrace : WordTrace (prefixWord ++ tailWord_1233384) baseStart_1233384 baseEnd_1233384 := by
    simpa [prefixWord, tailWord_1233384, baseEnd_1233384] using wordTrace_append hprefix tailTrace_1233384
  have hstable : (prefixWord ++ tailWord_1233384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233384).length < 2 ^ (prefixWord ++ tailWord_1233384).sum := by decide
  have hdescent : baseEnd_1233384 < baseStart_1233384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233395 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 8]
def baseStart_1233395 : Nat := 118140960795 + 1233395 * 2 ^ 59
def prefixEnd_1233395 : Nat := 4983230072969 + 3 ^ 40 * 1233395 * 2
def baseEnd_1233395 : Nat := 281477543045469808928989

theorem tailTrace_1233395 : CollatzResearch.WordTrace tailWord_1233395 prefixEnd_1233395 281477543045469808928989 := by
  unfold tailWord_1233395
  simp only [CollatzResearch.WordTrace]
  refine ⟨44985611366628036940637639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29990407577752024627091759 44985611366628036940637639)
  ·
    refine ⟨67478417049942055410956459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44985611366628036940637639 67478417049942055410956459)
    ·
      refine ⟨101217625574913083116434689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67478417049942055410956459 101217625574913083116434689)
      ·
        refine ⟨75913219181184812337326017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101217625574913083116434689 75913219181184812337326017)
        ·
          refine ⟨56934914385888609252994513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75913219181184812337326017 56934914385888609252994513)
          ·
            refine ⟨42701185789416456939745885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56934914385888609252994513 42701185789416456939745885)
            ·
              refine ⟨16012944671031171352404707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42701185789416456939745885 16012944671031171352404707)
              ·
                refine ⟨24019417006546757028607061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16012944671031171352404707 24019417006546757028607061)
                ·
                  refine ⟨281477543045469808928989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24019417006546757028607061 281477543045469808928989)
                  ·
                    rfl

theorem cell21_1233395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 8].length) (baseStart_1233395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233395 prefixEnd_1233395 := by exact prefixLift 1233395
  have htrace : WordTrace (prefixWord ++ tailWord_1233395) baseStart_1233395 baseEnd_1233395 := by
    simpa [prefixWord, tailWord_1233395, baseEnd_1233395] using wordTrace_append hprefix tailTrace_1233395
  have hstable : (prefixWord ++ tailWord_1233395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233395).length < 2 ^ (prefixWord ++ tailWord_1233395).sum := by decide
  have hdescent : baseEnd_1233395 < baseStart_1233395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233415 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 5]
def baseStart_1233415 : Nat := 118140960795 + 1233415 * 2 ^ 59
def prefixEnd_1233415 : Nat := 4983230072969 + 3 ^ 40 * 1233415 * 2
def baseEnd_1233415 : Nat := 281482107317954218595615

theorem tailTrace_1233415 : CollatzResearch.WordTrace tailWord_1233415 prefixEnd_1233415 281482107317954218595615 := by
  unfold tailWord_1233415
  simp only [CollatzResearch.WordTrace]
  refine ⟨44986340826555580356365699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29990893884370386904243799 44986340826555580356365699)
  ·
    refine ⟨67479511239833370534548549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44986340826555580356365699 67479511239833370534548549)
    ·
      refine ⟨12652408357468756975227853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67479511239833370534548549 12652408357468756975227853)
      ·
        refine ⟨4744653134050783865710445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12652408357468756975227853 4744653134050783865710445)
        ·
          refine ⟨1779244925269043949641417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4744653134050783865710445 1779244925269043949641417)
          ·
            refine ⟨1334433693951782962231063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1779244925269043949641417 1334433693951782962231063)
            ·
              refine ⟨2001650540927674443346595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1334433693951782962231063 2001650540927674443346595)
              ·
                refine ⟨3002475811391511665019893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2001650540927674443346595 3002475811391511665019893)
                ·
                  refine ⟨281482107317954218595615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3002475811391511665019893 281482107317954218595615)
                  ·
                    rfl

theorem cell21_1233415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 5].length) (baseStart_1233415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233415 prefixEnd_1233415 := by exact prefixLift 1233415
  have htrace : WordTrace (prefixWord ++ tailWord_1233415) baseStart_1233415 baseEnd_1233415 := by
    simpa [prefixWord, tailWord_1233415, baseEnd_1233415] using wordTrace_append hprefix tailTrace_1233415
  have hstable : (prefixWord ++ tailWord_1233415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233415).length < 2 ^ (prefixWord ++ tailWord_1233415).sum := by decide
  have hdescent : baseEnd_1233415 < baseStart_1233415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233460 : List Nat := [2, 5, 1, 3, 1, 9]
def baseStart_1233460 : Nat := 118140960795 + 1233460 * 2 ^ 59
def prefixEnd_1233460 : Nat := 4983230072969 + 3 ^ 40 * 1233460 * 2
def baseEnd_1233460 : Nat := 10425643590038671864649

theorem tailTrace_1233460 : CollatzResearch.WordTrace tailWord_1233460 prefixEnd_1233460 10425643590038671864649 := by
  unfold tailWord_1233460
  simp only [CollatzResearch.WordTrace]
  refine ⟨22493991055696276520876917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29991988074261702027835889 22493991055696276520876917)
  ·
    refine ⟨2108811661471525923832211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22493991055696276520876917 2108811661471525923832211)
    ·
      refine ⟨3163217492207288885748317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2108811661471525923832211 3163217492207288885748317)
      ·
        refine ⟨1186206559577733332155619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3163217492207288885748317 1186206559577733332155619)
        ·
          refine ⟨1779309839366599998233429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186206559577733332155619 1779309839366599998233429)
          ·
            refine ⟨10425643590038671864649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1779309839366599998233429 10425643590038671864649)
            ·
              rfl

theorem cell21_1233460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 9].length) (baseStart_1233460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233460 prefixEnd_1233460 := by exact prefixLift 1233460
  have htrace : WordTrace (prefixWord ++ tailWord_1233460) baseStart_1233460 baseEnd_1233460 := by
    simpa [prefixWord, tailWord_1233460, baseEnd_1233460] using wordTrace_append hprefix tailTrace_1233460
  have hstable : (prefixWord ++ tailWord_1233460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233460).length < 2 ^ (prefixWord ++ tailWord_1233460).sum := by decide
  have hdescent : baseEnd_1233460 < baseStart_1233460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233522 : List Nat := [3, 2, 1, 2, 4, 2, 1, 2, 4]
def baseStart_1233522 : Nat := 118140960795 + 1233522 * 2 ^ 59
def prefixEnd_1233522 : Nat := 4983230072969 + 3 ^ 40 * 1233522 * 2
def baseEnd_1233522 : Nat := 281506526175745810312063

theorem tailTrace_1233522 : CollatzResearch.WordTrace tailWord_1233522 prefixEnd_1233522 281506526175745810312063 := by
  unfold tailWord_1233522
  simp only [CollatzResearch.WordTrace]
  refine ⟨11247560859291984407627705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29993495624778625087007213 11247560859291984407627705)
  ·
    refine ⟨8435670644468988305720779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11247560859291984407627705 8435670644468988305720779)
    ·
      refine ⟨12653505966703482458581169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8435670644468988305720779 12653505966703482458581169)
      ·
        refine ⟨9490129475027611843935877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12653505966703482458581169 9490129475027611843935877)
        ·
          refine ⟨1779399276567677220737977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9490129475027611843935877 1779399276567677220737977)
          ·
            refine ⟨1334549457425757915553483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1779399276567677220737977 1334549457425757915553483)
            ·
              refine ⟨2001824186138636873330225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1334549457425757915553483 2001824186138636873330225)
              ·
                refine ⟨1501368139603977654997669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2001824186138636873330225 1501368139603977654997669)
                ·
                  refine ⟨281506526175745810312063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1501368139603977654997669 281506526175745810312063)
                  ·
                    rfl

theorem cell21_1233522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_1233522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233522 prefixEnd_1233522 := by exact prefixLift 1233522
  have htrace : WordTrace (prefixWord ++ tailWord_1233522) baseStart_1233522 baseEnd_1233522 := by
    simpa [prefixWord, tailWord_1233522, baseEnd_1233522] using wordTrace_append hprefix tailTrace_1233522
  have hstable : (prefixWord ++ tailWord_1233522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233522).length < 2 ^ (prefixWord ++ tailWord_1233522).sum := by decide
  have hdescent : baseEnd_1233522 < baseStart_1233522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233564 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 6]
def baseStart_1233564 : Nat := 118140960795 + 1233564 * 2 ^ 59
def prefixEnd_1233564 : Nat := 4983230072969 + 3 ^ 40 * 1233564 * 2
def baseEnd_1233564 : Nat := 281516111147963070611977

theorem tailTrace_1233564 : CollatzResearch.WordTrace tailWord_1233564 prefixEnd_1233564 281516111147963070611977 := by
  unfold tailWord_1233564
  simp only [CollatzResearch.WordTrace]
  refine ⟨22495887651507889401769873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29994516868677185869026497 22495887651507889401769873)
  ·
    refine ⟨16871915738630917051327405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22495887651507889401769873 16871915738630917051327405)
    ·
      refine ⟨6326968401986593894247777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16871915738630917051327405 6326968401986593894247777)
      ·
        refine ⟨4745226301489945420685833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6326968401986593894247777 4745226301489945420685833)
        ·
          refine ⟨3558919726117459065514375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4745226301489945420685833 3558919726117459065514375)
          ·
            refine ⟨5338379589176188598271563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3558919726117459065514375 5338379589176188598271563)
            ·
              refine ⟨8007569383764282897407345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5338379589176188598271563 8007569383764282897407345)
              ·
                refine ⟨6005677037823212173055509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8007569383764282897407345 6005677037823212173055509)
                ·
                  refine ⟨281516111147963070611977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6005677037823212173055509 281516111147963070611977)
                  ·
                    rfl

theorem cell21_1233564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_1233564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233564 prefixEnd_1233564 := by exact prefixLift 1233564
  have htrace : WordTrace (prefixWord ++ tailWord_1233564) baseStart_1233564 baseEnd_1233564 := by
    simpa [prefixWord, tailWord_1233564, baseEnd_1233564] using wordTrace_append hprefix tailTrace_1233564
  have hstable : (prefixWord ++ tailWord_1233564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233564).length < 2 ^ (prefixWord ++ tailWord_1233564).sum := by decide
  have hdescent : baseEnd_1233564 < baseStart_1233564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233626 : List Nat := [3, 1, 1, 2, 2, 2, 2, 5, 3]
def baseStart_1233626 : Nat := 118140960795 + 1233626 * 2 ^ 59
def prefixEnd_1233626 : Nat := 4983230072969 + 3 ^ 40 * 1233626 * 2
def baseEnd_1233626 : Nat := 281530260392664740578517

theorem tailTrace_1233626 : CollatzResearch.WordTrace tailWord_1233626 prefixEnd_1233626 281530260392664740578517 := by
  unfold tailWord_1233626
  simp only [CollatzResearch.WordTrace]
  refine ⟨11248509157197790848074183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29996024419194108928197821 11248509157197790848074183)
  ·
    refine ⟨16872763735796686272111275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11248509157197790848074183 16872763735796686272111275)
    ·
      refine ⟨25309145603695029408166913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16872763735796686272111275 25309145603695029408166913)
      ·
        refine ⟨18981859202771272056125185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25309145603695029408166913 18981859202771272056125185)
        ·
          refine ⟨14236394402078454042093889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18981859202771272056125185 14236394402078454042093889)
          ·
            refine ⟨10677295801558840531570417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14236394402078454042093889 10677295801558840531570417)
            ·
              refine ⟨8007971851169130398677813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10677295801558840531570417 8007971851169130398677813)
              ·
                refine ⟨750747361047105974876045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8007971851169130398677813 750747361047105974876045)
                ·
                  refine ⟨281530260392664740578517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750747361047105974876045 281530260392664740578517)
                  ·
                    rfl

theorem cell21_1233626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_1233626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233626 prefixEnd_1233626 := by exact prefixLift 1233626
  have htrace : WordTrace (prefixWord ++ tailWord_1233626) baseStart_1233626 baseEnd_1233626 := by
    simpa [prefixWord, tailWord_1233626, baseEnd_1233626] using wordTrace_append hprefix tailTrace_1233626
  have hstable : (prefixWord ++ tailWord_1233626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233626).length < 2 ^ (prefixWord ++ tailWord_1233626).sum := by decide
  have hdescent : baseEnd_1233626 < baseStart_1233626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233744 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 7]
def baseStart_1233744 : Nat := 118140960795 + 1233744 * 2 ^ 59
def prefixEnd_1233744 : Nat := 4983230072969 + 3 ^ 40 * 1233744 * 2
def baseEnd_1233744 : Nat := 281557189600322757611609

theorem tailTrace_1233744 : CollatzResearch.WordTrace tailWord_1233744 prefixEnd_1233744 281557189600322757611609 := by
  unfold tailWord_1233744
  simp only [CollatzResearch.WordTrace]
  refine ⟨22499170221181834772546143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29998893628242446363394857 22499170221181834772546143)
  ·
    refine ⟨33748755331772752158819215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22499170221181834772546143 33748755331772752158819215)
    ·
      refine ⟨50623132997659128238228823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33748755331772752158819215 50623132997659128238228823)
      ·
        refine ⟨75934699496488692357343235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50623132997659128238228823 75934699496488692357343235)
        ·
          refine ⟨113902049244733038536014853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75934699496488692357343235 113902049244733038536014853)
          ·
            refine ⟨21356634233387444725502785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113902049244733038536014853 21356634233387444725502785)
            ·
              refine ⟨16017475675040583544127089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21356634233387444725502785 16017475675040583544127089)
              ·
                refine ⟨12013106756280437658095317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16017475675040583544127089 12013106756280437658095317)
                ·
                  refine ⟨281557189600322757611609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12013106756280437658095317 281557189600322757611609)
                  ·
                    rfl

theorem cell21_1233744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_1233744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233744 prefixEnd_1233744 := by exact prefixLift 1233744
  have htrace : WordTrace (prefixWord ++ tailWord_1233744) baseStart_1233744 baseEnd_1233744 := by
    simpa [prefixWord, tailWord_1233744, baseEnd_1233744] using wordTrace_append hprefix tailTrace_1233744
  have hstable : (prefixWord ++ tailWord_1233744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233744).length < 2 ^ (prefixWord ++ tailWord_1233744).sum := by decide
  have hdescent : baseEnd_1233744 < baseStart_1233744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233823 : List Nat := [1, 1, 2, 5, 2, 3, 1, 6]
def baseStart_1233823 : Nat := 118140960795 + 1233823 * 2 ^ 59
def prefixEnd_1233823 : Nat := 4983230072969 + 3 ^ 40 * 1233823 * 2
def baseEnd_1233823 : Nat := 93858406158878725264927

theorem tailTrace_1233823 : CollatzResearch.WordTrace tailWord_1233823 prefixEnd_1233823 93858406158878725264927 := by
  unfold tailWord_1233823
  simp only [CollatzResearch.WordTrace]
  refine ⟨45001221809077466037218123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30000814539384977358145415 45001221809077466037218123)
  ·
    refine ⟨67501832713616199055827185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45001221809077466037218123 67501832713616199055827185)
    ·
      refine ⟨50626374535212149291870389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67501832713616199055827185 50626374535212149291870389)
      ·
        refine ⟨4746222612676138996112849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50626374535212149291870389 4746222612676138996112849)
        ·
          refine ⟨3559666959507104247084637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4746222612676138996112849 3559666959507104247084637)
          ·
            refine ⟨1334875109815164092656739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3559666959507104247084637 1334875109815164092656739)
            ·
              refine ⟨2002312664722746138985109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1334875109815164092656739 2002312664722746138985109)
              ·
                refine ⟨93858406158878725264927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2002312664722746138985109 93858406158878725264927)
                ·
                  rfl

theorem cell21_1233823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 6].length) (baseStart_1233823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233823 prefixEnd_1233823 := by exact prefixLift 1233823
  have htrace : WordTrace (prefixWord ++ tailWord_1233823) baseStart_1233823 baseEnd_1233823 := by
    simpa [prefixWord, tailWord_1233823, baseEnd_1233823] using wordTrace_append hprefix tailTrace_1233823
  have hstable : (prefixWord ++ tailWord_1233823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233823).length < 2 ^ (prefixWord ++ tailWord_1233823).sum := by decide
  have hdescent : baseEnd_1233823 < baseStart_1233823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233846 : List Nat := [5, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_1233846 : Nat := 118140960795 + 1233846 * 2 ^ 59
def prefixEnd_1233846 : Nat := 4983230072969 + 3 ^ 40 * 1233846 * 2
def baseEnd_1233846 : Nat := 281580467389993246911401

theorem tailTrace_1233846 : CollatzResearch.WordTrace tailWord_1233846 prefixEnd_1233846 281580467389993246911401 := by
  unfold tailWord_1233846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2812628792999633810331587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30001373791996093976870261 2812628792999633810331587)
  ·
    refine ⟨4218943189499450715497381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2812628792999633810331587 4218943189499450715497381)
    ·
      refine ⟨791051848031147009155759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4218943189499450715497381 791051848031147009155759)
      ·
        refine ⟨1186577772046720513733639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791051848031147009155759 1186577772046720513733639)
        ·
          refine ⟨1779866658070080770600459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186577772046720513733639 1779866658070080770600459)
          ·
            refine ⟨2669799987105121155900689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779866658070080770600459 2669799987105121155900689)
            ·
              refine ⟨2002349990328840866925517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2669799987105121155900689 2002349990328840866925517)
              ·
                refine ⟨750881246373315325097069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2002349990328840866925517 750881246373315325097069)
                ·
                  refine ⟨281580467389993246911401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750881246373315325097069 281580467389993246911401)
                  ·
                    rfl

theorem cell21_1233846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_1233846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233846 prefixEnd_1233846 := by exact prefixLift 1233846
  have htrace : WordTrace (prefixWord ++ tailWord_1233846) baseStart_1233846 baseEnd_1233846 := by
    simpa [prefixWord, tailWord_1233846, baseEnd_1233846] using wordTrace_append hprefix tailTrace_1233846
  have hstable : (prefixWord ++ tailWord_1233846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233846).length < 2 ^ (prefixWord ++ tailWord_1233846).sum := by decide
  have hdescent : baseEnd_1233846 < baseStart_1233846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233927 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 6]
def baseStart_1233927 : Nat := 118140960795 + 1233927 * 2 ^ 59
def prefixEnd_1233927 : Nat := 4983230072969 + 3 ^ 40 * 1233927 * 2
def baseEnd_1233927 : Nat := 281598952693555106061235

theorem tailTrace_1233927 : CollatzResearch.WordTrace tailWord_1233927 prefixEnd_1233927 281598952693555106061235 := by
  unfold tailWord_1233927
  simp only [CollatzResearch.WordTrace]
  refine ⟨45005015000700691799004035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30003343333800461199336023 45005015000700691799004035)
  ·
    refine ⟨67507522501051037698506053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45005015000700691799004035 67507522501051037698506053)
    ·
      refine ⟨12657660468947069568469885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67507522501051037698506053 12657660468947069568469885)
      ·
        refine ⟨4746622675855151088176207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12657660468947069568469885 4746622675855151088176207)
        ·
          refine ⟨7119934013782726632264311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4746622675855151088176207 7119934013782726632264311)
          ·
            refine ⟨10679901020674089948396467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7119934013782726632264311 10679901020674089948396467)
            ·
              refine ⟨16019851531011134922594701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10679901020674089948396467 16019851531011134922594701)
              ·
                refine ⟨6007444324129175595973013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16019851531011134922594701 6007444324129175595973013)
                ·
                  refine ⟨281598952693555106061235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6007444324129175595973013 281598952693555106061235)
                  ·
                    rfl

theorem cell21_1233927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 6].length) (baseStart_1233927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233927 prefixEnd_1233927 := by exact prefixLift 1233927
  have htrace : WordTrace (prefixWord ++ tailWord_1233927) baseStart_1233927 baseEnd_1233927 := by
    simpa [prefixWord, tailWord_1233927, baseEnd_1233927] using wordTrace_append hprefix tailTrace_1233927
  have hstable : (prefixWord ++ tailWord_1233927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233927).length < 2 ^ (prefixWord ++ tailWord_1233927).sum := by decide
  have hdescent : baseEnd_1233927 < baseStart_1233927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233930 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 5]
def baseStart_1233930 : Nat := 118140960795 + 1233930 * 2 ^ 59
def prefixEnd_1233930 : Nat := 4983230072969 + 3 ^ 40 * 1233930 * 2
def baseEnd_1233930 : Nat := 281599637334427767511229

theorem tailTrace_1233930 : CollatzResearch.WordTrace tailWord_1233930 prefixEnd_1233930 281599637334427767511229 := by
  unfold tailWord_1233930
  simp only [CollatzResearch.WordTrace]
  refine ⟨11251281104922455827840811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30003416279793215540908829 11251281104922455827840811)
  ·
    refine ⟨16876921657383683741761217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11251281104922455827840811 16876921657383683741761217)
    ·
      refine ⟨12657691243037762806320913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16876921657383683741761217 12657691243037762806320913)
      ·
        refine ⟨9493268432278322104740685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12657691243037762806320913 9493268432278322104740685)
        ·
          refine ⟨3559975662104370789277757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9493268432278322104740685 3559975662104370789277757)
          ·
            refine ⟨1334990873289139045979159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3559975662104370789277757 1334990873289139045979159)
            ·
              refine ⟨2002486309933708568968739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1334990873289139045979159 2002486309933708568968739)
              ·
                refine ⟨3003729464900562853453109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2002486309933708568968739 3003729464900562853453109)
                ·
                  refine ⟨281599637334427767511229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3003729464900562853453109 281599637334427767511229)
                  ·
                    rfl

theorem cell21_1233930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_1233930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233930 prefixEnd_1233930 := by exact prefixLift 1233930
  have htrace : WordTrace (prefixWord ++ tailWord_1233930) baseStart_1233930 baseEnd_1233930 := by
    simpa [prefixWord, tailWord_1233930, baseEnd_1233930] using wordTrace_append hprefix tailTrace_1233930
  have hstable : (prefixWord ++ tailWord_1233930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233930).length < 2 ^ (prefixWord ++ tailWord_1233930).sum := by decide
  have hdescent : baseEnd_1233930 < baseStart_1233930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233944 : List Nat := [2, 1, 2, 3, 2, 3, 1, 3, 4]
def baseStart_1233944 : Nat := 118140960795 + 1233944 * 2 ^ 59
def prefixEnd_1233944 : Nat := 4983230072969 + 3 ^ 40 * 1233944 * 2
def baseEnd_1233944 : Nat := 281602832325166854277867

theorem tailTrace_1233944 : CollatzResearch.WordTrace tailWord_1233944 prefixEnd_1233944 281602832325166854277867 := by
  unfold tailWord_1233944
  simp only [CollatzResearch.WordTrace]
  refine ⟨22502817520819551851186443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30003756694426069134915257 22502817520819551851186443)
  ·
    refine ⟨33754226281229327776779665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22502817520819551851186443 33754226281229327776779665)
    ·
      refine ⟨25315669710921995832584749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33754226281229327776779665 25315669710921995832584749)
      ·
        refine ⟨9493376141595748437219281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25315669710921995832584749 9493376141595748437219281)
        ·
          refine ⟨7120032106196811327914461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9493376141595748437219281 7120032106196811327914461)
          ·
            refine ⟨2670012039823804247967923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7120032106196811327914461 2670012039823804247967923)
            ·
              refine ⟨4005018059735706371951885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670012039823804247967923 4005018059735706371951885)
              ·
                refine ⟨1501881772400889889481957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4005018059735706371951885 1501881772400889889481957)
                ·
                  refine ⟨281602832325166854277867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1501881772400889889481957 281602832325166854277867)
                  ·
                    rfl

theorem cell21_1233944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_1233944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1233944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1233944 prefixEnd_1233944 := by exact prefixLift 1233944
  have htrace : WordTrace (prefixWord ++ tailWord_1233944) baseStart_1233944 baseEnd_1233944 := by
    simpa [prefixWord, tailWord_1233944, baseEnd_1233944] using wordTrace_append hprefix tailTrace_1233944
  have hstable : (prefixWord ++ tailWord_1233944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233944).length < 2 ^ (prefixWord ++ tailWord_1233944).sum := by decide
  have hdescent : baseEnd_1233944 < baseStart_1233944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234017 : List Nat := [1, 2, 3, 1, 1, 2, 2, 9]
def baseStart_1234017 : Nat := 118140960795 + 1234017 * 2 ^ 59
def prefixEnd_1234017 : Nat := 4983230072969 + 3 ^ 40 * 1234017 * 2
def baseEnd_1234017 : Nat := 93873163973244983187017

theorem tailTrace_1234017 : CollatzResearch.WordTrace tailWord_1234017 prefixEnd_1234017 93873163973244983187017 := by
  unfold tailWord_1234017
  simp only [CollatzResearch.WordTrace]
  refine ⟨45008297570374637169780305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30005531713583091446520203 45008297570374637169780305)
  ·
    refine ⟨33756223177780977877335229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45008297570374637169780305 33756223177780977877335229)
    ·
      refine ⟨12658583691667866704000711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33756223177780977877335229 12658583691667866704000711)
      ·
        refine ⟨18987875537501800056001067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12658583691667866704000711 18987875537501800056001067)
        ·
          refine ⟨28481813306252700084001601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18987875537501800056001067 28481813306252700084001601)
          ·
            refine ⟨21361359979689525063001201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28481813306252700084001601 21361359979689525063001201)
            ·
              refine ⟨16021019984767143797250901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21361359979689525063001201 16021019984767143797250901)
              ·
                refine ⟨93873163973244983187017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16021019984767143797250901 93873163973244983187017)
                ·
                  rfl

theorem cell21_1234017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 9].length) (baseStart_1234017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234017 prefixEnd_1234017 := by exact prefixLift 1234017
  have htrace : WordTrace (prefixWord ++ tailWord_1234017) baseStart_1234017 baseEnd_1234017 := by
    simpa [prefixWord, tailWord_1234017, baseEnd_1234017] using wordTrace_append hprefix tailTrace_1234017
  have hstable : (prefixWord ++ tailWord_1234017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234017).length < 2 ^ (prefixWord ++ tailWord_1234017).sum := by decide
  have hdescent : baseEnd_1234017 < baseStart_1234017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234037 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 6]
def baseStart_1234037 : Nat := 118140960795 + 1234037 * 2 ^ 59
def prefixEnd_1234037 : Nat := 4983230072969 + 3 ^ 40 * 1234037 * 2
def baseEnd_1234037 : Nat := 281624056192219359227677

theorem tailTrace_1234037 : CollatzResearch.WordTrace tailWord_1234037 prefixEnd_1234037 281624056192219359227677 := by
  unfold tailWord_1234037
  simp only [CollatzResearch.WordTrace]
  refine ⟨45009027030302180585508365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30006018020201453723672243 45009027030302180585508365)
  ·
    refine ⟨16878385136363317719565637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45009027030302180585508365 16878385136363317719565637)
    ·
      refine ⟨3164697213068122072418557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16878385136363317719565637 3164697213068122072418557)
      ·
        refine ⟨1186761454900545777156959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3164697213068122072418557 1186761454900545777156959)
        ·
          refine ⟨1780142182350818665735439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186761454900545777156959 1780142182350818665735439)
          ·
            refine ⟨2670213273526227998603159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780142182350818665735439 2670213273526227998603159)
            ·
              refine ⟨4005319910289341997904739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670213273526227998603159 4005319910289341997904739)
              ·
                refine ⟨6007979865434012996857109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4005319910289341997904739 6007979865434012996857109)
                ·
                  refine ⟨281624056192219359227677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6007979865434012996857109 281624056192219359227677)
                  ·
                    rfl

theorem cell21_1234037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_1234037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234037 prefixEnd_1234037 := by exact prefixLift 1234037
  have htrace : WordTrace (prefixWord ++ tailWord_1234037) baseStart_1234037 baseEnd_1234037 := by
    simpa [prefixWord, tailWord_1234037, baseEnd_1234037] using wordTrace_append hprefix tailTrace_1234037
  have hstable : (prefixWord ++ tailWord_1234037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234037).length < 2 ^ (prefixWord ++ tailWord_1234037).sum := by decide
  have hdescent : baseEnd_1234037 < baseStart_1234037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234048 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 5]
def baseStart_1234048 : Nat := 118140960795 + 1234048 * 2 ^ 59
def prefixEnd_1234048 : Nat := 4983230072969 + 3 ^ 40 * 1234048 * 2
def baseEnd_1234048 : Nat := 281626566542085784544321

theorem tailTrace_1234048 : CollatzResearch.WordTrace tailWord_1234048 prefixEnd_1234048 281626566542085784544321 := by
  unfold tailWord_1234048
  simp only [CollatzResearch.WordTrace]
  refine ⟨22504714116631164732079399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30006285488841552976105865 22504714116631164732079399)
  ·
    refine ⟨33757071174946747098119099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22504714116631164732079399 33757071174946747098119099)
    ·
      refine ⟨50635606762420120647178649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33757071174946747098119099 50635606762420120647178649)
      ·
        refine ⟨37976705071815090485383987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50635606762420120647178649 37976705071815090485383987)
        ·
          refine ⟨56965057607722635728075981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37976705071815090485383987 56965057607722635728075981)
          ·
            refine ⟨21361896602895988398028493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56965057607722635728075981 21361896602895988398028493)
            ·
              refine ⟨8010711226085995649260685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21361896602895988398028493 8010711226085995649260685)
              ·
                refine ⟨3004016709782248368472757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8010711226085995649260685 3004016709782248368472757)
                ·
                  refine ⟨281626566542085784544321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3004016709782248368472757 281626566542085784544321)
                  ·
                    rfl

theorem cell21_1234048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_1234048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234048 prefixEnd_1234048 := by exact prefixLift 1234048
  have htrace : WordTrace (prefixWord ++ tailWord_1234048) baseStart_1234048 baseEnd_1234048 := by
    simpa [prefixWord, tailWord_1234048, baseEnd_1234048] using wordTrace_append hprefix tailTrace_1234048
  have hstable : (prefixWord ++ tailWord_1234048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234048).length < 2 ^ (prefixWord ++ tailWord_1234048).sum := by decide
  have hdescent : baseEnd_1234048 < baseStart_1234048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234110 : List Nat := [4, 2, 1, 1, 3, 1, 1, 8]
def baseStart_1234110 : Nat := 118140960795 + 1234110 * 2 ^ 59
def prefixEnd_1234110 : Nat := 4983230072969 + 3 ^ 40 * 1234110 * 2
def baseEnd_1234110 : Nat := 93880238595595818170287

theorem tailTrace_1234110 : CollatzResearch.WordTrace tailWord_1234110 prefixEnd_1234110 93880238595595818170287 := by
  unfold tailWord_1234110
  simp only [CollatzResearch.WordTrace]
  refine ⟨5626461194879714256614473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30007793039358476035277189 5626461194879714256614473)
  ·
    refine ⟨4219845896159785692460855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5626461194879714256614473 4219845896159785692460855)
    ·
      refine ⟨6329768844239678538691283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4219845896159785692460855 6329768844239678538691283)
      ·
        refine ⟨9494653266359517808036925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6329768844239678538691283 9494653266359517808036925)
        ·
          refine ⟨3560494974884819178013847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9494653266359517808036925 3560494974884819178013847)
          ·
            refine ⟨5340742462327228767020771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3560494974884819178013847 5340742462327228767020771)
            ·
              refine ⟨8011113693490843150531157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5340742462327228767020771 8011113693490843150531157)
              ·
                refine ⟨93880238595595818170287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8011113693490843150531157 93880238595595818170287)
                ·
                  rfl

theorem cell21_1234110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_1234110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234110 prefixEnd_1234110 := by exact prefixLift 1234110
  have htrace : WordTrace (prefixWord ++ tailWord_1234110) baseStart_1234110 baseEnd_1234110 := by
    simpa [prefixWord, tailWord_1234110, baseEnd_1234110] using wordTrace_append hprefix tailTrace_1234110
  have hstable : (prefixWord ++ tailWord_1234110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234110).length < 2 ^ (prefixWord ++ tailWord_1234110).sum := by decide
  have hdescent : baseEnd_1234110 < baseStart_1234110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234113 : List Nat := [1, 2, 6, 1, 1, 2, 1, 3, 4]
def baseStart_1234113 : Nat := 118140960795 + 1234113 * 2 ^ 59
def prefixEnd_1234113 : Nat := 4983230072969 + 3 ^ 40 * 1234113 * 2
def baseEnd_1234113 : Nat := 281641400427660115960855

theorem tailTrace_1234113 : CollatzResearch.WordTrace tailWord_1234113 prefixEnd_1234113 281641400427660115960855 := by
  unfold tailWord_1234113
  simp only [CollatzResearch.WordTrace]
  refine ⟨45011798978026845565274993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30007865985351230376849995 45011798978026845565274993)
  ·
    refine ⟨33758849233520134173956245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45011798978026845565274993 33758849233520134173956245)
    ·
      refine ⟨1582446057821256289404199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33758849233520134173956245 1582446057821256289404199)
      ·
        refine ⟨2373669086731884434106299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582446057821256289404199 2373669086731884434106299)
        ·
          refine ⟨3560503630097826651159449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373669086731884434106299 3560503630097826651159449)
          ·
            refine ⟨2670377722573369988369587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3560503630097826651159449 2670377722573369988369587)
            ·
              refine ⟨4005566583860054982554381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670377722573369988369587 4005566583860054982554381)
              ·
                refine ⟨1502087468947520618457893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4005566583860054982554381 1502087468947520618457893)
                ·
                  refine ⟨281641400427660115960855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502087468947520618457893 281641400427660115960855)
                  ·
                    rfl

theorem cell21_1234113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_1234113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234113 prefixEnd_1234113 := by exact prefixLift 1234113
  have htrace : WordTrace (prefixWord ++ tailWord_1234113) baseStart_1234113 baseEnd_1234113 := by
    simpa [prefixWord, tailWord_1234113, baseEnd_1234113] using wordTrace_append hprefix tailTrace_1234113
  have hstable : (prefixWord ++ tailWord_1234113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234113).length < 2 ^ (prefixWord ++ tailWord_1234113).sum := by decide
  have hdescent : baseEnd_1234113 < baseStart_1234113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234155 : List Nat := [1, 1, 1, 1, 2, 6, 1, 4, 4]
def baseStart_1234155 : Nat := 118140960795 + 1234155 * 2 ^ 59
def prefixEnd_1234155 : Nat := 4983230072969 + 3 ^ 40 * 1234155 * 2
def baseEnd_1234155 : Nat := 281650985399877376260769

theorem tailTrace_1234155 : CollatzResearch.WordTrace tailWord_1234155 prefixEnd_1234155 281650985399877376260769 := by
  unfold tailWord_1234155
  simp only [CollatzResearch.WordTrace]
  refine ⟨45013330843874686738303919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30008887229249791158869279 45013330843874686738303919)
  ·
    refine ⟨67519996265812030107455879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45013330843874686738303919 67519996265812030107455879)
    ·
      refine ⟨101279994398718045161183819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67519996265812030107455879 101279994398718045161183819)
      ·
        refine ⟨151919991598077067741775729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101279994398718045161183819 151919991598077067741775729)
        ·
          refine ⟨113939993698557800806331797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151919991598077067741775729 113939993698557800806331797)
          ·
            refine ⟨5340937204619896912796803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 113939993698557800806331797 5340937204619896912796803)
            ·
              refine ⟨8011405806929845369195205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5340937204619896912796803 8011405806929845369195205)
              ·
                refine ⟨1502138588799346006724101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8011405806929845369195205 1502138588799346006724101)
                ·
                  refine ⟨281650985399877376260769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502138588799346006724101 281650985399877376260769)
                  ·
                    rfl

theorem cell21_1234155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 4].length) (baseStart_1234155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234155 prefixEnd_1234155 := by exact prefixLift 1234155
  have htrace : WordTrace (prefixWord ++ tailWord_1234155) baseStart_1234155 baseEnd_1234155 := by
    simpa [prefixWord, tailWord_1234155, baseEnd_1234155] using wordTrace_append hprefix tailTrace_1234155
  have hstable : (prefixWord ++ tailWord_1234155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234155).length < 2 ^ (prefixWord ++ tailWord_1234155).sum := by decide
  have hdescent : baseEnd_1234155 < baseStart_1234155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234237 : List Nat := [1, 4, 1, 5, 2, 1, 2, 5]
def baseStart_1234237 : Nat := 118140960795 + 1234237 * 2 ^ 59
def prefixEnd_1234237 : Nat := 4983230072969 + 3 ^ 40 * 1234237 * 2
def baseEnd_1234237 : Nat := 93889899639021151964645

theorem tailTrace_1234237 : CollatzResearch.WordTrace tailWord_1234237 prefixEnd_1234237 93889899639021151964645 := by
  unfold tailWord_1234237
  simp only [CollatzResearch.WordTrace]
  refine ⟨45016321629577614742788965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30010881086385076495192643 45016321629577614742788965)
  ·
    refine ⟨8440560305545802764272931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45016321629577614742788965 8440560305545802764272931)
    ·
      refine ⟨12660840458318704146409397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8440560305545802764272931 12660840458318704146409397)
      ·
        refine ⟨1186953792967378513725881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12660840458318704146409397 1186953792967378513725881)
        ·
          refine ⟨890215344725533885294411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1186953792967378513725881 890215344725533885294411)
          ·
            refine ⟨1335323017088300827941617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890215344725533885294411 1335323017088300827941617)
            ·
              refine ⟨1001492262816225620956213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1335323017088300827941617 1001492262816225620956213)
              ·
                refine ⟨93889899639021151964645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1001492262816225620956213 93889899639021151964645)
                ·
                  rfl

theorem cell21_1234237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 5].length) (baseStart_1234237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234237 prefixEnd_1234237 := by exact prefixLift 1234237
  have htrace : WordTrace (prefixWord ++ tailWord_1234237) baseStart_1234237 baseEnd_1234237 := by
    simpa [prefixWord, tailWord_1234237, baseEnd_1234237] using wordTrace_append hprefix tailTrace_1234237
  have hstable : (prefixWord ++ tailWord_1234237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234237).length < 2 ^ (prefixWord ++ tailWord_1234237).sum := by decide
  have hdescent : baseEnd_1234237 < baseStart_1234237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234282 : List Nat := [3, 1, 3, 3, 2, 2, 2, 1, 4]
def baseStart_1234282 : Nat := 118140960795 + 1234282 * 2 ^ 59
def prefixEnd_1234282 : Nat := 4983230072969 + 3 ^ 40 * 1234282 * 2
def baseEnd_1234282 : Nat := 281679968530153377643843

theorem tailTrace_1234282 : CollatzResearch.WordTrace tailWord_1234282 prefixEnd_1234282 281679968530153377643843 := by
  unfold tailWord_1234282
  simp only [CollatzResearch.WordTrace]
  refine ⟨11254490728603646857044275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30011975276276391618784733 11254490728603646857044275)
  ·
    refine ⟨16881736092905470285566413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11254490728603646857044275 16881736092905470285566413)
    ·
      refine ⟨6330651034839551357087405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16881736092905470285566413 6330651034839551357087405)
      ·
        refine ⟨2373994138064831758907777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6330651034839551357087405 2373994138064831758907777)
        ·
          refine ⟨1780495603548623819180833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2373994138064831758907777 1780495603548623819180833)
          ·
            refine ⟨1335371702661467864385625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1780495603548623819180833 1335371702661467864385625)
            ·
              refine ⟨1001528776996100898289219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1335371702661467864385625 1001528776996100898289219)
              ·
                refine ⟨1502293165494151347433829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1001528776996100898289219 1502293165494151347433829)
                ·
                  refine ⟨281679968530153377643843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502293165494151347433829 281679968530153377643843)
                  ·
                    rfl

theorem cell21_1234282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_1234282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234282 prefixEnd_1234282 := by exact prefixLift 1234282
  have htrace : WordTrace (prefixWord ++ tailWord_1234282) baseStart_1234282 baseEnd_1234282 := by
    simpa [prefixWord, tailWord_1234282, baseEnd_1234282] using wordTrace_append hprefix tailTrace_1234282
  have hstable : (prefixWord ++ tailWord_1234282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234282).length < 2 ^ (prefixWord ++ tailWord_1234282).sum := by decide
  have hdescent : baseEnd_1234282 < baseStart_1234282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234324 : List Nat := [2, 4, 2, 1, 2, 1, 1, 4, 4]
def baseStart_1234324 : Nat := 118140960795 + 1234324 * 2 ^ 59
def prefixEnd_1234324 : Nat := 4983230072969 + 3 ^ 40 * 1234324 * 2
def baseEnd_1234324 : Nat := 281689553502370637943757

theorem tailTrace_1234324 : CollatzResearch.WordTrace tailWord_1234324 prefixEnd_1234324 281689553502370637943757 := by
  unfold tailWord_1234324
  simp only [CollatzResearch.WordTrace]
  refine ⟨22509747390131214300603013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30012996520174952400804017 22509747390131214300603013)
  ·
    refine ⟨4220577635649602681363065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22509747390131214300603013 4220577635649602681363065)
    ·
      refine ⟨3165433226737202011022299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4220577635649602681363065 3165433226737202011022299)
      ·
        refine ⟨4748149840105803016533449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3165433226737202011022299 4748149840105803016533449)
        ·
          refine ⟨3561112380079352262400087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4748149840105803016533449 3561112380079352262400087)
          ·
            refine ⟨5341668570119028393600131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3561112380079352262400087 5341668570119028393600131)
            ·
              refine ⟨8012502855178542590400197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5341668570119028393600131 8012502855178542590400197)
              ·
                refine ⟨1502344285345976735700037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8012502855178542590400197 1502344285345976735700037)
                ·
                  refine ⟨281689553502370637943757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502344285345976735700037 281689553502370637943757)
                  ·
                    rfl

theorem cell21_1234324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_1234324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234324 prefixEnd_1234324 := by exact prefixLift 1234324
  have htrace : WordTrace (prefixWord ++ tailWord_1234324) baseStart_1234324 baseEnd_1234324 := by
    simpa [prefixWord, tailWord_1234324, baseEnd_1234324] using wordTrace_append hprefix tailTrace_1234324
  have hstable : (prefixWord ++ tailWord_1234324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234324).length < 2 ^ (prefixWord ++ tailWord_1234324).sum := by decide
  have hdescent : baseEnd_1234324 < baseStart_1234324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234338 : List Nat := [3, 3, 1, 2, 1, 2, 3, 6]
def baseStart_1234338 : Nat := 118140960795 + 1234338 * 2 ^ 59
def prefixEnd_1234338 : Nat := 4983230072969 + 3 ^ 40 * 1234338 * 2
def baseEnd_1234338 : Nat := 93897582831036574903465

theorem tailTrace_1234338 : CollatzResearch.WordTrace tailWord_1234338 prefixEnd_1234338 93897582831036574903465 := by
  unfold tailWord_1234338
  simp only [CollatzResearch.WordTrace]
  refine ⟨11255001350552927248053917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30013336934807805994810445 11255001350552927248053917)
  ·
    refine ⟨4220625506457347718020219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11255001350552927248053917 4220625506457347718020219)
    ·
      refine ⟨6330938259686021577030329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4220625506457347718020219 6330938259686021577030329)
      ·
        refine ⟨4748203694764516182772747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6330938259686021577030329 4748203694764516182772747)
        ·
          refine ⟨7122305542146774274159121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4748203694764516182772747 7122305542146774274159121)
          ·
            refine ⟨5341729156610080705619341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7122305542146774274159121 5341729156610080705619341)
            ·
              refine ⟨2003148433728780264607253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5341729156610080705619341 2003148433728780264607253)
              ·
                refine ⟨93897582831036574903465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2003148433728780264607253 93897582831036574903465)
                ·
                  rfl

theorem cell21_1234338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_1234338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234338 prefixEnd_1234338 := by exact prefixLift 1234338
  have htrace : WordTrace (prefixWord ++ tailWord_1234338) baseStart_1234338 baseEnd_1234338 := by
    simpa [prefixWord, tailWord_1234338, baseEnd_1234338] using wordTrace_append hprefix tailTrace_1234338
  have hstable : (prefixWord ++ tailWord_1234338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234338).length < 2 ^ (prefixWord ++ tailWord_1234338).sum := by decide
  have hdescent : baseEnd_1234338 < baseStart_1234338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234383 : List Nat := [1, 1, 2, 1, 1, 4, 5, 2, 4]
def baseStart_1234383 : Nat := 118140960795 + 1234383 * 2 ^ 59
def prefixEnd_1234383 : Nat := 4983230072969 + 3 ^ 40 * 1234383 * 2
def baseEnd_1234383 : Nat := 281703018106199646460303

theorem tailTrace_1234383 : CollatzResearch.WordTrace tailWord_1234383 prefixEnd_1234383 281703018106199646460303 := by
  unfold tailWord_1234383
  simp only [CollatzResearch.WordTrace]
  refine ⟨45021646687048681677603803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30014431124699121118402535 45021646687048681677603803)
  ·
    refine ⟨67532470030573022516405705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45021646687048681677603803 67532470030573022516405705)
    ·
      refine ⟨50649352522929766887304279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67532470030573022516405705 50649352522929766887304279)
      ·
        refine ⟨75974028784394650330956419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50649352522929766887304279 75974028784394650330956419)
        ·
          refine ⟨113961043176591975496434629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75974028784394650330956419 113961043176591975496434629)
          ·
            refine ⟨21367695595610995405581493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113961043176591975496434629 21367695595610995405581493)
            ·
              refine ⟨2003221462088530819273265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21367695595610995405581493 2003221462088530819273265)
              ·
                refine ⟨1502416096566398114454949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2003221462088530819273265 1502416096566398114454949)
                ·
                  refine ⟨281703018106199646460303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502416096566398114454949 281703018106199646460303)
                  ·
                    rfl

theorem cell21_1234383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 4].length) (baseStart_1234383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234383 prefixEnd_1234383 := by exact prefixLift 1234383
  have htrace : WordTrace (prefixWord ++ tailWord_1234383) baseStart_1234383 baseEnd_1234383 := by
    simpa [prefixWord, tailWord_1234383, baseEnd_1234383] using wordTrace_append hprefix tailTrace_1234383
  have hstable : (prefixWord ++ tailWord_1234383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234383).length < 2 ^ (prefixWord ++ tailWord_1234383).sum := by decide
  have hdescent : baseEnd_1234383 < baseStart_1234383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234411 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 7]
def baseStart_1234411 : Nat := 118140960795 + 1234411 * 2 ^ 59
def prefixEnd_1234411 : Nat := 4983230072969 + 3 ^ 40 * 1234411 * 2
def baseEnd_1234411 : Nat := 281709408087677819993579

theorem tailTrace_1234411 : CollatzResearch.WordTrace tailWord_1234411 prefixEnd_1234411 281709408087677819993579 := by
  unfold tailWord_1234411
  simp only [CollatzResearch.WordTrace]
  refine ⟨45022667930947242459623087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30015111953964828306415391 45022667930947242459623087)
  ·
    refine ⟨67534001896420863689434631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45022667930947242459623087 67534001896420863689434631)
    ·
      refine ⟨101301002844631295534151947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67534001896420863689434631 101301002844631295534151947)
      ·
        refine ⟨151951504266946943301227921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101301002844631295534151947 151951504266946943301227921)
        ·
          refine ⟨113963628200210207475920941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151951504266946943301227921 113963628200210207475920941)
          ·
            refine ⟨42736360575078827803470353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113963628200210207475920941 42736360575078827803470353)
            ·
              refine ⟨32052270431309120852602765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42736360575078827803470353 32052270431309120852602765)
              ·
                refine ⟨12019601411740920319726037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32052270431309120852602765 12019601411740920319726037)
                ·
                  refine ⟨281709408087677819993579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12019601411740920319726037 281709408087677819993579)
                  ·
                    rfl

theorem cell21_1234411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 7].length) (baseStart_1234411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234411 prefixEnd_1234411 := by exact prefixLift 1234411
  have htrace : WordTrace (prefixWord ++ tailWord_1234411) baseStart_1234411 baseEnd_1234411 := by
    simpa [prefixWord, tailWord_1234411, baseEnd_1234411] using wordTrace_append hprefix tailTrace_1234411
  have hstable : (prefixWord ++ tailWord_1234411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234411).length < 2 ^ (prefixWord ++ tailWord_1234411).sum := by decide
  have hdescent : baseEnd_1234411 < baseStart_1234411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234538 : List Nat := [3, 1, 3, 2, 1, 3, 2, 3, 3]
def baseStart_1234538 : Nat := 118140960795 + 1234538 * 2 ^ 59
def prefixEnd_1234538 : Nat := 4983230072969 + 3 ^ 40 * 1234538 * 2
def baseEnd_1234538 : Nat := 281738391217953821376653

theorem tailTrace_1234538 : CollatzResearch.WordTrace tailWord_1234538 prefixEnd_1234538 281738391217953821376653 := by
  unfold tailWord_1234538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11256825000371785787374067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30018200000991428766330845 11256825000371785787374067)
  ·
    refine ⟨16885237500557678681061101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11256825000371785787374067 16885237500557678681061101)
    ·
      refine ⟨6331964062709129505397913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16885237500557678681061101 6331964062709129505397913)
      ·
        refine ⟨4748973047031847129048435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6331964062709129505397913 4748973047031847129048435)
        ·
          refine ⟨7123459570547770693572653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4748973047031847129048435 7123459570547770693572653)
          ·
            refine ⟨2671297338955414010089745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7123459570547770693572653 2671297338955414010089745)
            ·
              refine ⟨2003473004216560507567309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2671297338955414010089745 2003473004216560507567309)
              ·
                refine ⟨751302376581210190337741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2003473004216560507567309 751302376581210190337741)
                ·
                  refine ⟨281738391217953821376653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 751302376581210190337741 281738391217953821376653)
                  ·
                    rfl

theorem cell21_1234538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_1234538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234538 prefixEnd_1234538 := by exact prefixLift 1234538
  have htrace : WordTrace (prefixWord ++ tailWord_1234538) baseStart_1234538 baseEnd_1234538 := by
    simpa [prefixWord, tailWord_1234538, baseEnd_1234538] using wordTrace_append hprefix tailTrace_1234538
  have hstable : (prefixWord ++ tailWord_1234538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234538).length < 2 ^ (prefixWord ++ tailWord_1234538).sum := by decide
  have hdescent : baseEnd_1234538 < baseStart_1234538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234597 : List Nat := [1, 3, 1, 2, 1, 2, 5, 3, 3]
def baseStart_1234597 : Nat := 118140960795 + 1234597 * 2 ^ 59
def prefixEnd_1234597 : Nat := 4983230072969 + 3 ^ 40 * 1234597 * 2
def baseEnd_1234597 : Nat := 281751855821782829893199

theorem tailTrace_1234597 : CollatzResearch.WordTrace tailWord_1234597 prefixEnd_1234597 281751855821782829893199 := by
  unfold tailWord_1234597
  simp only [CollatzResearch.WordTrace]
  refine ⟨45029451908273396225894045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30019634605515597483929363 45029451908273396225894045)
  ·
    refine ⟨16886044465602523584710267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45029451908273396225894045 16886044465602523584710267)
    ·
      refine ⟨25329066698403785377065401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16886044465602523584710267 25329066698403785377065401)
      ·
        refine ⟨18996800023802839032799051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25329066698403785377065401 18996800023802839032799051)
        ·
          refine ⟨28495200035704258549198577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18996800023802839032799051 28495200035704258549198577)
          ·
            refine ⟨21371400026778193911898933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28495200035704258549198577 21371400026778193911898933)
            ·
              refine ⟨2003568752510455679240525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21371400026778193911898933 2003568752510455679240525)
              ·
                refine ⟨751338282191420879715197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2003568752510455679240525 751338282191420879715197)
                ·
                  refine ⟨281751855821782829893199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 751338282191420879715197 281751855821782829893199)
                  ·
                    rfl

theorem cell21_1234597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_1234597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234597 prefixEnd_1234597 := by exact prefixLift 1234597
  have htrace : WordTrace (prefixWord ++ tailWord_1234597) baseStart_1234597 baseEnd_1234597 := by
    simpa [prefixWord, tailWord_1234597, baseEnd_1234597] using wordTrace_append hprefix tailTrace_1234597
  have hstable : (prefixWord ++ tailWord_1234597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234597).length < 2 ^ (prefixWord ++ tailWord_1234597).sum := by decide
  have hdescent : baseEnd_1234597 < baseStart_1234597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234600 : List Nat := [2, 1, 7, 1, 1, 2, 7]
def baseStart_1234600 : Nat := 118140960795 + 1234600 * 2 ^ 59
def prefixEnd_1234600 : Nat := 4983230072969 + 3 ^ 40 * 1234600 * 2
def baseEnd_1234600 : Nat := 31305837829183943482577

theorem tailTrace_1234600 : CollatzResearch.WordTrace tailWord_1234600 prefixEnd_1234600 31305837829183943482577 := by
  unfold tailWord_1234600
  simp only [CollatzResearch.WordTrace]
  refine ⟨22514780663631263869126627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30019707551508351825502169 22514780663631263869126627)
  ·
    refine ⟨33772170995446895803689941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22514780663631263869126627 33772170995446895803689941)
    ·
      refine ⟨791535257705786620398983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 33772170995446895803689941 791535257705786620398983)
      ·
        refine ⟨1187302886558679930598475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791535257705786620398983 1187302886558679930598475)
        ·
          refine ⟨1780954329838019895897713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187302886558679930598475 1780954329838019895897713)
          ·
            refine ⟨1335715747378514921923285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1780954329838019895897713 1335715747378514921923285)
            ·
              refine ⟨31305837829183943482577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1335715747378514921923285 31305837829183943482577)
              ·
                rfl

theorem cell21_1234600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 7].length) (baseStart_1234600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234600 prefixEnd_1234600 := by exact prefixLift 1234600
  have htrace : WordTrace (prefixWord ++ tailWord_1234600) baseStart_1234600 baseEnd_1234600 := by
    simpa [prefixWord, tailWord_1234600, baseEnd_1234600] using wordTrace_append hprefix tailTrace_1234600
  have hstable : (prefixWord ++ tailWord_1234600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234600).length < 2 ^ (prefixWord ++ tailWord_1234600).sum := by decide
  have hdescent : baseEnd_1234600 < baseStart_1234600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234608 : List Nat := [2, 1, 1, 1, 2, 1, 13]
def baseStart_1234608 : Nat := 118140960795 + 1234608 * 2 ^ 59
def prefixEnd_1234608 : Nat := 4983230072969 + 3 ^ 40 * 1234608 * 2
def baseEnd_1234608 : Nat := 31306040685738806134427

theorem tailTrace_1234608 : CollatzResearch.WordTrace tailWord_1234608 prefixEnd_1234608 31306040685738806134427 := by
  unfold tailWord_1234608
  simp only [CollatzResearch.WordTrace]
  refine ⟨22514926555616772552272239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30019902074155696736362985 22514926555616772552272239)
  ·
    refine ⟨33772389833425158828408359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22514926555616772552272239 33772389833425158828408359)
    ·
      refine ⟨50658584750137738242612539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33772389833425158828408359 50658584750137738242612539)
      ·
        refine ⟨75987877125206607363918809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50658584750137738242612539 75987877125206607363918809)
        ·
          refine ⟨56990907843904955522939107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75987877125206607363918809 56990907843904955522939107)
          ·
            refine ⟨85486361765857433284408661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56990907843904955522939107 85486361765857433284408661)
            ·
              refine ⟨31306040685738806134427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 85486361765857433284408661 31306040685738806134427)
              ·
                rfl

theorem cell21_1234608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 13].length) (baseStart_1234608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234608 prefixEnd_1234608 := by exact prefixLift 1234608
  have htrace : WordTrace (prefixWord ++ tailWord_1234608) baseStart_1234608 baseEnd_1234608 := by
    simpa [prefixWord, tailWord_1234608, baseEnd_1234608] using wordTrace_append hprefix tailTrace_1234608
  have hstable : (prefixWord ++ tailWord_1234608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234608).length < 2 ^ (prefixWord ++ tailWord_1234608).sum := by decide
  have hdescent : baseEnd_1234608 < baseStart_1234608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234614 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_1234614 : Nat := 118140960795 + 1234614 * 2 ^ 59
def prefixEnd_1234614 : Nat := 4983230072969 + 3 ^ 40 * 1234614 * 2
def baseEnd_1234614 : Nat := 281755735453394578109831

theorem tailTrace_1234614 : CollatzResearch.WordTrace tailWord_1234614 prefixEnd_1234614 281755735453394578109831 := by
  unfold tailWord_1234614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2814379496825738008078931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30020047966141205419508597 2814379496825738008078931)
  ·
    refine ⟨4221569245238607012118397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2814379496825738008078931 4221569245238607012118397)
    ·
      refine ⟨1583088466964477629544399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4221569245238607012118397 1583088466964477629544399)
      ·
        refine ⟨2374632700446716444316599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1583088466964477629544399 2374632700446716444316599)
        ·
          refine ⟨3561949050670074666474899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374632700446716444316599 3561949050670074666474899)
          ·
            refine ⟨5342923576005111999712349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3561949050670074666474899 5342923576005111999712349)
            ·
              refine ⟨2003596341001916999892131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5342923576005111999712349 2003596341001916999892131)
              ·
                refine ⟨3005394511502875499838197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003596341001916999892131 3005394511502875499838197)
                ·
                  refine ⟨281755735453394578109831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3005394511502875499838197 281755735453394578109831)
                  ·
                    rfl

theorem cell21_1234614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_1234614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234614 prefixEnd_1234614 := by exact prefixLift 1234614
  have htrace : WordTrace (prefixWord ++ tailWord_1234614) baseStart_1234614 baseEnd_1234614 := by
    simpa [prefixWord, tailWord_1234614, baseEnd_1234614] using wordTrace_append hprefix tailTrace_1234614
  have hstable : (prefixWord ++ tailWord_1234614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234614).length < 2 ^ (prefixWord ++ tailWord_1234614).sum := by decide
  have hdescent : baseEnd_1234614 < baseStart_1234614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234639 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 5]
def baseStart_1234639 : Nat := 118140960795 + 1234639 * 2 ^ 59
def prefixEnd_1234639 : Nat := 4983230072969 + 3 ^ 40 * 1234639 * 2
def baseEnd_1234639 : Nat := 281761440794000090193113

theorem tailTrace_1234639 : CollatzResearch.WordTrace tailWord_1234639 prefixEnd_1234639 281761440794000090193113 := by
  unfold tailWord_1234639
  simp only [CollatzResearch.WordTrace]
  refine ⟨45030983774121237398922971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30020655849414158265948647 45030983774121237398922971)
  ·
    refine ⟨67546475661181856098384457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45030983774121237398922971 67546475661181856098384457)
    ·
      refine ⟨50659856745886392073788343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67546475661181856098384457 50659856745886392073788343)
      ·
        refine ⟨75989785118829588110682515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50659856745886392073788343 75989785118829588110682515)
        ·
          refine ⟨113984677678244382166023773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75989785118829588110682515 113984677678244382166023773)
          ·
            refine ⟨42744254129341643312258915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113984677678244382166023773 42744254129341643312258915)
            ·
              refine ⟨64116381194012464968388373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42744254129341643312258915 64116381194012464968388373)
              ·
                refine ⟨3005455368469334295393205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64116381194012464968388373 3005455368469334295393205)
                ·
                  refine ⟨281761440794000090193113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3005455368469334295393205 281761440794000090193113)
                  ·
                    rfl

theorem cell21_1234639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 5].length) (baseStart_1234639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234639 prefixEnd_1234639 := by exact prefixLift 1234639
  have htrace : WordTrace (prefixWord ++ tailWord_1234639) baseStart_1234639 baseEnd_1234639 := by
    simpa [prefixWord, tailWord_1234639, baseEnd_1234639] using wordTrace_append hprefix tailTrace_1234639
  have hstable : (prefixWord ++ tailWord_1234639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234639).length < 2 ^ (prefixWord ++ tailWord_1234639).sum := by decide
  have hdescent : baseEnd_1234639 < baseStart_1234639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234673 : List Nat := [1, 2, 2, 2, 2, 4, 1, 4, 3]
def baseStart_1234673 : Nat := 118140960795 + 1234673 * 2 ^ 59
def prefixEnd_1234673 : Nat := 4983230072969 + 3 ^ 40 * 1234673 * 2
def baseEnd_1234673 : Nat := 281769200057223586626377

theorem tailTrace_1234673 : CollatzResearch.WordTrace tailWord_1234673 prefixEnd_1234673 281769200057223586626377 := by
  unfold tailWord_1234673
  simp only [CollatzResearch.WordTrace]
  refine ⟨45032223855998061205660673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30021482570665374137107115 45032223855998061205660673)
  ·
    refine ⟨33774167891998545904245505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45032223855998061205660673 33774167891998545904245505)
    ·
      refine ⟨25330625918998909428184129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33774167891998545904245505 25330625918998909428184129)
      ·
        refine ⟨18997969439249182071138097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25330625918998909428184129 18997969439249182071138097)
        ·
          refine ⟨14248477079436886553353573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18997969439249182071138097 14248477079436886553353573)
          ·
            refine ⟨2671589452394416228753795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14248477079436886553353573 2671589452394416228753795)
            ·
              refine ⟨4007384178591624343130693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2671589452394416228753795 4007384178591624343130693)
              ·
                refine ⟨751384533485929564337005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4007384178591624343130693 751384533485929564337005)
                ·
                  refine ⟨281769200057223586626377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 751384533485929564337005 281769200057223586626377)
                  ·
                    rfl

theorem cell21_1234673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 3].length) (baseStart_1234673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234673 prefixEnd_1234673 := by exact prefixLift 1234673
  have htrace : WordTrace (prefixWord ++ tailWord_1234673) baseStart_1234673 baseEnd_1234673 := by
    simpa [prefixWord, tailWord_1234673, baseEnd_1234673] using wordTrace_append hprefix tailTrace_1234673
  have hstable : (prefixWord ++ tailWord_1234673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234673).length < 2 ^ (prefixWord ++ tailWord_1234673).sum := by decide
  have hdescent : baseEnd_1234673 < baseStart_1234673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234676 : List Nat := [2, 6, 1, 1, 1, 3, 1, 6]
def baseStart_1234676 : Nat := 118140960795 + 1234676 * 2 ^ 59
def prefixEnd_1234676 : Nat := 4983230072969 + 3 ^ 40 * 1234676 * 2
def baseEnd_1234676 : Nat := 93923294899365416025457

theorem tailTrace_1234676 : CollatzResearch.WordTrace tailWord_1234676 prefixEnd_1234676 93923294899365416025457 := by
  unfold tailWord_1234676
  simp only [CollatzResearch.WordTrace]
  refine ⟨22516166637493596359009941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30021555516658128478679921 22516166637493596359009941)
  ·
    refine ⟨1055445311132512329328591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22516166637493596359009941 1055445311132512329328591)
    ·
      refine ⟨1583167966698768493992887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1055445311132512329328591 1583167966698768493992887)
      ·
        refine ⟨2374751950048152740989331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1583167966698768493992887 2374751950048152740989331)
        ·
          refine ⟨3562127925072229111483997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374751950048152740989331 3562127925072229111483997)
          ·
            refine ⟨1335797971902085916806499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3562127925072229111483997 1335797971902085916806499)
            ·
              refine ⟨2003696957853128875209749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335797971902085916806499 2003696957853128875209749)
              ·
                refine ⟨93923294899365416025457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2003696957853128875209749 93923294899365416025457)
                ·
                  rfl

theorem cell21_1234676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 6].length) (baseStart_1234676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234676 prefixEnd_1234676 := by exact prefixLift 1234676
  have htrace : WordTrace (prefixWord ++ tailWord_1234676) baseStart_1234676 baseEnd_1234676 := by
    simpa [prefixWord, tailWord_1234676, baseEnd_1234676] using wordTrace_append hprefix tailTrace_1234676
  have hstable : (prefixWord ++ tailWord_1234676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234676).length < 2 ^ (prefixWord ++ tailWord_1234676).sum := by decide
  have hdescent : baseEnd_1234676 < baseStart_1234676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234732 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 5]
def baseStart_1234732 : Nat := 118140960795 + 1234732 * 2 ^ 59
def prefixEnd_1234732 : Nat := 4983230072969 + 3 ^ 40 * 1234732 * 2
def baseEnd_1234732 : Nat := 281782664661052595142923

theorem tailTrace_1234732 : CollatzResearch.WordTrace tailWord_1234732 prefixEnd_1234732 281782664661052595142923 := by
  unfold tailWord_1234732
  simp only [CollatzResearch.WordTrace]
  refine ⟨22517187881392157141029225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30022917175189542854705633 22517187881392157141029225)
  ·
    refine ⟨16887890911044117855771919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22517187881392157141029225 16887890911044117855771919)
    ·
      refine ⟨25331836366566176783657879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16887890911044117855771919 25331836366566176783657879)
      ·
        refine ⟨37997754549849265175486819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25331836366566176783657879 37997754549849265175486819)
        ·
          refine ⟨56996631824773897763230229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37997754549849265175486819 56996631824773897763230229)
          ·
            refine ⟨2671717116786276457651417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56996631824773897763230229 2671717116786276457651417)
            ·
              refine ⟨2003787837589707343238563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2671717116786276457651417 2003787837589707343238563)
              ·
                refine ⟨3005681756384561014857845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003787837589707343238563 3005681756384561014857845)
                ·
                  refine ⟨281782664661052595142923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3005681756384561014857845 281782664661052595142923)
                  ·
                    rfl

theorem cell21_1234732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_1234732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234732 prefixEnd_1234732 := by exact prefixLift 1234732
  have htrace : WordTrace (prefixWord ++ tailWord_1234732) baseStart_1234732 baseEnd_1234732 := by
    simpa [prefixWord, tailWord_1234732, baseEnd_1234732] using wordTrace_append hprefix tailTrace_1234732
  have hstable : (prefixWord ++ tailWord_1234732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234732).length < 2 ^ (prefixWord ++ tailWord_1234732).sum := by decide
  have hdescent : baseEnd_1234732 < baseStart_1234732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234839 : List Nat := [1, 1, 3, 3, 1, 4, 2, 2, 4]
def baseStart_1234839 : Nat := 118140960795 + 1234839 * 2 ^ 59
def prefixEnd_1234839 : Nat := 4983230072969 + 3 ^ 40 * 1234839 * 2
def baseEnd_1234839 : Nat := 281807083518844186859371

theorem tailTrace_1234839 : CollatzResearch.WordTrace tailWord_1234839 prefixEnd_1234839 281807083518844186859371 := by
  unfold tailWord_1234839
  simp only [CollatzResearch.WordTrace]
  refine ⟨45038278373396671556203571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30025518915597781037469047 45038278373396671556203571)
  ·
    refine ⟨67557417560095007334305357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45038278373396671556203571 67557417560095007334305357)
    ·
      refine ⟨25334031585035627750364509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67557417560095007334305357 25334031585035627750364509)
      ·
        refine ⟨9500261844388360406386691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25334031585035627750364509 9500261844388360406386691)
        ·
          refine ⟨14250392766582540609580037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9500261844388360406386691 14250392766582540609580037)
          ·
            refine ⟨2671948643734226364296257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14250392766582540609580037 2671948643734226364296257)
            ·
              refine ⟨2003961482800669773222193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2671948643734226364296257 2003961482800669773222193)
              ·
                refine ⟨1502971112100502329916645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2003961482800669773222193 1502971112100502329916645)
                ·
                  refine ⟨281807083518844186859371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502971112100502329916645 281807083518844186859371)
                  ·
                    rfl

theorem cell21_1234839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 4].length) (baseStart_1234839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234839 prefixEnd_1234839 := by exact prefixLift 1234839
  have htrace : WordTrace (prefixWord ++ tailWord_1234839) baseStart_1234839 baseEnd_1234839 := by
    simpa [prefixWord, tailWord_1234839, baseEnd_1234839] using wordTrace_append hprefix tailTrace_1234839
  have hstable : (prefixWord ++ tailWord_1234839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234839).length < 2 ^ (prefixWord ++ tailWord_1234839).sum := by decide
  have hdescent : baseEnd_1234839 < baseStart_1234839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234842 : List Nat := [3, 1, 1, 4, 2, 1, 4, 2, 3]
def baseStart_1234842 : Nat := 118140960795 + 1234842 * 2 ^ 59
def prefixEnd_1234842 : Nat := 4983230072969 + 3 ^ 40 * 1234842 * 2
def baseEnd_1234842 : Nat := 281807768159716848309365

theorem tailTrace_1234842 : CollatzResearch.WordTrace tailWord_1234842 prefixEnd_1234842 281807768159716848309365 := by
  unfold tailWord_1234842
  simp only [CollatzResearch.WordTrace]
  refine ⟨11259596948096450767140695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30025591861590535379041853 11259596948096450767140695)
  ·
    refine ⟨16889395422144676150711043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11259596948096450767140695 16889395422144676150711043)
    ·
      refine ⟨25334093133217014226066565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16889395422144676150711043 25334093133217014226066565)
      ·
        refine ⟨4750142462478190167387481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25334093133217014226066565 4750142462478190167387481)
        ·
          refine ⟨3562606846858642625540611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4750142462478190167387481 3562606846858642625540611)
          ·
            refine ⟨5343910270287963938310917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562606846858642625540611 5343910270287963938310917)
            ·
              refine ⟨1001983175678993238433297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5343910270287963938310917 1001983175678993238433297)
              ·
                refine ⟨751487381759244928824973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1001983175678993238433297 751487381759244928824973)
                ·
                  refine ⟨281807768159716848309365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 751487381759244928824973 281807768159716848309365)
                  ·
                    rfl

theorem cell21_1234842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_1234842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234842 prefixEnd_1234842 := by exact prefixLift 1234842
  have htrace : WordTrace (prefixWord ++ tailWord_1234842) baseStart_1234842 baseEnd_1234842 := by
    simpa [prefixWord, tailWord_1234842, baseEnd_1234842] using wordTrace_append hprefix tailTrace_1234842
  have hstable : (prefixWord ++ tailWord_1234842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234842).length < 2 ^ (prefixWord ++ tailWord_1234842).sum := by decide
  have hdescent : baseEnd_1234842 < baseStart_1234842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234867 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 5]
def baseStart_1234867 : Nat := 118140960795 + 1234867 * 2 ^ 59
def prefixEnd_1234867 : Nat := 4983230072969 + 3 ^ 40 * 1234867 * 2
def baseEnd_1234867 : Nat := 281813473500322360392647

theorem tailTrace_1234867 : CollatzResearch.WordTrace tailWord_1234867 prefixEnd_1234867 281813473500322360392647 := by
  unfold tailWord_1234867
  simp only [CollatzResearch.WordTrace]
  refine ⟨45039299617295232338222855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30026199744863488225481903 45039299617295232338222855)
  ·
    refine ⟨67558949425942848507334283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45039299617295232338222855 67558949425942848507334283)
    ·
      refine ⟨101338424138914272761001425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67558949425942848507334283 101338424138914272761001425)
      ·
        refine ⟨76003818104185704570751069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101338424138914272761001425 76003818104185704570751069)
        ·
          refine ⟨28501431789069639214031651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76003818104185704570751069 28501431789069639214031651)
          ·
            refine ⟨42752147683604458821047477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28501431789069639214031651 42752147683604458821047477)
            ·
              refine ⟨4008013845337918014473201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42752147683604458821047477 4008013845337918014473201)
              ·
                refine ⟨3006010384003438510854901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4008013845337918014473201 3006010384003438510854901)
                ·
                  refine ⟨281813473500322360392647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3006010384003438510854901 281813473500322360392647)
                  ·
                    rfl

theorem cell21_1234867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 5].length) (baseStart_1234867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234867 prefixEnd_1234867 := by exact prefixLift 1234867
  have htrace : WordTrace (prefixWord ++ tailWord_1234867) baseStart_1234867 baseEnd_1234867 := by
    simpa [prefixWord, tailWord_1234867, baseEnd_1234867] using wordTrace_append hprefix tailTrace_1234867
  have hstable : (prefixWord ++ tailWord_1234867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234867).length < 2 ^ (prefixWord ++ tailWord_1234867).sum := by decide
  have hdescent : baseEnd_1234867 < baseStart_1234867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234901 : List Nat := [1, 3, 2, 3, 2, 1, 2, 4, 3]
def baseStart_1234901 : Nat := 118140960795 + 1234901 * 2 ^ 59
def prefixEnd_1234901 : Nat := 4983230072969 + 3 ^ 40 * 1234901 * 2
def baseEnd_1234901 : Nat := 281821232763545856825911

theorem tailTrace_1234901 : CollatzResearch.WordTrace tailWord_1234901 prefixEnd_1234901 281821232763545856825911 := by
  unfold tailWord_1234901
  simp only [CollatzResearch.WordTrace]
  refine ⟨45040539699172056144960557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30027026466114704096640371 45040539699172056144960557)
  ·
    refine ⟨16890202387189521054360209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45040539699172056144960557 16890202387189521054360209)
    ·
      refine ⟨12667651790392140790770157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16890202387189521054360209 12667651790392140790770157)
      ·
        refine ⟨4750369421397052796538809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12667651790392140790770157 4750369421397052796538809)
        ·
          refine ⟨3562777066047789597404107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4750369421397052796538809 3562777066047789597404107)
          ·
            refine ⟨5344165599071684396106161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562777066047789597404107 5344165599071684396106161)
            ·
              refine ⟨4008124199303763297079621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5344165599071684396106161 4008124199303763297079621)
              ·
                refine ⟨751523287369455618202429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4008124199303763297079621 751523287369455618202429)
                ·
                  refine ⟨281821232763545856825911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 751523287369455618202429 281821232763545856825911)
                  ·
                    rfl

theorem cell21_1234901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_1234901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234901 prefixEnd_1234901 := by exact prefixLift 1234901
  have htrace : WordTrace (prefixWord ++ tailWord_1234901) baseStart_1234901 baseEnd_1234901 := by
    simpa [prefixWord, tailWord_1234901, baseEnd_1234901] using wordTrace_append hprefix tailTrace_1234901
  have hstable : (prefixWord ++ tailWord_1234901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234901).length < 2 ^ (prefixWord ++ tailWord_1234901).sum := by decide
  have hdescent : baseEnd_1234901 < baseStart_1234901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234929 : List Nat := [1, 2, 2, 2, 5, 1, 1, 7]
def baseStart_1234929 : Nat := 118140960795 + 1234929 * 2 ^ 59
def prefixEnd_1234929 : Nat := 4983230072969 + 3 ^ 40 * 1234929 * 2
def baseEnd_1234929 : Nat := 93942540915008010119729

theorem tailTrace_1234929 : CollatzResearch.WordTrace tailWord_1234929 prefixEnd_1234929 93942540915008010119729 := by
  unfold tailWord_1234929
  simp only [CollatzResearch.WordTrace]
  refine ⟨45041560943070616926979841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30027707295380411284653227 45041560943070616926979841)
  ·
    refine ⟨33781170707302962695234881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45041560943070616926979841 33781170707302962695234881)
    ·
      refine ⟨25335878030477222021426161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33781170707302962695234881 25335878030477222021426161)
      ·
        refine ⟨19001908522857916516069621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25335878030477222021426161 19001908522857916516069621)
        ·
          refine ⟨1781428924017929673381527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19001908522857916516069621 1781428924017929673381527)
          ·
            refine ⟨2672143386026894510072291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781428924017929673381527 2672143386026894510072291)
            ·
              refine ⟨4008215079040341765108437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2672143386026894510072291 4008215079040341765108437)
              ·
                refine ⟨93942540915008010119729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4008215079040341765108437 93942540915008010119729)
                ·
                  rfl

theorem cell21_1234929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 7].length) (baseStart_1234929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1234929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1234929 prefixEnd_1234929 := by exact prefixLift 1234929
  have htrace : WordTrace (prefixWord ++ tailWord_1234929) baseStart_1234929 baseEnd_1234929 := by
    simpa [prefixWord, tailWord_1234929, baseEnd_1234929] using wordTrace_append hprefix tailTrace_1234929
  have hstable : (prefixWord ++ tailWord_1234929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234929).length < 2 ^ (prefixWord ++ tailWord_1234929).sum := by decide
  have hdescent : baseEnd_1234929 < baseStart_1234929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235036 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 5]
def baseStart_1235036 : Nat := 118140960795 + 1235036 * 2 ^ 59
def prefixEnd_1235036 : Nat := 4983230072969 + 3 ^ 40 * 1235036 * 2
def baseEnd_1235036 : Nat := 281852041602815622075635

theorem tailTrace_1235036 : CollatzResearch.WordTrace tailWord_1235036 prefixEnd_1235036 281852041602815622075635 := by
  unfold tailWord_1235036
  simp only [CollatzResearch.WordTrace]
  refine ⟨22522731776841487100562481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30030309035788649467416641 22522731776841487100562481)
  ·
    refine ⟨16892048832631115325421861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22522731776841487100562481 16892048832631115325421861)
    ·
      refine ⟨3167259156118334123516599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16892048832631115325421861 3167259156118334123516599)
      ·
        refine ⟨4750888734177501185274899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3167259156118334123516599 4750888734177501185274899)
        ·
          refine ⟨7126333101266251777912349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4750888734177501185274899 7126333101266251777912349)
          ·
            refine ⟨2672374912974844416717131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7126333101266251777912349 2672374912974844416717131)
            ·
              refine ⟨4008562369462266625075697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2672374912974844416717131 4008562369462266625075697)
              ·
                refine ⟨3006421777096699968806773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4008562369462266625075697 3006421777096699968806773)
                ·
                  refine ⟨281852041602815622075635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3006421777096699968806773 281852041602815622075635)
                  ·
                    rfl

theorem cell21_1235036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_1235036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235036 prefixEnd_1235036 := by exact prefixLift 1235036
  have htrace : WordTrace (prefixWord ++ tailWord_1235036) baseStart_1235036 baseEnd_1235036 := by
    simpa [prefixWord, tailWord_1235036, baseEnd_1235036] using wordTrace_append hprefix tailTrace_1235036
  have hstable : (prefixWord ++ tailWord_1235036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235036).length < 2 ^ (prefixWord ++ tailWord_1235036).sum := by decide
  have hdescent : baseEnd_1235036 < baseStart_1235036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235053 : List Nat := [1, 5, 1, 1, 2, 1, 4, 3, 3]
def baseStart_1235053 : Nat := 118140960795 + 1235053 * 2 ^ 59
def prefixEnd_1235053 : Nat := 4983230072969 + 3 ^ 40 * 1235053 * 2
def baseEnd_1235053 : Nat := 281855921234427370292267

theorem tailTrace_1235053 : CollatzResearch.WordTrace tailWord_1235053 prefixEnd_1235053 281855921234427370292267 := by
  unfold tailWord_1235053
  simp only [CollatzResearch.WordTrace]
  refine ⟨45046083594621386104493813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30030722396414257402995875 45046083594621386104493813)
  ·
    refine ⟨4223070336995754947296295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45046083594621386104493813 4223070336995754947296295)
    ·
      refine ⟨6334605505493632420944443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4223070336995754947296295 6334605505493632420944443)
      ·
        refine ⟨9501908258240448631416665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6334605505493632420944443 9501908258240448631416665)
        ·
          refine ⟨7126431193680336473562499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9501908258240448631416665 7126431193680336473562499)
          ·
            refine ⟨10689646790520504710343749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7126431193680336473562499 10689646790520504710343749)
            ·
              refine ⟨2004308773222594633189453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10689646790520504710343749 2004308773222594633189453)
              ·
                refine ⟨751615789958472987446045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2004308773222594633189453 751615789958472987446045)
                ·
                  refine ⟨281855921234427370292267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 751615789958472987446045 281855921234427370292267)
                  ·
                    rfl

theorem cell21_1235053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_1235053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235053 prefixEnd_1235053 := by exact prefixLift 1235053
  have htrace : WordTrace (prefixWord ++ tailWord_1235053) baseStart_1235053 baseEnd_1235053 := by
    simpa [prefixWord, tailWord_1235053, baseEnd_1235053] using wordTrace_append hprefix tailTrace_1235053
  have hstable : (prefixWord ++ tailWord_1235053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235053).length < 2 ^ (prefixWord ++ tailWord_1235053).sum := by decide
  have hdescent : baseEnd_1235053 < baseStart_1235053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235109 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 8]
def baseStart_1235109 : Nat := 118140960795 + 1235109 * 2 ^ 59
def prefixEnd_1235109 : Nat := 4983230072969 + 3 ^ 40 * 1235109 * 2
def baseEnd_1235109 : Nat := 281868701197383717358819

theorem tailTrace_1235109 : CollatzResearch.WordTrace tailWord_1235109 prefixEnd_1235109 281868701197383717358819 := by
  unfold tailWord_1235109
  simp only [CollatzResearch.WordTrace]
  refine ⟨45048126082418507668532381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30032084054945671779021587 45048126082418507668532381)
  ·
    refine ⟨16893047280906940375699643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45048126082418507668532381 16893047280906940375699643)
    ·
      refine ⟨25339570921360410563549465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16893047280906940375699643 25339570921360410563549465)
      ·
        refine ⟨19004678191020307922662099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25339570921360410563549465 19004678191020307922662099)
        ·
          refine ⟨28507017286530461883993149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19004678191020307922662099 28507017286530461883993149)
          ·
            refine ⟨10690131482448923206497431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28507017286530461883993149 10690131482448923206497431)
            ·
              refine ⟨16035197223673384809746147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10690131482448923206497431 16035197223673384809746147)
              ·
                refine ⟨24052795835510077214619221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16035197223673384809746147 24052795835510077214619221)
                ·
                  refine ⟨281868701197383717358819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24052795835510077214619221 281868701197383717358819)
                  ·
                    rfl

theorem cell21_1235109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_1235109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235109 prefixEnd_1235109 := by exact prefixLift 1235109
  have htrace : WordTrace (prefixWord ++ tailWord_1235109) baseStart_1235109 baseEnd_1235109 := by
    simpa [prefixWord, tailWord_1235109, baseEnd_1235109] using wordTrace_append hprefix tailTrace_1235109
  have hstable : (prefixWord ++ tailWord_1235109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235109).length < 2 ^ (prefixWord ++ tailWord_1235109).sum := by decide
  have hdescent : baseEnd_1235109 < baseStart_1235109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235129 : List Nat := [1, 2, 1, 4, 1, 2, 5, 2, 3]
def baseStart_1235129 : Nat := 118140960795 + 1235129 * 2 ^ 59
def prefixEnd_1235129 : Nat := 4983230072969 + 3 ^ 40 * 1235129 * 2
def baseEnd_1235129 : Nat := 281873265469868127025445

theorem tailTrace_1235129 : CollatzResearch.WordTrace tailWord_1235129 prefixEnd_1235129 281873265469868127025445 := by
  unfold tailWord_1235129
  simp only [CollatzResearch.WordTrace]
  refine ⟨45048855542346051084260441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30032570361564034056173627 45048855542346051084260441)
  ·
    refine ⟨33786641656759538313195331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45048855542346051084260441 33786641656759538313195331)
    ·
      refine ⟨50679962485139307469792997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33786641656759538313195331 50679962485139307469792997)
      ·
        refine ⟨9502492965963620150586187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50679962485139307469792997 9502492965963620150586187)
        ·
          refine ⟨14253739448945430225879281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9502492965963620150586187 14253739448945430225879281)
          ·
            refine ⟨10690304586709072669409461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14253739448945430225879281 10690304586709072669409461)
            ·
              refine ⟨1002216055003975562757137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10690304586709072669409461 1002216055003975562757137)
              ·
                refine ⟨751662041252981672067853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1002216055003975562757137 751662041252981672067853)
                ·
                  refine ⟨281873265469868127025445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 751662041252981672067853 281873265469868127025445)
                  ·
                    rfl

theorem cell21_1235129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 3].length) (baseStart_1235129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235129 prefixEnd_1235129 := by exact prefixLift 1235129
  have htrace : WordTrace (prefixWord ++ tailWord_1235129) baseStart_1235129 baseEnd_1235129 := by
    simpa [prefixWord, tailWord_1235129, baseEnd_1235129] using wordTrace_append hprefix tailTrace_1235129
  have hstable : (prefixWord ++ tailWord_1235129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235129).length < 2 ^ (prefixWord ++ tailWord_1235129).sum := by decide
  have hdescent : baseEnd_1235129 < baseStart_1235129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235185 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 6]
def baseStart_1235185 : Nat := 118140960795 + 1235185 * 2 ^ 59
def prefixEnd_1235185 : Nat := 4983230072969 + 3 ^ 40 * 1235185 * 2
def baseEnd_1235185 : Nat := 281886045432824474091997

theorem tailTrace_1235185 : CollatzResearch.WordTrace tailWord_1235185 prefixEnd_1235185 281886045432824474091997 := by
  unfold tailWord_1235185
  simp only [CollatzResearch.WordTrace]
  refine ⟨45050898030143172648299009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30033932020095448432199339 45050898030143172648299009)
  ·
    refine ⟨33788173522607379486224257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45050898030143172648299009 33788173522607379486224257)
    ·
      refine ⟨25341130141955534614668193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33788173522607379486224257 25341130141955534614668193)
      ·
        refine ⟨19005847606466650961001145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25341130141955534614668193 19005847606466650961001145)
        ·
          refine ⟨14254385704849988220750859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19005847606466650961001145 14254385704849988220750859)
          ·
            refine ⟨21381578557274982331126289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14254385704849988220750859 21381578557274982331126289)
            ·
              refine ⟨16036183917956236748344717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21381578557274982331126289 16036183917956236748344717)
              ·
                refine ⟨6013568969233588780629269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16036183917956236748344717 6013568969233588780629269)
                ·
                  refine ⟨281886045432824474091997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6013568969233588780629269 281886045432824474091997)
                  ·
                    rfl

theorem cell21_1235185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_1235185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235185 prefixEnd_1235185 := by exact prefixLift 1235185
  have htrace : WordTrace (prefixWord ++ tailWord_1235185) baseStart_1235185 baseEnd_1235185 := by
    simpa [prefixWord, tailWord_1235185, baseEnd_1235185] using wordTrace_append hprefix tailTrace_1235185
  have hstable : (prefixWord ++ tailWord_1235185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235185).length < 2 ^ (prefixWord ++ tailWord_1235185).sum := by decide
  have hdescent : baseEnd_1235185 < baseStart_1235185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235281 : List Nat := [1, 2, 2, 1, 4, 4, 1, 3, 3]
def baseStart_1235281 : Nat := 118140960795 + 1235281 * 2 ^ 59
def prefixEnd_1235281 : Nat := 4983230072969 + 3 ^ 40 * 1235281 * 2
def baseEnd_1235281 : Nat := 281907953940749640491801

theorem tailTrace_1235281 : CollatzResearch.WordTrace tailWord_1235281 prefixEnd_1235281 281907953940749640491801 := by
  unfold tailWord_1235281
  simp only [CollatzResearch.WordTrace]
  refine ⟨45054399437795381043793697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30036266291863587362529131 45054399437795381043793697)
  ·
    refine ⟨33790799578346535782845273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45054399437795381043793697 33790799578346535782845273)
    ·
      refine ⟨25343099683759901837133955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33790799578346535782845273 25343099683759901837133955)
      ·
        refine ⟨38014649525639852755700933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25343099683759901837133955 38014649525639852755700933)
        ·
          refine ⟨7127746786057472391693925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38014649525639852755700933 7127746786057472391693925)
          ·
            refine ⟨1336452522385776073442611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7127746786057472391693925 1336452522385776073442611)
            ·
              refine ⟨2004678783578664110163917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1336452522385776073442611 2004678783578664110163917)
              ·
                refine ⟨751754543841999041311469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2004678783578664110163917 751754543841999041311469)
                ·
                  refine ⟨281907953940749640491801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 751754543841999041311469 281907953940749640491801)
                  ·
                    rfl

theorem cell21_1235281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 3].length) (baseStart_1235281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235281 prefixEnd_1235281 := by exact prefixLift 1235281
  have htrace : WordTrace (prefixWord ++ tailWord_1235281) baseStart_1235281 baseEnd_1235281 := by
    simpa [prefixWord, tailWord_1235281, baseEnd_1235281] using wordTrace_append hprefix tailTrace_1235281
  have hstable : (prefixWord ++ tailWord_1235281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235281).length < 2 ^ (prefixWord ++ tailWord_1235281).sum := by decide
  have hdescent : baseEnd_1235281 < baseStart_1235281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235298 : List Nat := [3, 3, 2, 1, 1, 3, 3, 2, 3]
def baseStart_1235298 : Nat := 118140960795 + 1235298 * 2 ^ 59
def prefixEnd_1235298 : Nat := 4983230072969 + 3 ^ 40 * 1235298 * 2
def baseEnd_1235298 : Nat := 281911833572361388708433

theorem tailTrace_1235298 : CollatzResearch.WordTrace tailWord_1235298 prefixEnd_1235298 281911833572361388708433 := by
  unfold tailWord_1235298
  simp only [CollatzResearch.WordTrace]
  refine ⟨11263754869683448236790637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30036679652489195298108365 11263754869683448236790637)
  ·
    refine ⟨4223908076131293088796489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11263754869683448236790637 4223908076131293088796489)
    ·
      refine ⟨3167931057098469816597367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4223908076131293088796489 3167931057098469816597367)
      ·
        refine ⟨4751896585647704724896051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3167931057098469816597367 4751896585647704724896051)
        ·
          refine ⟨7127844878471557087344077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4751896585647704724896051 7127844878471557087344077)
          ·
            refine ⟨2672941829426833907754029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7127844878471557087344077 2672941829426833907754029)
            ·
              refine ⟨1002353186035062715407761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2672941829426833907754029 1002353186035062715407761)
              ·
                refine ⟨751764889526297036555821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1002353186035062715407761 751764889526297036555821)
                ·
                  refine ⟨281911833572361388708433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 751764889526297036555821 281911833572361388708433)
                  ·
                    rfl

theorem cell21_1235298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_1235298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235298 prefixEnd_1235298 := by exact prefixLift 1235298
  have htrace : WordTrace (prefixWord ++ tailWord_1235298) baseStart_1235298 baseEnd_1235298 := by
    simpa [prefixWord, tailWord_1235298, baseEnd_1235298] using wordTrace_append hprefix tailTrace_1235298
  have hstable : (prefixWord ++ tailWord_1235298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235298).length < 2 ^ (prefixWord ++ tailWord_1235298).sum := by decide
  have hdescent : baseEnd_1235298 < baseStart_1235298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235354 : List Nat := [3, 1, 1, 4, 1, 2, 1, 4, 4]
def baseStart_1235354 : Nat := 118140960795 + 1235354 * 2 ^ 59
def prefixEnd_1235354 : Nat := 4983230072969 + 3 ^ 40 * 1235354 * 2
def baseEnd_1235354 : Nat := 281924613535317735774985

theorem tailTrace_1235354 : CollatzResearch.WordTrace tailWord_1235354 prefixEnd_1235354 281924613535317735774985 := by
  unfold tailWord_1235354
  simp only [CollatzResearch.WordTrace]
  refine ⟨11264265491632728627800279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30038041311020609674134077 11264265491632728627800279)
  ·
    refine ⟨16896398237449092941700419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11264265491632728627800279 16896398237449092941700419)
    ·
      refine ⟨25344597356173639412550629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16896398237449092941700419 25344597356173639412550629)
      ·
        refine ⟨4752112004282557389853243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25344597356173639412550629 4752112004282557389853243)
        ·
          refine ⟨7128168006423836084779865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4752112004282557389853243 7128168006423836084779865)
          ·
            refine ⟨5346126004817877063584899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7128168006423836084779865 5346126004817877063584899)
            ·
              refine ⟨8019189007226815595377349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5346126004817877063584899 8019189007226815595377349)
              ·
                refine ⟨1503597938855027924133253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8019189007226815595377349 1503597938855027924133253)
                ·
                  refine ⟨281924613535317735774985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1503597938855027924133253 281924613535317735774985)
                  ·
                    rfl

theorem cell21_1235354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_1235354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235354 prefixEnd_1235354 := by exact prefixLift 1235354
  have htrace : WordTrace (prefixWord ++ tailWord_1235354) baseStart_1235354 baseEnd_1235354 := by
    simpa [prefixWord, tailWord_1235354, baseEnd_1235354] using wordTrace_append hprefix tailTrace_1235354
  have hstable : (prefixWord ++ tailWord_1235354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235354).length < 2 ^ (prefixWord ++ tailWord_1235354).sum := by decide
  have hdescent : baseEnd_1235354 < baseStart_1235354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235357 : List Nat := [1, 4, 2, 1, 4, 1, 1, 4, 3]
def baseStart_1235357 : Nat := 118140960795 + 1235357 * 2 ^ 59
def prefixEnd_1235357 : Nat := 4983230072969 + 3 ^ 40 * 1235357 * 2
def baseEnd_1235357 : Nat := 281925298176190397224979

theorem tailTrace_1235357 : CollatzResearch.WordTrace tailWord_1235357 prefixEnd_1235357 281925298176190397224979 := by
  unfold tailWord_1235357
  simp only [CollatzResearch.WordTrace]
  refine ⟨45057171385520046023560325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30038114257013364015706883 45057171385520046023560325)
  ·
    refine ⟨8448219634785008629417561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45057171385520046023560325 8448219634785008629417561)
    ·
      refine ⟨6336164726088756472063171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8448219634785008629417561 6336164726088756472063171)
      ·
        refine ⟨9504247089133134708094757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6336164726088756472063171 9504247089133134708094757)
        ·
          refine ⟨1782046329212462757767767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9504247089133134708094757 1782046329212462757767767)
          ·
            refine ⟨2673069493818694136651651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1782046329212462757767767 2673069493818694136651651)
            ·
              refine ⟨4009604240728041204977477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2673069493818694136651651 4009604240728041204977477)
              ·
                refine ⟨751800795136507725933277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4009604240728041204977477 751800795136507725933277)
                ·
                  refine ⟨281925298176190397224979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 751800795136507725933277 281925298176190397224979)
                  ·
                    rfl

theorem cell21_1235357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_1235357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235357 prefixEnd_1235357 := by exact prefixLift 1235357
  have htrace : WordTrace (prefixWord ++ tailWord_1235357) baseStart_1235357 baseEnd_1235357 := by
    simpa [prefixWord, tailWord_1235357, baseEnd_1235357] using wordTrace_append hprefix tailTrace_1235357
  have hstable : (prefixWord ++ tailWord_1235357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235357).length < 2 ^ (prefixWord ++ tailWord_1235357).sum := by decide
  have hdescent : baseEnd_1235357 < baseStart_1235357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235385 : List Nat := [1, 2, 1, 4, 3, 2, 3, 5]
def baseStart_1235385 : Nat := 118140960795 + 1235385 * 2 ^ 59
def prefixEnd_1235385 : Nat := 4983230072969 + 3 ^ 40 * 1235385 * 2
def baseEnd_1235385 : Nat := 93977229385889523586085

theorem tailTrace_1235385 : CollatzResearch.WordTrace tailWord_1235385 prefixEnd_1235385 93977229385889523586085 := by
  unfold tailWord_1235385
  simp only [CollatzResearch.WordTrace]
  refine ⟨45058192629418606805579609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30038795086279071203719739 45058192629418606805579609)
  ·
    refine ⟨33793644472063955104184707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45058192629418606805579609 33793644472063955104184707)
    ·
      refine ⟨50690466708095932656277061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33793644472063955104184707 50690466708095932656277061)
      ·
        refine ⟨9504462507767987373051949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50690466708095932656277061 9504462507767987373051949)
        ·
          refine ⟨3564173440412995264894481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9504462507767987373051949 3564173440412995264894481)
          ·
            refine ⟨2673130080309746448670861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3564173440412995264894481 2673130080309746448670861)
            ·
              refine ⟨1002423780116154918251573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2673130080309746448670861 1002423780116154918251573)
              ·
                refine ⟨93977229385889523586085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1002423780116154918251573 93977229385889523586085)
                ·
                  rfl

theorem cell21_1235385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 5].length) (baseStart_1235385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235385 prefixEnd_1235385 := by exact prefixLift 1235385
  have htrace : WordTrace (prefixWord ++ tailWord_1235385) baseStart_1235385 baseEnd_1235385 := by
    simpa [prefixWord, tailWord_1235385, baseEnd_1235385] using wordTrace_append hprefix tailTrace_1235385
  have hstable : (prefixWord ++ tailWord_1235385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235385).length < 2 ^ (prefixWord ++ tailWord_1235385).sum := by decide
  have hdescent : baseEnd_1235385 < baseStart_1235385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235526 : List Nat := [6, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_1235526 : Nat := 118140960795 + 1235526 * 2 ^ 59
def prefixEnd_1235526 : Nat := 4983230072969 + 3 ^ 40 * 1235526 * 2
def baseEnd_1235526 : Nat := 281963866278683658907967

theorem tailTrace_1235526 : CollatzResearch.WordTrace tailWord_1235526 prefixEnd_1235526 281963866278683658907967 := by
  unfold tailWord_1235526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1408229228809618371451951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30042223547938525257641621 1408229228809618371451951)
  ·
    refine ⟨2112343843214427557177927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1408229228809618371451951 2112343843214427557177927)
    ·
      refine ⟨3168515764821641335766891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2112343843214427557177927 3168515764821641335766891)
      ·
        refine ⟨4752773647232462003650337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3168515764821641335766891 4752773647232462003650337)
        ·
          refine ⟨3564580235424346502737753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4752773647232462003650337 3564580235424346502737753)
          ·
            refine ⟨2673435176568259877053315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3564580235424346502737753 2673435176568259877053315)
            ·
              refine ⟨4010152764852389815579973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2673435176568259877053315 4010152764852389815579973)
              ·
                refine ⟨751903643409823090421245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4010152764852389815579973 751903643409823090421245)
                ·
                  refine ⟨281963866278683658907967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 751903643409823090421245 281963866278683658907967)
                  ·
                    rfl

theorem cell21_1235526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_1235526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235526 prefixEnd_1235526 := by exact prefixLift 1235526
  have htrace : WordTrace (prefixWord ++ tailWord_1235526) baseStart_1235526 baseEnd_1235526 := by
    simpa [prefixWord, tailWord_1235526, baseEnd_1235526] using wordTrace_append hprefix tailTrace_1235526
  have hstable : (prefixWord ++ tailWord_1235526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235526).length < 2 ^ (prefixWord ++ tailWord_1235526).sum := by decide
  have hdescent : baseEnd_1235526 < baseStart_1235526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235641 : List Nat := [1, 2, 1, 4, 1, 1, 1, 6, 4]
def baseStart_1235641 : Nat := 118140960795 + 1235641 * 2 ^ 59
def prefixEnd_1235641 : Nat := 4983230072969 + 3 ^ 40 * 1235641 * 2
def baseEnd_1235641 : Nat := 281990110845469014491065

theorem tailTrace_1235641 : CollatzResearch.WordTrace tailWord_1235641 prefixEnd_1235641 281990110845469014491065 := by
  unfold tailWord_1235641
  simp only [CollatzResearch.WordTrace]
  refine ⟨45067529716491162526898777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30045019810994108351265851 45067529716491162526898777)
  ·
    refine ⟨33800647287368371895174083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45067529716491162526898777 33800647287368371895174083)
    ·
      refine ⟨50700970931052557842761125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33800647287368371895174083 50700970931052557842761125)
      ·
        refine ⟨9506432049572354595517711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50700970931052557842761125 9506432049572354595517711)
        ·
          refine ⟨14259648074358531893276567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9506432049572354595517711 14259648074358531893276567)
          ·
            refine ⟨21389472111537797839914851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14259648074358531893276567 21389472111537797839914851)
            ·
              refine ⟨32084208167306696759872277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21389472111537797839914851 32084208167306696759872277)
              ·
                refine ⟨1503947257842501410619013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32084208167306696759872277 1503947257842501410619013)
                ·
                  refine ⟨281990110845469014491065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1503947257842501410619013 281990110845469014491065)
                  ·
                    rfl

theorem cell21_1235641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_1235641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235641 prefixEnd_1235641 := by exact prefixLift 1235641
  have htrace : WordTrace (prefixWord ++ tailWord_1235641) baseStart_1235641 baseEnd_1235641 := by
    simpa [prefixWord, tailWord_1235641, baseEnd_1235641] using wordTrace_append hprefix tailTrace_1235641
  have hstable : (prefixWord ++ tailWord_1235641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235641).length < 2 ^ (prefixWord ++ tailWord_1235641).sum := by decide
  have hdescent : baseEnd_1235641 < baseStart_1235641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235658 : List Nat := [3, 1, 2, 1, 4, 2, 1, 3, 4]
def baseStart_1235658 : Nat := 118140960795 + 1235658 * 2 ^ 59
def prefixEnd_1235658 : Nat := 4983230072969 + 3 ^ 40 * 1235658 * 2
def baseEnd_1235658 : Nat := 281993990477080762707697

theorem tailTrace_1235658 : CollatzResearch.WordTrace tailWord_1235658 prefixEnd_1235658 281993990477080762707697 := by
  unfold tailWord_1235658
  simp only [CollatzResearch.WordTrace]
  refine ⟨11267037439357393607566907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30045433171619716286845085 11267037439357393607566907)
  ·
    refine ⟨16900556159036090411350361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11267037439357393607566907 16900556159036090411350361)
    ·
      refine ⟨12675417119277067808512771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16900556159036090411350361 12675417119277067808512771)
      ·
        refine ⟨19013125678915601712769157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12675417119277067808512771 19013125678915601712769157)
        ·
          refine ⟨3564961064796675321144217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19013125678915601712769157 3564961064796675321144217)
          ·
            refine ⟨2673720798597506490858163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3564961064796675321144217 2673720798597506490858163)
            ·
              refine ⟨4010581197896259736287245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2673720798597506490858163 4010581197896259736287245)
              ·
                refine ⟨1503967949211097401107717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4010581197896259736287245 1503967949211097401107717)
                ·
                  refine ⟨281993990477080762707697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1503967949211097401107717 281993990477080762707697)
                  ·
                    rfl

theorem cell21_1235658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_1235658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235658 prefixEnd_1235658 := by exact prefixLift 1235658
  have htrace : WordTrace (prefixWord ++ tailWord_1235658) baseStart_1235658 baseEnd_1235658 := by
    simpa [prefixWord, tailWord_1235658, baseEnd_1235658] using wordTrace_append hprefix tailTrace_1235658
  have hstable : (prefixWord ++ tailWord_1235658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235658).length < 2 ^ (prefixWord ++ tailWord_1235658).sum := by decide
  have hdescent : baseEnd_1235658 < baseStart_1235658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235748 : List Nat := [2, 3, 1, 3, 3, 1, 8]
def baseStart_1235748 : Nat := 118140960795 + 1235748 * 2 ^ 59
def prefixEnd_1235748 : Nat := 4983230072969 + 3 ^ 40 * 1235748 * 2
def baseEnd_1235748 : Nat := 31334947744806734023057

theorem tailTrace_1235748 : CollatzResearch.WordTrace tailWord_1235748 prefixEnd_1235748 31334947744806734023057 := by
  unfold tailWord_1235748
  simp only [CollatzResearch.WordTrace]
  refine ⟨22535716163551759900521949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30047621551402346534029265 22535716163551759900521949)
  ·
    refine ⟨8450893561331909962695731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22535716163551759900521949 8450893561331909962695731)
    ·
      refine ⟨12676340341997864944043597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8450893561331909962695731 12676340341997864944043597)
      ·
        refine ⟨4753627628249199354016349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12676340341997864944043597 4753627628249199354016349)
        ·
          refine ⟨1782610360593449757756131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4753627628249199354016349 1782610360593449757756131)
          ·
            refine ⟨2673915540890174636634197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1782610360593449757756131 2673915540890174636634197)
            ·
              refine ⟨31334947744806734023057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2673915540890174636634197 31334947744806734023057)
              ·
                rfl

theorem cell21_1235748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 8].length) (baseStart_1235748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235748 prefixEnd_1235748 := by exact prefixLift 1235748
  have htrace : WordTrace (prefixWord ++ tailWord_1235748) baseStart_1235748 baseEnd_1235748 := by
    simpa [prefixWord, tailWord_1235748, baseEnd_1235748] using wordTrace_append hprefix tailTrace_1235748
  have hstable : (prefixWord ++ tailWord_1235748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235748).length < 2 ^ (prefixWord ++ tailWord_1235748).sum := by decide
  have hdescent : baseEnd_1235748 < baseStart_1235748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235782 : List Nat := [6, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1235782 : Nat := 118140960795 + 1235782 * 2 ^ 59
def prefixEnd_1235782 : Nat := 4983230072969 + 3 ^ 40 * 1235782 * 2
def baseEnd_1235782 : Nat := 94007429655494700880259

theorem tailTrace_1235782 : CollatzResearch.WordTrace tailWord_1235782 prefixEnd_1235782 94007429655494700880259 := by
  unfold tailWord_1235782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1408521012780635737743175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30048448272653562405187733 1408521012780635737743175)
  ·
    refine ⟨2112781519170953606614763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1408521012780635737743175 2112781519170953606614763)
    ·
      refine ⟨3169172278756430409922145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2112781519170953606614763 3169172278756430409922145)
      ·
        refine ⟨2376879209067322807441609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3169172278756430409922145 2376879209067322807441609)
        ·
          refine ⟨1782659406800492105581207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2376879209067322807441609 1782659406800492105581207)
          ·
            refine ⟨2673989110200738158371811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1782659406800492105581207 2673989110200738158371811)
            ·
              refine ⟨4010983665301107237557717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2673989110200738158371811 4010983665301107237557717)
              ·
                refine ⟨94007429655494700880259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4010983665301107237557717 94007429655494700880259)
                ·
                  rfl

theorem cell21_1235782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1235782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235782 prefixEnd_1235782 := by exact prefixLift 1235782
  have htrace : WordTrace (prefixWord ++ tailWord_1235782) baseStart_1235782 baseEnd_1235782 := by
    simpa [prefixWord, tailWord_1235782, baseEnd_1235782] using wordTrace_append hprefix tailTrace_1235782
  have hstable : (prefixWord ++ tailWord_1235782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235782).length < 2 ^ (prefixWord ++ tailWord_1235782).sum := by decide
  have hdescent : baseEnd_1235782 < baseStart_1235782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235852 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 8]
def baseStart_1235852 : Nat := 118140960795 + 1235852 * 2 ^ 59
def prefixEnd_1235852 : Nat := 4983230072969 + 3 ^ 40 * 1235852 * 2
def baseEnd_1235852 : Nat := 282038263920179536473967

theorem tailTrace_1235852 : CollatzResearch.WordTrace tailWord_1235852 prefixEnd_1235852 282038263920179536473967 := by
  unfold tailWord_1235852
  simp only [CollatzResearch.WordTrace]
  refine ⟨22537612759363372781414905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30050150345817830375219873 22537612759363372781414905)
  ·
    refine ⟨16903209569522529586061179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22537612759363372781414905 16903209569522529586061179)
    ·
      refine ⟨25354814354283794379091769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16903209569522529586061179 25354814354283794379091769)
      ·
        refine ⟨19016110765712845784318827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25354814354283794379091769 19016110765712845784318827)
        ·
          refine ⟨28524166148569268676478241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19016110765712845784318827 28524166148569268676478241)
          ·
            refine ⟨21393124611426951507358681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28524166148569268676478241 21393124611426951507358681)
            ·
              refine ⟨16044843458570213630519011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21393124611426951507358681 16044843458570213630519011)
              ·
                refine ⟨24067265187855320445778517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16044843458570213630519011 24067265187855320445778517)
                ·
                  refine ⟨282038263920179536473967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24067265187855320445778517 282038263920179536473967)
                  ·
                    rfl

theorem cell21_1235852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_1235852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235852 prefixEnd_1235852 := by exact prefixLift 1235852
  have htrace : WordTrace (prefixWord ++ tailWord_1235852) baseStart_1235852 baseEnd_1235852 := by
    simpa [prefixWord, tailWord_1235852, baseEnd_1235852] using wordTrace_append hprefix tailTrace_1235852
  have hstable : (prefixWord ++ tailWord_1235852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235852).length < 2 ^ (prefixWord ++ tailWord_1235852).sum := by decide
  have hdescent : baseEnd_1235852 < baseStart_1235852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235872 : List Nat := [2, 1, 1, 4, 1, 1, 6, 2, 3]
def baseStart_1235872 : Nat := 118140960795 + 1235872 * 2 ^ 59
def prefixEnd_1235872 : Nat := 4983230072969 + 3 ^ 40 * 1235872 * 2
def baseEnd_1235872 : Nat := 282042828192663946140593

theorem tailTrace_1235872 : CollatzResearch.WordTrace tailWord_1235872 prefixEnd_1235872 282042828192663946140593 := by
  unfold tailWord_1235872
  simp only [CollatzResearch.WordTrace]
  refine ⟨22537977489327144489278935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30050636652436192652371913 22537977489327144489278935)
  ·
    refine ⟨33806966233990716733918403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22537977489327144489278935 33806966233990716733918403)
    ·
      refine ⟨50710449350986075100877605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33806966233990716733918403 50710449350986075100877605)
      ·
        refine ⟨9508209253309889081414551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50710449350986075100877605 9508209253309889081414551)
        ·
          refine ⟨14262313879964833622121827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9508209253309889081414551 14262313879964833622121827)
          ·
            refine ⟨21393470819947250433182741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14262313879964833622121827 21393470819947250433182741)
            ·
              refine ⟨1002818944685027364055441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21393470819947250433182741 1002818944685027364055441)
              ·
                refine ⟨752114208513770523041581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1002818944685027364055441 752114208513770523041581)
                ·
                  refine ⟨282042828192663946140593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 752114208513770523041581 282042828192663946140593)
                  ·
                    rfl

theorem cell21_1235872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 3].length) (baseStart_1235872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235872 prefixEnd_1235872 := by exact prefixLift 1235872
  have htrace : WordTrace (prefixWord ++ tailWord_1235872) baseStart_1235872 baseEnd_1235872 := by
    simpa [prefixWord, tailWord_1235872, baseEnd_1235872] using wordTrace_append hprefix tailTrace_1235872
  have hstable : (prefixWord ++ tailWord_1235872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235872).length < 2 ^ (prefixWord ++ tailWord_1235872).sum := by decide
  have hdescent : baseEnd_1235872 < baseStart_1235872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235996 : List Nat := [2, 2, 3, 1, 5, 1, 2, 1, 4]
def baseStart_1235996 : Nat := 118140960795 + 1235996 * 2 ^ 59
def prefixEnd_1235996 : Nat := 4983230072969 + 3 ^ 40 * 1235996 * 2
def baseEnd_1235996 : Nat := 282071126682067286073673

theorem tailTrace_1235996 : CollatzResearch.WordTrace tailWord_1235996 prefixEnd_1235996 282071126682067286073673 := by
  unfold tailWord_1235996
  simp only [CollatzResearch.WordTrace]
  refine ⟨22540238815102529078035921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30053651753470038770714561 22540238815102529078035921)
  ·
    refine ⟨16905179111326896808526941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22540238815102529078035921 16905179111326896808526941)
    ·
      refine ⟨6339442166747586303197603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16905179111326896808526941 6339442166747586303197603)
      ·
        refine ⟨9509163250121379454796405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6339442166747586303197603 9509163250121379454796405)
        ·
          refine ⟨891484054698879323887163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9509163250121379454796405 891484054698879323887163)
          ·
            refine ⟨1337226082048318985830745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 891484054698879323887163 1337226082048318985830745)
            ·
              refine ⟨1002919561536239239373059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1337226082048318985830745 1002919561536239239373059)
              ·
                refine ⟨1504379342304358859059589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002919561536239239373059 1504379342304358859059589)
                ·
                  refine ⟨282071126682067286073673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1504379342304358859059589 282071126682067286073673)
                  ·
                    rfl

theorem cell21_1235996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_1235996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1235996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1235996 prefixEnd_1235996 := by exact prefixLift 1235996
  have htrace : WordTrace (prefixWord ++ tailWord_1235996) baseStart_1235996 baseEnd_1235996 := by
    simpa [prefixWord, tailWord_1235996, baseEnd_1235996] using wordTrace_append hprefix tailTrace_1235996
  have hstable : (prefixWord ++ tailWord_1235996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235996).length < 2 ^ (prefixWord ++ tailWord_1235996).sum := by decide
  have hdescent : baseEnd_1235996 < baseStart_1235996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236080 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 6]
def baseStart_1236080 : Nat := 118140960795 + 1236080 * 2 ^ 59
def prefixEnd_1236080 : Nat := 4983230072969 + 3 ^ 40 * 1236080 * 2
def baseEnd_1236080 : Nat := 282090296626501806673501

theorem tailTrace_1236080 : CollatzResearch.WordTrace tailWord_1236080 prefixEnd_1236080 282090296626501806673501 := by
  unfold tailWord_1236080
  simp only [CollatzResearch.WordTrace]
  refine ⟨22541770680950370251064847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30055694241267160334753129 22541770680950370251064847)
  ·
    refine ⟨33812656021425555376597271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22541770680950370251064847 33812656021425555376597271)
    ·
      refine ⟨50718984032138333064895907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33812656021425555376597271 50718984032138333064895907)
      ·
        refine ⟨76078476048207499597343861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50718984032138333064895907 76078476048207499597343861)
        ·
          refine ⟨7132357129519453087250987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76078476048207499597343861 7132357129519453087250987)
          ·
            refine ⟨10698535694279179630876481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7132357129519453087250987 10698535694279179630876481)
            ·
              refine ⟨8023901770709384723157361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10698535694279179630876481 8023901770709384723157361)
              ·
                refine ⟨6017926328032038542368021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8023901770709384723157361 6017926328032038542368021)
                ·
                  refine ⟨282090296626501806673501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6017926328032038542368021 282090296626501806673501)
                  ·
                    rfl

theorem cell21_1236080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_1236080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236080 prefixEnd_1236080 := by exact prefixLift 1236080
  have htrace : WordTrace (prefixWord ++ tailWord_1236080) baseStart_1236080 baseEnd_1236080 := by
    simpa [prefixWord, tailWord_1236080, baseEnd_1236080] using wordTrace_append hprefix tailTrace_1236080
  have hstable : (prefixWord ++ tailWord_1236080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236080).length < 2 ^ (prefixWord ++ tailWord_1236080).sum := by decide
  have hdescent : baseEnd_1236080 < baseStart_1236080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236097 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 6]
def baseStart_1236097 : Nat := 118140960795 + 1236097 * 2 ^ 59
def prefixEnd_1236097 : Nat := 4983230072969 + 3 ^ 40 * 1236097 * 2
def baseEnd_1236097 : Nat := 282094176258113554890133

theorem tailTrace_1236097 : CollatzResearch.WordTrace tailWord_1236097 prefixEnd_1236097 282094176258113554890133 := by
  unfold tailWord_1236097
  simp only [CollatzResearch.WordTrace]
  refine ⟨45084161402839152405498545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30056107601892768270332363 45084161402839152405498545)
  ·
    refine ⟨33813121052129364304123909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45084161402839152405498545 33813121052129364304123909)
    ·
      refine ⟨6339960197274255807023233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33813121052129364304123909 6339960197274255807023233)
      ·
        refine ⟨4754970147955691855267425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6339960197274255807023233 4754970147955691855267425)
        ·
          refine ⟨3566227610966768891450569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4754970147955691855267425 3566227610966768891450569)
          ·
            refine ⟨2674670708225076668587927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3566227610966768891450569 2674670708225076668587927)
            ·
              refine ⟨4012006062337615002881891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2674670708225076668587927 4012006062337615002881891)
              ·
                refine ⟨6018009093506422504322837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4012006062337615002881891 6018009093506422504322837)
                ·
                  refine ⟨282094176258113554890133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6018009093506422504322837 282094176258113554890133)
                  ·
                    rfl

theorem cell21_1236097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_1236097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236097 prefixEnd_1236097 := by exact prefixLift 1236097
  have htrace : WordTrace (prefixWord ++ tailWord_1236097) baseStart_1236097 baseEnd_1236097 := by
    simpa [prefixWord, tailWord_1236097, baseEnd_1236097] using wordTrace_append hprefix tailTrace_1236097
  have hstable : (prefixWord ++ tailWord_1236097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236097).length < 2 ^ (prefixWord ++ tailWord_1236097).sum := by decide
  have hdescent : baseEnd_1236097 < baseStart_1236097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236162 : List Nat := [3, 5, 1, 1, 2, 1, 2, 6]
def baseStart_1236162 : Nat := 118140960795 + 1236162 * 2 ^ 59
def prefixEnd_1236162 : Nat := 4983230072969 + 3 ^ 40 * 1236162 * 2
def baseEnd_1236162 : Nat := 94036336714562628768889

theorem tailTrace_1236162 : CollatzResearch.WordTrace tailWord_1236162 prefixEnd_1236162 94036336714562628768889 := by
  unfold tailWord_1236162
  simp only [CollatzResearch.WordTrace]
  refine ⟨11271633036900917126653685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30057688098402445671076493 11271633036900917126653685)
  ·
    refine ⟨1056715597209460980623783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11271633036900917126653685 1056715597209460980623783)
    ·
      refine ⟨1585073395814191470935675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1056715597209460980623783 1585073395814191470935675)
      ·
        refine ⟨2377610093721287206403513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1585073395814191470935675 2377610093721287206403513)
        ·
          refine ⟨1783207570290965404802635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2377610093721287206403513 1783207570290965404802635)
          ·
            refine ⟨2674811355436448107203953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1783207570290965404802635 2674811355436448107203953)
            ·
              refine ⟨2006108516577336080402965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2674811355436448107203953 2006108516577336080402965)
              ·
                refine ⟨94036336714562628768889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2006108516577336080402965 94036336714562628768889)
                ·
                  rfl

theorem cell21_1236162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_1236162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236162 prefixEnd_1236162 := by exact prefixLift 1236162
  have htrace : WordTrace (prefixWord ++ tailWord_1236162) baseStart_1236162 baseEnd_1236162 := by
    simpa [prefixWord, tailWord_1236162, baseEnd_1236162] using wordTrace_append hprefix tailTrace_1236162
  have hstable : (prefixWord ++ tailWord_1236162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236162).length < 2 ^ (prefixWord ++ tailWord_1236162).sum := by decide
  have hdescent : baseEnd_1236162 < baseStart_1236162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236210 : List Nat := [3, 2, 1, 3, 4, 1, 2, 2, 3]
def baseStart_1236210 : Nat := 118140960795 + 1236210 * 2 ^ 59
def prefixEnd_1236210 : Nat := 4983230072969 + 3 ^ 40 * 1236210 * 2
def baseEnd_1236210 : Nat := 282119964397650469506569

theorem tailTrace_1236210 : CollatzResearch.WordTrace tailWord_1236210 prefixEnd_1236210 282119964397650469506569 := by
  unfold tailWord_1236210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11272070712857443176090521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30058855234286515136241389 11272070712857443176090521)
  ·
    refine ⟨8454053034643082382067891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11272070712857443176090521 8454053034643082382067891)
    ·
      refine ⟨12681079551964623573101837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8454053034643082382067891 12681079551964623573101837)
      ·
        refine ⟨4755404831986733839913189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12681079551964623573101837 4755404831986733839913189)
        ·
          refine ⟨891638405997512594983723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4755404831986733839913189 891638405997512594983723)
          ·
            refine ⟨1337457608996268892475585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 891638405997512594983723 1337457608996268892475585)
            ·
              refine ⟨1003093206747201669356689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1337457608996268892475585 1003093206747201669356689)
              ·
                refine ⟨752319905060401252017517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1003093206747201669356689 752319905060401252017517)
                ·
                  refine ⟨282119964397650469506569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 752319905060401252017517 282119964397650469506569)
                  ·
                    rfl

theorem cell21_1236210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_1236210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236210 prefixEnd_1236210 := by exact prefixLift 1236210
  have htrace : WordTrace (prefixWord ++ tailWord_1236210) baseStart_1236210 baseEnd_1236210 := by
    simpa [prefixWord, tailWord_1236210, baseEnd_1236210] using wordTrace_append hprefix tailTrace_1236210
  have hstable : (prefixWord ++ tailWord_1236210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236210).length < 2 ^ (prefixWord ++ tailWord_1236210).sum := by decide
  have hdescent : baseEnd_1236210 < baseStart_1236210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236266 : List Nat := [3, 1, 4, 2, 1, 1, 3, 2, 4]
def baseStart_1236266 : Nat := 118140960795 + 1236266 * 2 ^ 59
def prefixEnd_1236266 : Nat := 4983230072969 + 3 ^ 40 * 1236266 * 2
def baseEnd_1236266 : Nat := 282132744360606816573121

theorem tailTrace_1236266 : CollatzResearch.WordTrace tailWord_1236266 prefixEnd_1236266 282132744360606816573121 := by
  unfold tailWord_1236266
  simp only [CollatzResearch.WordTrace]
  refine ⟨11272581334806723567100163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30060216892817929512267101 11272581334806723567100163)
  ·
    refine ⟨16908872002210085350650245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11272581334806723567100163 16908872002210085350650245)
    ·
      refine ⟨3170413500414391003246921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16908872002210085350650245 3170413500414391003246921)
      ·
        refine ⟨2377810125310793252435191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3170413500414391003246921 2377810125310793252435191)
        ·
          refine ⟨3566715187966189878652787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2377810125310793252435191 3566715187966189878652787)
          ·
            refine ⟨5350072781949284817979181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3566715187966189878652787 5350072781949284817979181)
            ·
              refine ⟨2006277293230981806742193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5350072781949284817979181 2006277293230981806742193)
              ·
                refine ⟨1504707969923236355056645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2006277293230981806742193 1504707969923236355056645)
                ·
                  refine ⟨282132744360606816573121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1504707969923236355056645 282132744360606816573121)
                  ·
                    rfl

theorem cell21_1236266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_1236266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236266 prefixEnd_1236266 := by exact prefixLift 1236266
  have htrace : WordTrace (prefixWord ++ tailWord_1236266) baseStart_1236266 baseEnd_1236266 := by
    simpa [prefixWord, tailWord_1236266, baseEnd_1236266] using wordTrace_append hprefix tailTrace_1236266
  have hstable : (prefixWord ++ tailWord_1236266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236266).length < 2 ^ (prefixWord ++ tailWord_1236266).sum := by decide
  have hdescent : baseEnd_1236266 < baseStart_1236266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236308 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 8]
def baseStart_1236308 : Nat := 118140960795 + 1236308 * 2 ^ 59
def prefixEnd_1236308 : Nat := 4983230072969 + 3 ^ 40 * 1236308 * 2
def baseEnd_1236308 : Nat := 282142329332824076873035

theorem tailTrace_1236308 : CollatzResearch.WordTrace tailWord_1236308 prefixEnd_1236308 282142329332824076873035 := by
  unfold tailWord_1236308
  simp only [CollatzResearch.WordTrace]
  refine ⟨22545928602537367720714789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30061238136716490294286385 22545928602537367720714789)
  ·
    refine ⟨4227361612975756447634023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22545928602537367720714789 4227361612975756447634023)
    ·
      refine ⟨6341042419463634671451035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4227361612975756447634023 6341042419463634671451035)
      ·
        refine ⟨9511563629195452007176553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6341042419463634671451035 9511563629195452007176553)
        ·
          refine ⟨7133672721896589005382415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9511563629195452007176553 7133672721896589005382415)
          ·
            refine ⟨10700509082844883508073623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7133672721896589005382415 10700509082844883508073623)
            ·
              refine ⟨16050763624267325262110435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10700509082844883508073623 16050763624267325262110435)
              ·
                refine ⟨24076145436400987893165653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16050763624267325262110435 24076145436400987893165653)
                ·
                  refine ⟨282142329332824076873035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24076145436400987893165653 282142329332824076873035)
                  ·
                    rfl

theorem cell21_1236308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_1236308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236308 prefixEnd_1236308 := by exact prefixLift 1236308
  have htrace : WordTrace (prefixWord ++ tailWord_1236308) baseStart_1236308 baseEnd_1236308 := by
    simpa [prefixWord, tailWord_1236308, baseEnd_1236308] using wordTrace_append hprefix tailTrace_1236308
  have hstable : (prefixWord ++ tailWord_1236308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236308).length < 2 ^ (prefixWord ++ tailWord_1236308).sum := by decide
  have hdescent : baseEnd_1236308 < baseStart_1236308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236311 : List Nat := [1, 1, 3, 2, 3, 2, 3, 3, 3]
def baseStart_1236311 : Nat := 118140960795 + 1236311 * 2 ^ 59
def prefixEnd_1236311 : Nat := 4983230072969 + 3 ^ 40 * 1236311 * 2
def baseEnd_1236311 : Nat := 282143013973696738323029

theorem tailTrace_1236311 : CollatzResearch.WordTrace tailWord_1236311 prefixEnd_1236311 282143013973696738323029 := by
  unfold tailWord_1236311
  simp only [CollatzResearch.WordTrace]
  refine ⟨45091966624063866953788787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30061311082709244635859191 45091966624063866953788787)
  ·
    refine ⟨67637949936095800430683181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45091966624063866953788787 67637949936095800430683181)
    ·
      refine ⟨25364231226035925161506193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67637949936095800430683181 25364231226035925161506193)
      ·
        refine ⟨19023173419526943871129645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25364231226035925161506193 19023173419526943871129645)
        ·
          refine ⟨7133690032322603951673617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19023173419526943871129645 7133690032322603951673617)
          ·
            refine ⟨5350267524241952963755213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7133690032322603951673617 5350267524241952963755213)
            ·
              refine ⟨2006350321590732361408205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5350267524241952963755213 2006350321590732361408205)
              ·
                refine ⟨752381370596524635528077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2006350321590732361408205 752381370596524635528077)
                ·
                  refine ⟨282143013973696738323029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 752381370596524635528077 282143013973696738323029)
                  ·
                    rfl

theorem cell21_1236311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 3].length) (baseStart_1236311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236311 prefixEnd_1236311 := by exact prefixLift 1236311
  have htrace : WordTrace (prefixWord ++ tailWord_1236311) baseStart_1236311 baseEnd_1236311 := by
    simpa [prefixWord, tailWord_1236311, baseEnd_1236311] using wordTrace_append hprefix tailTrace_1236311
  have hstable : (prefixWord ++ tailWord_1236311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236311).length < 2 ^ (prefixWord ++ tailWord_1236311).sum := by decide
  have hdescent : baseEnd_1236311 < baseStart_1236311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236328 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 5]
def baseStart_1236328 : Nat := 118140960795 + 1236328 * 2 ^ 59
def prefixEnd_1236328 : Nat := 4983230072969 + 3 ^ 40 * 1236328 * 2
def baseEnd_1236328 : Nat := 282146893605308486539661

theorem tailTrace_1236328 : CollatzResearch.WordTrace tailWord_1236328 prefixEnd_1236328 282146893605308486539661 := by
  unfold tailWord_1236328
  simp only [CollatzResearch.WordTrace]
  refine ⟨22546293332501139428578819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30061724443334852571438425 22546293332501139428578819)
  ·
    refine ⟨33819439998751709142868229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22546293332501139428578819 33819439998751709142868229)
    ·
      refine ⟨6341144999765945464287793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33819439998751709142868229 6341144999765945464287793)
      ·
        refine ⟨4755858749824459098215845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6341144999765945464287793 4755858749824459098215845)
        ·
          refine ⟨891723515592086080915471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4755858749824459098215845 891723515592086080915471)
          ·
            refine ⟨1337585273388129121373207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 891723515592086080915471 1337585273388129121373207)
            ·
              refine ⟨2006377910082193682059811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1337585273388129121373207 2006377910082193682059811)
              ·
                refine ⟨3009566865123290523089717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2006377910082193682059811 3009566865123290523089717)
                ·
                  refine ⟨282146893605308486539661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3009566865123290523089717 282146893605308486539661)
                  ·
                    rfl

theorem cell21_1236328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 5].length) (baseStart_1236328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236328 prefixEnd_1236328 := by exact prefixLift 1236328
  have htrace : WordTrace (prefixWord ++ tailWord_1236328) baseStart_1236328 baseEnd_1236328 := by
    simpa [prefixWord, tailWord_1236328, baseEnd_1236328] using wordTrace_append hprefix tailTrace_1236328
  have hstable : (prefixWord ++ tailWord_1236328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236328).length < 2 ^ (prefixWord ++ tailWord_1236328).sum := by decide
  have hdescent : baseEnd_1236328 < baseStart_1236328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236474 : List Nat := [3, 1, 1, 1, 1, 2, 5, 7]
def baseStart_1236474 : Nat := 118140960795 + 1236474 * 2 ^ 59
def prefixEnd_1236474 : Nat := 4983230072969 + 3 ^ 40 * 1236474 * 2
def baseEnd_1236474 : Nat := 94060070931481559035343

theorem tailTrace_1236474 : CollatzResearch.WordTrace tailWord_1236474 prefixEnd_1236474 94060070931481559035343 := by
  unfold tailWord_1236474
  simp only [CollatzResearch.WordTrace]
  refine ⟨11274477930618336447993119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30065274481648897194648317 11274477930618336447993119)
  ·
    refine ⟨16911716895927504671989679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11274477930618336447993119 16911716895927504671989679)
    ·
      refine ⟨25367575343891257007984519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16911716895927504671989679 25367575343891257007984519)
      ·
        refine ⟨38051363015836885511976779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25367575343891257007984519 38051363015836885511976779)
        ·
          refine ⟨57077044523755328267965169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38051363015836885511976779 57077044523755328267965169)
          ·
            refine ⟨42807783392816496200973877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57077044523755328267965169 42807783392816496200973877)
            ·
              refine ⟨4013229693076546518841301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42807783392816496200973877 4013229693076546518841301)
              ·
                refine ⟨94060070931481559035343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4013229693076546518841301 94060070931481559035343)
                ·
                  rfl

theorem cell21_1236474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_1236474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236474 prefixEnd_1236474 := by exact prefixLift 1236474
  have htrace : WordTrace (prefixWord ++ tailWord_1236474) baseStart_1236474 baseEnd_1236474 := by
    simpa [prefixWord, tailWord_1236474, baseEnd_1236474] using wordTrace_append hprefix tailTrace_1236474
  have hstable : (prefixWord ++ tailWord_1236474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236474).length < 2 ^ (prefixWord ++ tailWord_1236474).sum := by decide
  have hdescent : baseEnd_1236474 < baseStart_1236474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236491 : List Nat := [1, 1, 1, 1, 8, 2, 7]
def baseStart_1236491 : Nat := 118140960795 + 1236491 * 2 ^ 59
def prefixEnd_1236491 : Nat := 4983230072969 + 3 ^ 40 * 1236491 * 2
def baseEnd_1236491 : Nat := 31353788047339602813629

theorem tailTrace_1236491 : CollatzResearch.WordTrace tailWord_1236491 prefixEnd_1236491 31353788047339602813629 := by
  unfold tailWord_1236491
  simp only [CollatzResearch.WordTrace]
  refine ⟨45098531763411757695341327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30065687842274505130227551 45098531763411757695341327)
  ·
    refine ⟨67647797645117636543011991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45098531763411757695341327 67647797645117636543011991)
    ·
      refine ⟨101471696467676454814517987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67647797645117636543011991 101471696467676454814517987)
      ·
        refine ⟨152207544701514682221776981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101471696467676454814517987 152207544701514682221776981)
        ·
          refine ⟨1783682164470875182286449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 152207544701514682221776981 1783682164470875182286449)
          ·
            refine ⟨1337761623353156386714837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1783682164470875182286449 1337761623353156386714837)
            ·
              refine ⟨31353788047339602813629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1337761623353156386714837 31353788047339602813629)
              ·
                rfl

theorem cell21_1236491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 7].length) (baseStart_1236491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236491 prefixEnd_1236491 := by exact prefixLift 1236491
  have htrace : WordTrace (prefixWord ++ tailWord_1236491) baseStart_1236491 baseEnd_1236491 := by
    simpa [prefixWord, tailWord_1236491, baseEnd_1236491] using wordTrace_append hprefix tailTrace_1236491
  have hstable : (prefixWord ++ tailWord_1236491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236491).length < 2 ^ (prefixWord ++ tailWord_1236491).sum := by decide
  have hdescent : baseEnd_1236491 < baseStart_1236491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236556 : List Nat := [2, 2, 1, 3, 1, 5, 2, 2, 3]
def baseStart_1236556 : Nat := 118140960795 + 1236556 * 2 ^ 59
def prefixEnd_1236556 : Nat := 4983230072969 + 3 ^ 40 * 1236556 * 2
def baseEnd_1236556 : Nat := 282198926311630756739195

theorem tailTrace_1236556 : CollatzResearch.WordTrace tailWord_1236556 prefixEnd_1236556 282198926311630756739195 := by
  unfold tailWord_1236556
  simp only [CollatzResearch.WordTrace]
  refine ⟨22550451254088136898228761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30067268338784182530971681 22550451254088136898228761)
  ·
    refine ⟨16912838440566102673671571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22550451254088136898228761 16912838440566102673671571)
    ·
      refine ⟨25369257660849154010507357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16912838440566102673671571 25369257660849154010507357)
      ·
        refine ⟨9513471622818432753940259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25369257660849154010507357 9513471622818432753940259)
        ·
          refine ⟨14270207434227649130910389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9513471622818432753940259 14270207434227649130910389)
          ·
            refine ⟨1337831946958842106022849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14270207434227649130910389 1337831946958842106022849)
            ·
              refine ⟨1003373960219131579517137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1337831946958842106022849 1003373960219131579517137)
              ·
                refine ⟨752530470164348684637853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1003373960219131579517137 752530470164348684637853)
                ·
                  refine ⟨282198926311630756739195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 752530470164348684637853 282198926311630756739195)
                  ·
                    rfl

theorem cell21_1236556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_1236556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236556 prefixEnd_1236556 := by exact prefixLift 1236556
  have htrace : WordTrace (prefixWord ++ tailWord_1236556) baseStart_1236556 baseEnd_1236556 := by
    simpa [prefixWord, tailWord_1236556, baseEnd_1236556] using wordTrace_append hprefix tailTrace_1236556
  have hstable : (prefixWord ++ tailWord_1236556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236556).length < 2 ^ (prefixWord ++ tailWord_1236556).sum := by decide
  have hdescent : baseEnd_1236556 < baseStart_1236556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236567 : List Nat := [1, 1, 3, 2, 2, 5, 1, 6]
def baseStart_1236567 : Nat := 118140960795 + 1236567 * 2 ^ 59
def prefixEnd_1236567 : Nat := 4983230072969 + 3 ^ 40 * 1236567 * 2
def baseEnd_1236567 : Nat := 94067145553832394018613

theorem tailTrace_1236567 : CollatzResearch.WordTrace tailWord_1236567 prefixEnd_1236567 94067145553832394018613 := by
  unfold tailWord_1236567
  simp only [CollatzResearch.WordTrace]
  refine ⟨45101303711136422675107955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30067535807424281783405303 45101303711136422675107955)
  ·
    refine ⟨67651955566704634012661933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45101303711136422675107955 67651955566704634012661933)
    ·
      refine ⟨25369483337514237754748225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67651955566704634012661933 25369483337514237754748225)
      ·
        refine ⟨19027112503135678316061169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25369483337514237754748225 19027112503135678316061169)
        ·
          refine ⟨14270334377351758737045877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19027112503135678316061169 14270334377351758737045877)
          ·
            refine ⟨1337843847876727381598051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14270334377351758737045877 1337843847876727381598051)
            ·
              refine ⟨2006765771815091072397077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1337843847876727381598051 2006765771815091072397077)
              ·
                refine ⟨94067145553832394018613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2006765771815091072397077 94067145553832394018613)
                ·
                  rfl

theorem cell21_1236567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 6].length) (baseStart_1236567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236567 prefixEnd_1236567 := by exact prefixLift 1236567
  have htrace : WordTrace (prefixWord ++ tailWord_1236567) baseStart_1236567 baseEnd_1236567 := by
    simpa [prefixWord, tailWord_1236567, baseEnd_1236567] using wordTrace_append hprefix tailTrace_1236567
  have hstable : (prefixWord ++ tailWord_1236567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236567).length < 2 ^ (prefixWord ++ tailWord_1236567).sum := by decide
  have hdescent : baseEnd_1236567 < baseStart_1236567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236581 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 7]
def baseStart_1236581 : Nat := 118140960795 + 1236581 * 2 ^ 59
def prefixEnd_1236581 : Nat := 4983230072969 + 3 ^ 40 * 1236581 * 2
def baseEnd_1236581 : Nat := 282204631652236268822477

theorem tailTrace_1236581 : CollatzResearch.WordTrace tailWord_1236581 prefixEnd_1236581 282204631652236268822477 := by
  unfold tailWord_1236581
  simp only [CollatzResearch.WordTrace]
  refine ⟨45101814333085703066117597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30067876222057135377411731 45101814333085703066117597)
  ·
    refine ⟨16913180374907138649794099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45101814333085703066117597 16913180374907138649794099)
    ·
      refine ⟨25369770562360707974691149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16913180374907138649794099 25369770562360707974691149)
      ·
        refine ⟨9513663960885265490509181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25369770562360707974691149 9513663960885265490509181)
        ·
          refine ⟨3567623985331974558940943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9513663960885265490509181 3567623985331974558940943)
          ·
            refine ⟨5351435977997961838411415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3567623985331974558940943 5351435977997961838411415)
            ·
              refine ⟨8027153966996942757617123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5351435977997961838411415 8027153966996942757617123)
              ·
                refine ⟨12040730950495414136425685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8027153966996942757617123 12040730950495414136425685)
                ·
                  refine ⟨282204631652236268822477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12040730950495414136425685 282204631652236268822477)
                  ·
                    rfl

theorem cell21_1236581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_1236581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236581 prefixEnd_1236581 := by exact prefixLift 1236581
  have htrace : WordTrace (prefixWord ++ tailWord_1236581) baseStart_1236581 baseEnd_1236581 := by
    simpa [prefixWord, tailWord_1236581, baseEnd_1236581] using wordTrace_append hprefix tailTrace_1236581
  have hstable : (prefixWord ++ tailWord_1236581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236581).length < 2 ^ (prefixWord ++ tailWord_1236581).sum := by decide
  have hdescent : baseEnd_1236581 < baseStart_1236581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236584 : List Nat := [2, 1, 4, 3, 1, 2, 3, 5]
def baseStart_1236584 : Nat := 118140960795 + 1236584 * 2 ^ 59
def prefixEnd_1236584 : Nat := 4983230072969 + 3 ^ 40 * 1236584 * 2
def baseEnd_1236584 : Nat := 94068438764369643424157

theorem tailTrace_1236584 : CollatzResearch.WordTrace tailWord_1236584 prefixEnd_1236584 94068438764369643424157 := by
  unfold tailWord_1236584
  simp only [CollatzResearch.WordTrace]
  refine ⟨22550961876037417289238403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30067949168049889718984537 22550961876037417289238403)
  ·
    refine ⟨33826442814056125933857605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22550961876037417289238403 33826442814056125933857605)
    ·
      refine ⟨6342458027635523612598301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33826442814056125933857605 6342458027635523612598301)
      ·
        refine ⟨2378421760363321354724363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6342458027635523612598301 2378421760363321354724363)
        ·
          refine ⟨3567632640544982032086545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2378421760363321354724363 3567632640544982032086545)
          ·
            refine ⟨2675724480408736524064909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3567632640544982032086545 2675724480408736524064909)
            ·
              refine ⟨1003396680153276196524341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2675724480408736524064909 1003396680153276196524341)
              ·
                refine ⟨94068438764369643424157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1003396680153276196524341 94068438764369643424157)
                ·
                  rfl

theorem cell21_1236584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 5].length) (baseStart_1236584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236584 prefixEnd_1236584 := by exact prefixLift 1236584
  have htrace : WordTrace (prefixWord ++ tailWord_1236584) baseStart_1236584 baseEnd_1236584 := by
    simpa [prefixWord, tailWord_1236584, baseEnd_1236584] using wordTrace_append hprefix tailTrace_1236584
  have hstable : (prefixWord ++ tailWord_1236584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236584).length < 2 ^ (prefixWord ++ tailWord_1236584).sum := by decide
  have hdescent : baseEnd_1236584 < baseStart_1236584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236671 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 6]
def baseStart_1236671 : Nat := 118140960795 + 1236671 * 2 ^ 59
def prefixEnd_1236671 : Nat := 4983230072969 + 3 ^ 40 * 1236671 * 2
def baseEnd_1236671 : Nat := 282225170878416112322293

theorem tailTrace_1236671 : CollatzResearch.WordTrace tailWord_1236671 prefixEnd_1236671 282225170878416112322293 := by
  unfold tailWord_1236671
  simp only [CollatzResearch.WordTrace]
  refine ⟨45105096902759648436893867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30070064601839765624595911 45105096902759648436893867)
  ·
    refine ⟨67657645354139472655340801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45105096902759648436893867 67657645354139472655340801)
    ·
      refine ⟨50743234015604604491505601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67657645354139472655340801 50743234015604604491505601)
      ·
        refine ⟨38057425511703453368629201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50743234015604604491505601 38057425511703453368629201)
        ·
          refine ⟨28543069133777590026471901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38057425511703453368629201 28543069133777590026471901)
          ·
            refine ⟨10703650925166596259926963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28543069133777590026471901 10703650925166596259926963)
            ·
              refine ⟨16055476387749894389890445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10703650925166596259926963 16055476387749894389890445)
              ·
                refine ⟨6020803645406210396208917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16055476387749894389890445 6020803645406210396208917)
                ·
                  refine ⟨282225170878416112322293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6020803645406210396208917 282225170878416112322293)
                  ·
                    rfl

theorem cell21_1236671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 6].length) (baseStart_1236671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236671 prefixEnd_1236671 := by exact prefixLift 1236671
  have htrace : WordTrace (prefixWord ++ tailWord_1236671) baseStart_1236671 baseEnd_1236671 := by
    simpa [prefixWord, tailWord_1236671, baseEnd_1236671] using wordTrace_append hprefix tailTrace_1236671
  have hstable : (prefixWord ++ tailWord_1236671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236671).length < 2 ^ (prefixWord ++ tailWord_1236671).sum := by decide
  have hdescent : baseEnd_1236671 < baseStart_1236671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236742 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1236742 : Nat := 118140960795 + 1236742 * 2 ^ 59
def prefixEnd_1236742 : Nat := 4983230072969 + 3 ^ 40 * 1236742 * 2
def baseEnd_1236742 : Nat := 282241374045735766638815

theorem tailTrace_1236742 : CollatzResearch.WordTrace tailWord_1236742 prefixEnd_1236742 282241374045735766638815 := by
  unfold tailWord_1236742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1409615202671950861335265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30071790990334951708485653 1409615202671950861335265)
  ·
    refine ⟨1057211402003963146001449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1409615202671950861335265 1057211402003963146001449)
    ·
      refine ⟨792908551502972359501087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1057211402003963146001449 792908551502972359501087)
      ·
        refine ⟨1189362827254458539251631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 792908551502972359501087 1189362827254458539251631)
        ·
          refine ⟨1784044240881687808877447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1189362827254458539251631 1784044240881687808877447)
          ·
            refine ⟨2676066361322531713316171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1784044240881687808877447 2676066361322531713316171)
            ·
              refine ⟨4014099541983797569974257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2676066361322531713316171 4014099541983797569974257)
              ·
                refine ⟨3010574656487848177480693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4014099541983797569974257 3010574656487848177480693)
                ·
                  refine ⟨282241374045735766638815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3010574656487848177480693 282241374045735766638815)
                  ·
                    rfl

theorem cell21_1236742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1236742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236742 prefixEnd_1236742 := by exact prefixLift 1236742
  have htrace : WordTrace (prefixWord ++ tailWord_1236742) baseStart_1236742 baseEnd_1236742 := by
    simpa [prefixWord, tailWord_1236742, baseEnd_1236742] using wordTrace_append hprefix tailTrace_1236742
  have hstable : (prefixWord ++ tailWord_1236742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236742).length < 2 ^ (prefixWord ++ tailWord_1236742).sum := by decide
  have hdescent : baseEnd_1236742 < baseStart_1236742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236798 : List Nat := [4, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1236798 : Nat := 118140960795 + 1236798 * 2 ^ 59
def prefixEnd_1236798 : Nat := 4983230072969 + 3 ^ 40 * 1236798 * 2
def baseEnd_1236798 : Nat := 282254154008692113705367

theorem tailTrace_1236798 : CollatzResearch.WordTrace tailWord_1236798 prefixEnd_1236798 282254154008692113705367 := by
  unfold tailWord_1236798
  simp only [CollatzResearch.WordTrace]
  refine ⟨5638716121662443640845881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30073152648866366084511365 5638716121662443640845881)
  ·
    refine ⟨4229037091246832730634411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5638716121662443640845881 4229037091246832730634411)
    ·
      refine ⟨6343555636870249095951617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4229037091246832730634411 6343555636870249095951617)
      ·
        refine ⟨4757666727652686821963713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6343555636870249095951617 4757666727652686821963713)
        ·
          refine ⟨3568250045739515116472785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4757666727652686821963713 3568250045739515116472785)
          ·
            refine ⟨2676187534304636337354589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3568250045739515116472785 2676187534304636337354589)
            ·
              refine ⟨1003570325364238626507971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2676187534304636337354589 1003570325364238626507971)
              ·
                refine ⟨1505355488046357939761957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1003570325364238626507971 1505355488046357939761957)
                ·
                  refine ⟨282254154008692113705367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1505355488046357939761957 282254154008692113705367)
                  ·
                    rfl

theorem cell21_1236798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1236798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236798 prefixEnd_1236798 := by exact prefixLift 1236798
  have htrace : WordTrace (prefixWord ++ tailWord_1236798) baseStart_1236798 baseEnd_1236798 := by
    simpa [prefixWord, tailWord_1236798, baseEnd_1236798] using wordTrace_append hprefix tailTrace_1236798
  have hstable : (prefixWord ++ tailWord_1236798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236798).length < 2 ^ (prefixWord ++ tailWord_1236798).sum := by decide
  have hdescent : baseEnd_1236798 < baseStart_1236798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236812 : List Nat := [2, 2, 1, 3, 4, 2, 2, 5]
def baseStart_1236812 : Nat := 118140960795 + 1236812 * 2 ^ 59
def prefixEnd_1236812 : Nat := 4983230072969 + 3 ^ 40 * 1236812 * 2
def baseEnd_1236812 : Nat := 94085782999810400157335

theorem tailTrace_1236812 : CollatzResearch.WordTrace tailWord_1236812 prefixEnd_1236812 94085782999810400157335 := by
  unfold tailWord_1236812
  simp only [CollatzResearch.WordTrace]
  refine ⟨22555119797624414758888345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30073493063499219678517793 22555119797624414758888345)
  ·
    refine ⟨16916339848218311069166259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22555119797624414758888345 16916339848218311069166259)
    ·
      refine ⟨25374509772327466603749389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16916339848218311069166259 25374509772327466603749389)
      ·
        refine ⟨9515441164622799976406021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25374509772327466603749389 9515441164622799976406021)
        ·
          refine ⟨1784145218366774995576129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9515441164622799976406021 1784145218366774995576129)
          ·
            refine ⟨1338108913775081246682097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1784145218366774995576129 1338108913775081246682097)
            ·
              refine ⟨1003581685331310935011573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1338108913775081246682097 1003581685331310935011573)
              ·
                refine ⟨94085782999810400157335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1003581685331310935011573 94085782999810400157335)
                ·
                  rfl

theorem cell21_1236812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 5].length) (baseStart_1236812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236812 prefixEnd_1236812 := by exact prefixLift 1236812
  have htrace : WordTrace (prefixWord ++ tailWord_1236812) baseStart_1236812 baseEnd_1236812 := by
    simpa [prefixWord, tailWord_1236812, baseEnd_1236812] using wordTrace_append hprefix tailTrace_1236812
  have hstable : (prefixWord ++ tailWord_1236812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236812).length < 2 ^ (prefixWord ++ tailWord_1236812).sum := by decide
  have hdescent : baseEnd_1236812 < baseStart_1236812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236840 : List Nat := [2, 1, 4, 2, 1, 1, 2, 4, 4]
def baseStart_1236840 : Nat := 118140960795 + 1236840 * 2 ^ 59
def prefixEnd_1236840 : Nat := 4983230072969 + 3 ^ 40 * 1236840 * 2
def baseEnd_1236840 : Nat := 282263738980909374005281

theorem tailTrace_1236840 : CollatzResearch.WordTrace tailWord_1236840 prefixEnd_1236840 282263738980909374005281 := by
  unfold tailWord_1236840
  simp only [CollatzResearch.WordTrace]
  refine ⟨22555630419573695149897987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30074173892764926866530649 22555630419573695149897987)
  ·
    refine ⟨33833445629360542724846981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22555630419573695149897987 33833445629360542724846981)
    ·
      refine ⟨6343771055505101760908809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33833445629360542724846981 6343771055505101760908809)
      ·
        refine ⟨4757828291628826320681607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6343771055505101760908809 4757828291628826320681607)
        ·
          refine ⟨7136742437443239481022411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4757828291628826320681607 7136742437443239481022411)
          ·
            refine ⟨10705113656164859221533617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7136742437443239481022411 10705113656164859221533617)
            ·
              refine ⟨8028835242123644416150213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10705113656164859221533617 8028835242123644416150213)
              ·
                refine ⟨1505406607898183328028165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8028835242123644416150213 1505406607898183328028165)
                ·
                  refine ⟨282263738980909374005281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1505406607898183328028165 282263738980909374005281)
                  ·
                    rfl

theorem cell21_1236840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_1236840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236840 prefixEnd_1236840 := by exact prefixLift 1236840
  have htrace : WordTrace (prefixWord ++ tailWord_1236840) baseStart_1236840 baseEnd_1236840 := by
    simpa [prefixWord, tailWord_1236840, baseEnd_1236840] using wordTrace_append hprefix tailTrace_1236840
  have hstable : (prefixWord ++ tailWord_1236840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236840).length < 2 ^ (prefixWord ++ tailWord_1236840).sum := by decide
  have hdescent : baseEnd_1236840 < baseStart_1236840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236894 : List Nat := [4, 3, 1, 3, 1, 2, 2, 2, 3]
def baseStart_1236894 : Nat := 118140960795 + 1236894 * 2 ^ 59
def prefixEnd_1236894 : Nat := 4983230072969 + 3 ^ 40 * 1236894 * 2
def baseEnd_1236894 : Nat := 282276062516617280105171

theorem tailTrace_1236894 : CollatzResearch.WordTrace tailWord_1236894 prefixEnd_1236894 282276062516617280105171 := by
  unfold tailWord_1236894
  simp only [CollatzResearch.WordTrace]
  refine ⟨5639153797618969690282717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30075486920634505014841157 5639153797618969690282717)
  ·
    refine ⟨2114682674107113633856019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5639153797618969690282717 2114682674107113633856019)
    ·
      refine ⟨3172024011160670450784029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2114682674107113633856019 3172024011160670450784029)
      ·
        refine ⟨1189509004185251419044011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3172024011160670450784029 1189509004185251419044011)
        ·
          refine ⟨1784263506277877128566017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1189509004185251419044011 1784263506277877128566017)
          ·
            refine ⟨1338197629708407846424513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1784263506277877128566017 1338197629708407846424513)
            ·
              refine ⟨1003648222281305884818385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1338197629708407846424513 1003648222281305884818385)
              ·
                refine ⟨752736166710979413613789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1003648222281305884818385 752736166710979413613789)
                ·
                  refine ⟨282276062516617280105171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 752736166710979413613789 282276062516617280105171)
                  ·
                    rfl

theorem cell21_1236894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_1236894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236894 prefixEnd_1236894 := by exact prefixLift 1236894
  have htrace : WordTrace (prefixWord ++ tailWord_1236894) baseStart_1236894 baseEnd_1236894 := by
    simpa [prefixWord, tailWord_1236894, baseEnd_1236894] using wordTrace_append hprefix tailTrace_1236894
  have hstable : (prefixWord ++ tailWord_1236894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236894).length < 2 ^ (prefixWord ++ tailWord_1236894).sum := by decide
  have hdescent : baseEnd_1236894 < baseStart_1236894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236998 : List Nat := [6, 2, 1, 2, 1, 2, 7]
def baseStart_1236998 : Nat := 118140960795 + 1236998 * 2 ^ 59
def prefixEnd_1236998 : Nat := 4983230072969 + 3 ^ 40 * 1236998 * 2
def baseEnd_1236998 : Nat := 31366644081504023374625

theorem tailTrace_1236998 : CollatzResearch.WordTrace tailWord_1236998 prefixEnd_1236998 31366644081504023374625 := by
  unfold tailWord_1236998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1409906986642968227626489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30078015715049988856031765 1409906986642968227626489)
  ·
    refine ⟨1057430239982226170719867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1409906986642968227626489 1057430239982226170719867)
    ·
      refine ⟨1586145359973339256079801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1057430239982226170719867 1586145359973339256079801)
      ·
        refine ⟨1189609019980004442059851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1586145359973339256079801 1189609019980004442059851)
        ·
          refine ⟨1784413529970006663089777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1189609019980004442059851 1784413529970006663089777)
          ·
            refine ⟨1338310147477504997317333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1784413529970006663089777 1338310147477504997317333)
            ·
              refine ⟨31366644081504023374625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1338310147477504997317333 31366644081504023374625)
              ·
                rfl

theorem cell21_1236998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 7].length) (baseStart_1236998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1236998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1236998 prefixEnd_1236998 := by exact prefixLift 1236998
  have htrace : WordTrace (prefixWord ++ tailWord_1236998) baseStart_1236998 baseEnd_1236998 := by
    simpa [prefixWord, tailWord_1236998, baseEnd_1236998] using wordTrace_append hprefix tailTrace_1236998
  have hstable : (prefixWord ++ tailWord_1236998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236998).length < 2 ^ (prefixWord ++ tailWord_1236998).sum := by decide
  have hdescent : baseEnd_1236998 < baseStart_1236998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237012 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 5]
def baseStart_1237012 : Nat := 118140960795 + 1237012 * 2 ^ 59
def prefixEnd_1237012 : Nat := 4983230072969 + 3 ^ 40 * 1237012 * 2
def baseEnd_1237012 : Nat := 282302991724275297138263

theorem tailTrace_1237012 : CollatzResearch.WordTrace tailWord_1237012 prefixEnd_1237012 282302991724275297138263 := by
  unfold tailWord_1237012
  simp only [CollatzResearch.WordTrace]
  refine ⟨22558767097262131837528645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30078356129682842450038193 22558767097262131837528645)
  ·
    refine ⟨4229768830736649719536621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22558767097262131837528645 4229768830736649719536621)
    ·
      refine ⟨1586163311526243644826233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4229768830736649719536621 1586163311526243644826233)
      ·
        refine ⟨1189622483644682733619675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1586163311526243644826233 1189622483644682733619675)
        ·
          refine ⟨1784433725467024100429513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1189622483644682733619675 1784433725467024100429513)
          ·
            refine ⟨1338325294100268075322135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1784433725467024100429513 1338325294100268075322135)
            ·
              refine ⟨2007487941150402112983203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338325294100268075322135 2007487941150402112983203)
              ·
                refine ⟨3011231911725603169474805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2007487941150402112983203 3011231911725603169474805)
                ·
                  refine ⟨282302991724275297138263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3011231911725603169474805 282302991724275297138263)
                  ·
                    rfl

theorem cell21_1237012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_1237012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237012 prefixEnd_1237012 := by exact prefixLift 1237012
  have htrace : WordTrace (prefixWord ++ tailWord_1237012) baseStart_1237012 baseEnd_1237012 := by
    simpa [prefixWord, tailWord_1237012, baseEnd_1237012] using wordTrace_append hprefix tailTrace_1237012
  have hstable : (prefixWord ++ tailWord_1237012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237012).length < 2 ^ (prefixWord ++ tailWord_1237012).sum := by decide
  have hdescent : baseEnd_1237012 < baseStart_1237012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237085 : List Nat := [1, 4, 4, 1, 1, 1, 2, 3, 4]
def baseStart_1237085 : Nat := 118140960795 + 1237085 * 2 ^ 59
def prefixEnd_1237085 : Nat := 4983230072969 + 3 ^ 40 * 1237085 * 2
def baseEnd_1237085 : Nat := 282319651318843392421447

theorem tailTrace_1237085 : CollatzResearch.WordTrace tailWord_1237085 prefixEnd_1237085 282319651318843392421447 := by
  unfold tailWord_1237085
  simp only [CollatzResearch.WordTrace]
  refine ⟨45120196723259797142464709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30080131148839864761643139 45120196723259797142464709)
  ·
    refine ⟨8460036885611211964212133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45120196723259797142464709 8460036885611211964212133)
    ·
      refine ⟨1586256916052102243289775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8460036885611211964212133 1586256916052102243289775)
      ·
        refine ⟨2379385374078153364934663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1586256916052102243289775 2379385374078153364934663)
        ·
          refine ⟨3569078061117230047401995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2379385374078153364934663 3569078061117230047401995)
          ·
            refine ⟨5353617091675845071102993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3569078061117230047401995 5353617091675845071102993)
            ·
              refine ⟨4015212818756883803327245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5353617091675845071102993 4015212818756883803327245)
              ·
                refine ⟨1505704807033831426247717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4015212818756883803327245 1505704807033831426247717)
                ·
                  refine ⟨282319651318843392421447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1505704807033831426247717 282319651318843392421447)
                  ·
                    rfl

theorem cell21_1237085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_1237085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237085 prefixEnd_1237085 := by exact prefixLift 1237085
  have htrace : WordTrace (prefixWord ++ tailWord_1237085) baseStart_1237085 baseEnd_1237085 := by
    simpa [prefixWord, tailWord_1237085, baseEnd_1237085] using wordTrace_append hprefix tailTrace_1237085
  have hstable : (prefixWord ++ tailWord_1237085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237085).length < 2 ^ (prefixWord ++ tailWord_1237085).sum := by decide
  have hdescent : baseEnd_1237085 < baseStart_1237085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237130 : List Nat := [3, 1, 2, 3, 1, 2, 2, 4, 3]
def baseStart_1237130 : Nat := 118140960795 + 1237130 * 2 ^ 59
def prefixEnd_1237130 : Nat := 4983230072969 + 3 ^ 40 * 1237130 * 2
def baseEnd_1237130 : Nat := 282329920931933314171355

theorem tailTrace_1237130 : CollatzResearch.WordTrace tailWord_1237130 prefixEnd_1237130 282329920931933314171355 := by
  unfold tailWord_1237130
  simp only [CollatzResearch.WordTrace]
  refine ⟨11280459502024192456963211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30081225338731179885235229 11280459502024192456963211)
  ·
    refine ⟨16920689253036288685444817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11280459502024192456963211 16920689253036288685444817)
    ·
      refine ⟨12690516939777216514083613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16920689253036288685444817 12690516939777216514083613)
      ·
        refine ⟨4758943852416456192781355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12690516939777216514083613 4758943852416456192781355)
        ·
          refine ⟨7138415778624684289172033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4758943852416456192781355 7138415778624684289172033)
          ·
            refine ⟨5353811833968513216879025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7138415778624684289172033 5353811833968513216879025)
            ·
              refine ⟨4015358875476384912659269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5353811833968513216879025 4015358875476384912659269)
              ·
                refine ⟨752879789151822171123613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4015358875476384912659269 752879789151822171123613)
                ·
                  refine ⟨282329920931933314171355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 752879789151822171123613 282329920931933314171355)
                  ·
                    rfl

theorem cell21_1237130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_1237130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237130 prefixEnd_1237130 := by exact prefixLift 1237130
  have htrace : WordTrace (prefixWord ++ tailWord_1237130) baseStart_1237130 baseEnd_1237130 := by
    simpa [prefixWord, tailWord_1237130, baseEnd_1237130] using wordTrace_append hprefix tailTrace_1237130
  have hstable : (prefixWord ++ tailWord_1237130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237130).length < 2 ^ (prefixWord ++ tailWord_1237130).sum := by decide
  have hdescent : baseEnd_1237130 < baseStart_1237130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237141 : List Nat := [1, 3, 2, 1, 1, 1, 4, 8]
def baseStart_1237141 : Nat := 118140960795 + 1237141 * 2 ^ 59
def prefixEnd_1237141 : Nat := 4983230072969 + 3 ^ 40 * 1237141 * 2
def baseEnd_1237141 : Nat := 94110810427266579829333

theorem tailTrace_1237141 : CollatzResearch.WordTrace tailWord_1237141 prefixEnd_1237141 94110810427266579829333 := by
  unfold tailWord_1237141
  simp only [CollatzResearch.WordTrace]
  refine ⟨45122239211056918706503277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30081492807371279137668851 45122239211056918706503277)
  ·
    refine ⟨16920839704146344514938729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45122239211056918706503277 16920839704146344514938729)
    ·
      refine ⟨12690629778109758386204047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16920839704146344514938729 12690629778109758386204047)
      ·
        refine ⟨19035944667164637579306071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12690629778109758386204047 19035944667164637579306071)
        ·
          refine ⟨28553917000746956368959107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19035944667164637579306071 28553917000746956368959107)
          ·
            refine ⟨42830875501120434553438661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28553917000746956368959107 42830875501120434553438661)
            ·
              refine ⟨8030789156460081478769749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42830875501120434553438661 8030789156460081478769749)
              ·
                refine ⟨94110810427266579829333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8030789156460081478769749 94110810427266579829333)
                ·
                  rfl

theorem cell21_1237141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 8].length) (baseStart_1237141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237141 prefixEnd_1237141 := by exact prefixLift 1237141
  have htrace : WordTrace (prefixWord ++ tailWord_1237141) baseStart_1237141 baseEnd_1237141 := by
    simpa [prefixWord, tailWord_1237141, baseEnd_1237141] using wordTrace_append hprefix tailTrace_1237141
  have hstable : (prefixWord ++ tailWord_1237141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237141).length < 2 ^ (prefixWord ++ tailWord_1237141).sum := by decide
  have hdescent : baseEnd_1237141 < baseStart_1237141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237189 : List Nat := [1, 3, 1, 1, 1, 1, 4, 6, 3]
def baseStart_1237189 : Nat := 118140960795 + 1237189 * 2 ^ 59
def prefixEnd_1237189 : Nat := 4983230072969 + 3 ^ 40 * 1237189 * 2
def baseEnd_1237189 : Nat := 282343385535762322687901

theorem tailTrace_1237189 : CollatzResearch.WordTrace tailWord_1237189 prefixEnd_1237189 282343385535762322687901 := by
  unfold tailWord_1237189
  simp only [CollatzResearch.WordTrace]
  refine ⟨45123989914883022904250621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30082659943255348602833747 45123989914883022904250621)
  ·
    refine ⟨16921496218081133589093983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45123989914883022904250621 16921496218081133589093983)
    ·
      refine ⟨25382244327121700383640975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16921496218081133589093983 25382244327121700383640975)
      ·
        refine ⟨38073366490682550575461463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25382244327121700383640975 38073366490682550575461463)
        ·
          refine ⟨57110049736023825863192195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38073366490682550575461463 57110049736023825863192195)
          ·
            refine ⟨85665074604035738794788293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57110049736023825863192195 85665074604035738794788293)
            ·
              refine ⟨16062201488256701024022805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85665074604035738794788293 16062201488256701024022805)
              ·
                refine ⟨752915694762032860501069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16062201488256701024022805 752915694762032860501069)
                ·
                  refine ⟨282343385535762322687901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 752915694762032860501069 282343385535762322687901)
                  ·
                    rfl

theorem cell21_1237189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_1237189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237189 prefixEnd_1237189 := by exact prefixLift 1237189
  have htrace : WordTrace (prefixWord ++ tailWord_1237189) baseStart_1237189 baseEnd_1237189 := by
    simpa [prefixWord, tailWord_1237189, baseEnd_1237189] using wordTrace_append hprefix tailTrace_1237189
  have hstable : (prefixWord ++ tailWord_1237189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237189).length < 2 ^ (prefixWord ++ tailWord_1237189).sum := by decide
  have hdescent : baseEnd_1237189 < baseStart_1237189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237217 : List Nat := [1, 2, 3, 1, 3, 1, 1, 9]
def baseStart_1237217 : Nat := 118140960795 + 1237217 * 2 ^ 59
def prefixEnd_1237217 : Nat := 4983230072969 + 3 ^ 40 * 1237217 * 2
def baseEnd_1237217 : Nat := 94116591839080165407059

theorem tailTrace_1237217 : CollatzResearch.WordTrace tailWord_1237217 prefixEnd_1237217 94116591839080165407059 := by
  unfold tailWord_1237217
  simp only [CollatzResearch.WordTrace]
  refine ⟨45125011158781583686269905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30083340772521055790846603 45125011158781583686269905)
  ·
    refine ⟨33843758369086187764702429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45125011158781583686269905 33843758369086187764702429)
    ·
      refine ⟨12691409388407320411763411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33843758369086187764702429 12691409388407320411763411)
      ·
        refine ⟨19037114082610980617645117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12691409388407320411763411 19037114082610980617645117)
        ·
          refine ⟨7138917780979117731616919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19037114082610980617645117 7138917780979117731616919)
          ·
            refine ⟨10708376671468676597425379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7138917780979117731616919 10708376671468676597425379)
            ·
              refine ⟨16062565007203014896138069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10708376671468676597425379 16062565007203014896138069)
              ·
                refine ⟨94116591839080165407059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16062565007203014896138069 94116591839080165407059)
                ·
                  rfl

theorem cell21_1237217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 9].length) (baseStart_1237217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237217 prefixEnd_1237217 := by exact prefixLift 1237217
  have htrace : WordTrace (prefixWord ++ tailWord_1237217) baseStart_1237217 baseEnd_1237217 := by
    simpa [prefixWord, tailWord_1237217, baseEnd_1237217] using wordTrace_append hprefix tailTrace_1237217
  have hstable : (prefixWord ++ tailWord_1237217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237217).length < 2 ^ (prefixWord ++ tailWord_1237217).sum := by decide
  have hdescent : baseEnd_1237217 < baseStart_1237217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237282 : List Nat := [3, 3, 1, 1, 3, 1, 1, 5, 3]
def baseStart_1237282 : Nat := 118140960795 + 1237282 * 2 ^ 59
def prefixEnd_1237282 : Nat := 4983230072969 + 3 ^ 40 * 1237282 * 2
def baseEnd_1237282 : Nat := 282364609402814827637711

theorem tailTrace_1237282 : CollatzResearch.WordTrace tailWord_1237282 prefixEnd_1237282 282364609402814827637711 := by
  unfold tailWord_1237282
  simp only [CollatzResearch.WordTrace]
  refine ⟨11281845475886524946846525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30084921269030733191590733 11281845475886524946846525)
  ·
    refine ⟨4230692053457446855067447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11281845475886524946846525 4230692053457446855067447)
    ·
      refine ⟨6346038080186170282601171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4230692053457446855067447 6346038080186170282601171)
      ·
        refine ⟨9519057120279255423901757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6346038080186170282601171 9519057120279255423901757)
        ·
          refine ⟨3569646420104720783963159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9519057120279255423901757 3569646420104720783963159)
          ·
            refine ⟨5354469630157081175944739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3569646420104720783963159 5354469630157081175944739)
            ·
              refine ⟨8031704445235621763917109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5354469630157081175944739 8031704445235621763917109)
              ·
                refine ⟨752972291740839540367229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8031704445235621763917109 752972291740839540367229)
                ·
                  refine ⟨282364609402814827637711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 752972291740839540367229 282364609402814827637711)
                  ·
                    rfl

theorem cell21_1237282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_1237282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237282 prefixEnd_1237282 := by exact prefixLift 1237282
  have htrace : WordTrace (prefixWord ++ tailWord_1237282) baseStart_1237282 baseEnd_1237282 := by
    simpa [prefixWord, tailWord_1237282, baseEnd_1237282] using wordTrace_append hprefix tailTrace_1237282
  have hstable : (prefixWord ++ tailWord_1237282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237282).length < 2 ^ (prefixWord ++ tailWord_1237282).sum := by decide
  have hdescent : baseEnd_1237282 < baseStart_1237282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237324 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 5]
def baseStart_1237324 : Nat := 118140960795 + 1237324 * 2 ^ 59
def prefixEnd_1237324 : Nat := 4983230072969 + 3 ^ 40 * 1237324 * 2
def baseEnd_1237324 : Nat := 282374194375032087937625

theorem tailTrace_1237324 : CollatzResearch.WordTrace tailWord_1237324 prefixEnd_1237324 282374194375032087937625 := by
  unfold tailWord_1237324
  simp only [CollatzResearch.WordTrace]
  refine ⟨22564456884696970480207513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30085942512929293973610017 22564456884696970480207513)
  ·
    refine ⟨16923342663522727860155635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22564456884696970480207513 16923342663522727860155635)
    ·
      refine ⟨25385013995284091790233453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16923342663522727860155635 25385013995284091790233453)
      ·
        refine ⟨9519380248231534421337545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25385013995284091790233453 9519380248231534421337545)
        ·
          refine ⟨7139535186173650816003159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9519380248231534421337545 7139535186173650816003159)
          ·
            refine ⟨10709302779260476224004739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7139535186173650816003159 10709302779260476224004739)
            ·
              refine ⟨16063954168890714336007109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10709302779260476224004739 16063954168890714336007109)
              ·
                refine ⟨3011991406667008938001333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16063954168890714336007109 3011991406667008938001333)
                ·
                  refine ⟨282374194375032087937625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3011991406667008938001333 282374194375032087937625)
                  ·
                    rfl

theorem cell21_1237324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_1237324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237324 prefixEnd_1237324 := by exact prefixLift 1237324
  have htrace : WordTrace (prefixWord ++ tailWord_1237324) baseStart_1237324 baseEnd_1237324 := by
    simpa [prefixWord, tailWord_1237324, baseEnd_1237324] using wordTrace_append hprefix tailTrace_1237324
  have hstable : (prefixWord ++ tailWord_1237324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237324).length < 2 ^ (prefixWord ++ tailWord_1237324).sum := by decide
  have hdescent : baseEnd_1237324 < baseStart_1237324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237409 : List Nat := [1, 2, 3, 5, 2, 1, 2, 2, 3]
def baseStart_1237409 : Nat := 118140960795 + 1237409 * 2 ^ 59
def prefixEnd_1237409 : Nat := 4983230072969 + 3 ^ 40 * 1237409 * 2
def baseEnd_1237409 : Nat := 282393592533090829020785

theorem tailTrace_1237409 : CollatzResearch.WordTrace tailWord_1237409 prefixEnd_1237409 282393592533090829020785 := by
  unfold tailWord_1237409
  simp only [CollatzResearch.WordTrace]
  refine ⟨45132013974086000477259281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30088009316057333651506187 45132013974086000477259281)
  ·
    refine ⟨33849010480564500357944461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45132013974086000477259281 33849010480564500357944461)
    ·
      refine ⟨12693378930211687634229173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33849010480564500357944461 12693378930211687634229173)
      ·
        refine ⟨1190004274707345715708985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12693378930211687634229173 1190004274707345715708985)
        ·
          refine ⟨892503206030509286781739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1190004274707345715708985 892503206030509286781739)
          ·
            refine ⟨1338754809045763930172609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892503206030509286781739 1338754809045763930172609)
            ·
              refine ⟨1004066106784322947629457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1338754809045763930172609 1004066106784322947629457)
              ·
                refine ⟨753049580088242210722093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1004066106784322947629457 753049580088242210722093)
                ·
                  refine ⟨282393592533090829020785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 753049580088242210722093 282393592533090829020785)
                  ·
                    rfl

theorem cell21_1237409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 3].length) (baseStart_1237409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237409 prefixEnd_1237409 := by exact prefixLift 1237409
  have htrace : WordTrace (prefixWord ++ tailWord_1237409) baseStart_1237409 baseEnd_1237409 := by
    simpa [prefixWord, tailWord_1237409, baseEnd_1237409] using wordTrace_append hprefix tailTrace_1237409
  have hstable : (prefixWord ++ tailWord_1237409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237409).length < 2 ^ (prefixWord ++ tailWord_1237409).sum := by decide
  have hdescent : baseEnd_1237409 < baseStart_1237409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237431 : List Nat := [1, 1, 3, 1, 3, 3, 2, 3, 4]
def baseStart_1237431 : Nat := 118140960795 + 1237431 * 2 ^ 59
def prefixEnd_1237431 : Nat := 4983230072969 + 3 ^ 40 * 1237431 * 2
def baseEnd_1237431 : Nat := 282398613232823679654073

theorem tailTrace_1237431 : CollatzResearch.WordTrace tailWord_1237431 prefixEnd_1237431 282398613232823679654073 := by
  unfold tailWord_1237431
  simp only [CollatzResearch.WordTrace]
  refine ⟨45132816380006298234560147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30088544253337532156373431 45132816380006298234560147)
  ·
    refine ⟨67699224570009447351840221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45132816380006298234560147 67699224570009447351840221)
    ·
      refine ⟨25387209213753542756940083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67699224570009447351840221 25387209213753542756940083)
      ·
        refine ⟨38080813820630314135410125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25387209213753542756940083 38080813820630314135410125)
        ·
          refine ⟨14280305182736367800778797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38080813820630314135410125 14280305182736367800778797)
          ·
            refine ⟨5355114443526137925292049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14280305182736367800778797 5355114443526137925292049)
            ·
              refine ⟨4016335832644603443969037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5355114443526137925292049 4016335832644603443969037)
              ·
                refine ⟨1506125937241726291488389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4016335832644603443969037 1506125937241726291488389)
                ·
                  refine ⟨282398613232823679654073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1506125937241726291488389 282398613232823679654073)
                  ·
                    rfl

theorem cell21_1237431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 4].length) (baseStart_1237431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237431 prefixEnd_1237431 := by exact prefixLift 1237431
  have htrace : WordTrace (prefixWord ++ tailWord_1237431) baseStart_1237431 baseEnd_1237431 := by
    simpa [prefixWord, tailWord_1237431, baseEnd_1237431] using wordTrace_append hprefix tailTrace_1237431
  have hstable : (prefixWord ++ tailWord_1237431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237431).length < 2 ^ (prefixWord ++ tailWord_1237431).sum := by decide
  have hdescent : baseEnd_1237431 < baseStart_1237431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237462 : List Nat := [5, 2, 1, 1, 1, 1, 10]
def baseStart_1237462 : Nat := 118140960795 + 1237462 * 2 ^ 59
def prefixEnd_1237462 : Nat := 4983230072969 + 3 ^ 40 * 1237462 * 2
def baseEnd_1237462 : Nat := 31378409761686057181927

theorem tailTrace_1237462 : CollatzResearch.WordTrace tailWord_1237462 prefixEnd_1237462 31378409761686057181927 := by
  unfold tailWord_1237462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2820871690180874408058665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30089298028595993685959093 2820871690180874408058665)
  ·
    refine ⟨2115653767635655806043999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2820871690180874408058665 2115653767635655806043999)
    ·
      refine ⟨3173480651453483709065999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2115653767635655806043999 3173480651453483709065999)
      ·
        refine ⟨4760220977180225563598999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3173480651453483709065999 4760220977180225563598999)
        ·
          refine ⟨7140331465770338345398499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4760220977180225563598999 7140331465770338345398499)
          ·
            refine ⟨10710497198655507518097749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7140331465770338345398499 10710497198655507518097749)
            ·
              refine ⟨31378409761686057181927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10710497198655507518097749 31378409761686057181927)
              ·
                rfl

theorem cell21_1237462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 10].length) (baseStart_1237462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237462 prefixEnd_1237462 := by exact prefixLift 1237462
  have htrace : WordTrace (prefixWord ++ tailWord_1237462) baseStart_1237462 baseEnd_1237462 := by
    simpa [prefixWord, tailWord_1237462, baseEnd_1237462] using wordTrace_append hprefix tailTrace_1237462
  have hstable : (prefixWord ++ tailWord_1237462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237462).length < 2 ^ (prefixWord ++ tailWord_1237462).sum := by decide
  have hdescent : baseEnd_1237462 < baseStart_1237462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237524 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 6]
def baseStart_1237524 : Nat := 118140960795 + 1237524 * 2 ^ 59
def prefixEnd_1237524 : Nat := 4983230072969 + 3 ^ 40 * 1237524 * 2
def baseEnd_1237524 : Nat := 282419837099876184603883

theorem tailTrace_1237524 : CollatzResearch.WordTrace tailWord_1237524 prefixEnd_1237524 282419837099876184603883 := by
  unfold tailWord_1237524
  simp only [CollatzResearch.WordTrace]
  refine ⟨22568104184334687558847813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30090805579112916745130417 22568104184334687558847813)
  ·
    refine ⟨4231519534562753917283965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22568104184334687558847813 4231519534562753917283965)
    ·
      refine ⟨1586819825461032718981487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4231519534562753917283965 1586819825461032718981487)
      ·
        refine ⟨2380229738191549078472231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1586819825461032718981487 2380229738191549078472231)
        ·
          refine ⟨3570344607287323617708347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2380229738191549078472231 3570344607287323617708347)
          ·
            refine ⟨5355516910930985426562521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3570344607287323617708347 5355516910930985426562521)
            ·
              refine ⟨4016637683198239069921891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5355516910930985426562521 4016637683198239069921891)
              ·
                refine ⟨6024956524797358604882837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4016637683198239069921891 6024956524797358604882837)
                ·
                  refine ⟨282419837099876184603883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6024956524797358604882837 282419837099876184603883)
                  ·
                    rfl

theorem cell21_1237524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_1237524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237524 prefixEnd_1237524 := by exact prefixLift 1237524
  have htrace : WordTrace (prefixWord ++ tailWord_1237524) baseStart_1237524 baseEnd_1237524 := by
    simpa [prefixWord, tailWord_1237524, baseEnd_1237524] using wordTrace_append hprefix tailTrace_1237524
  have hstable : (prefixWord ++ tailWord_1237524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237524).length < 2 ^ (prefixWord ++ tailWord_1237524).sum := by decide
  have hdescent : baseEnd_1237524 < baseStart_1237524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237527 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 5]
def baseStart_1237527 : Nat := 118140960795 + 1237527 * 2 ^ 59
def prefixEnd_1237527 : Nat := 4983230072969 + 3 ^ 40 * 1237527 * 2
def baseEnd_1237527 : Nat := 282420521740748846053877

theorem tailTrace_1237527 : CollatzResearch.WordTrace tailWord_1237527 prefixEnd_1237527 282420521740748846053877 := by
  unfold tailWord_1237527
  simp only [CollatzResearch.WordTrace]
  refine ⟨45136317787658506630054835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30090878525105671086703223 45136317787658506630054835)
  ·
    refine ⟨67704476681487759945082253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45136317787658506630054835 67704476681487759945082253)
    ·
      refine ⟨25389178755557909979405845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67704476681487759945082253 25389178755557909979405845)
      ·
        refine ⟨1190117754166777030284649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25389178755557909979405845 1190117754166777030284649)
        ·
          refine ⟨892588315625082772713487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1190117754166777030284649 892588315625082772713487)
          ·
            refine ⟨1338882473437624159070231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892588315625082772713487 1338882473437624159070231)
            ·
              refine ⟨2008323710156436238605347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338882473437624159070231 2008323710156436238605347)
              ·
                refine ⟨3012485565234654357908021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008323710156436238605347 3012485565234654357908021)
                ·
                  refine ⟨282420521740748846053877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3012485565234654357908021 282420521740748846053877)
                  ·
                    rfl

theorem cell21_1237527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 5].length) (baseStart_1237527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237527 prefixEnd_1237527 := by exact prefixLift 1237527
  have htrace : WordTrace (prefixWord ++ tailWord_1237527) baseStart_1237527 baseEnd_1237527 := by
    simpa [prefixWord, tailWord_1237527, baseEnd_1237527] using wordTrace_append hprefix tailTrace_1237527
  have hstable : (prefixWord ++ tailWord_1237527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237527).length < 2 ^ (prefixWord ++ tailWord_1237527).sum := by decide
  have hdescent : baseEnd_1237527 < baseStart_1237527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237572 : List Nat := [2, 3, 5, 1, 2, 8]
def baseStart_1237572 : Nat := 118140960795 + 1237572 * 2 ^ 59
def prefixEnd_1237572 : Nat := 4983230072969 + 3 ^ 40 * 1237572 * 2
def baseEnd_1237572 : Nat := 10460399679771806214955

theorem tailTrace_1237572 : CollatzResearch.WordTrace tailWord_1237572 prefixEnd_1237572 10460399679771806214955 := by
  unfold tailWord_1237572
  simp only [CollatzResearch.WordTrace]
  refine ⟨22568979536247739657721485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30091972714996986210295313 22568979536247739657721485)
  ·
    refine ⟨8463367326092902371645557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22568979536247739657721485 8463367326092902371645557)
    ·
      refine ⟨793440686821209597341771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8463367326092902371645557 793440686821209597341771)
      ·
        refine ⟨1190161030231814396012657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 793440686821209597341771 1190161030231814396012657)
        ·
          refine ⟨892620772673860797009493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1190161030231814396012657 892620772673860797009493)
          ·
            refine ⟨10460399679771806214955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 892620772673860797009493 10460399679771806214955)
            ·
              rfl

theorem cell21_1237572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 8].length) (baseStart_1237572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237572 prefixEnd_1237572 := by exact prefixLift 1237572
  have htrace : WordTrace (prefixWord ++ tailWord_1237572) baseStart_1237572 baseEnd_1237572 := by
    simpa [prefixWord, tailWord_1237572, baseEnd_1237572] using wordTrace_append hprefix tailTrace_1237572
  have hstable : (prefixWord ++ tailWord_1237572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237572).length < 2 ^ (prefixWord ++ tailWord_1237572).sum := by decide
  have hdescent : baseEnd_1237572 < baseStart_1237572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237634 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 6]
def baseStart_1237634 : Nat := 118140960795 + 1237634 * 2 ^ 59
def prefixEnd_1237634 : Nat := 4983230072969 + 3 ^ 40 * 1237634 * 2
def baseEnd_1237634 : Nat := 282444940598540437770325

theorem tailTrace_1237634 : CollatzResearch.WordTrace tailWord_1237634 prefixEnd_1237634 282444940598540437770325 := by
  unfold tailWord_1237634
  simp only [CollatzResearch.WordTrace]
  refine ⟨11285055099567715976049989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30093480265513909269466637 11285055099567715976049989)
  ·
    refine ⟨2115947831168946745509373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11285055099567715976049989 2115947831168946745509373)
    ·
      refine ⟨793480436688355029566015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2115947831168946745509373 793480436688355029566015)
      ·
        refine ⟨1190220655032532544349023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 793480436688355029566015 1190220655032532544349023)
        ·
          refine ⟨1785330982548798816523535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1190220655032532544349023 1785330982548798816523535)
          ·
            refine ⟨2677996473823198224785303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785330982548798816523535 2677996473823198224785303)
            ·
              refine ⟨4016994710734797337177955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2677996473823198224785303 4016994710734797337177955)
              ·
                refine ⟨6025492066102196005766933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4016994710734797337177955 6025492066102196005766933)
                ·
                  refine ⟨282444940598540437770325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6025492066102196005766933 282444940598540437770325)
                  ·
                    rfl

theorem cell21_1237634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_1237634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237634 prefixEnd_1237634 := by exact prefixLift 1237634
  have htrace : WordTrace (prefixWord ++ tailWord_1237634) baseStart_1237634 baseEnd_1237634 := by
    simpa [prefixWord, tailWord_1237634, baseEnd_1237634] using wordTrace_append hprefix tailTrace_1237634
  have hstable : (prefixWord ++ tailWord_1237634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237634).length < 2 ^ (prefixWord ++ tailWord_1237634).sum := by decide
  have hdescent : baseEnd_1237634 < baseStart_1237634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237704 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 5]
def baseStart_1237704 : Nat := 118140960795 + 1237704 * 2 ^ 59
def prefixEnd_1237704 : Nat := 4983230072969 + 3 ^ 40 * 1237704 * 2
def baseEnd_1237704 : Nat := 282460915552235871603515

theorem tailTrace_1237704 : CollatzResearch.WordTrace tailWord_1237704 prefixEnd_1237704 282460915552235871603515 := by
  unfold tailWord_1237704
  simp only [CollatzResearch.WordTrace]
  refine ⟨22571386754008632929624083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30095182338678177239498777 22571386754008632929624083)
  ·
    refine ⟨33857080131012949394436125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22571386754008632929624083 33857080131012949394436125)
    ·
      refine ⟨12696405049129856022913547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33857080131012949394436125 12696405049129856022913547)
      ·
        refine ⟨19044607573694784034370321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12696405049129856022913547 19044607573694784034370321)
        ·
          refine ⟨14283455680271088025777741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19044607573694784034370321 14283455680271088025777741)
          ·
            refine ⟨5356295880101658009666653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14283455680271088025777741 5356295880101658009666653)
            ·
              refine ⟨2008610955038121753624995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5356295880101658009666653 2008610955038121753624995)
              ·
                refine ⟨3012916432557182630437493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008610955038121753624995 3012916432557182630437493)
                ·
                  refine ⟨282460915552235871603515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3012916432557182630437493 282460915552235871603515)
                  ·
                    rfl

theorem cell21_1237704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_1237704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237704 prefixEnd_1237704 := by exact prefixLift 1237704
  have htrace : WordTrace (prefixWord ++ tailWord_1237704) baseStart_1237704 baseEnd_1237704 := by
    simpa [prefixWord, tailWord_1237704, baseEnd_1237704] using wordTrace_append hprefix tailTrace_1237704
  have hstable : (prefixWord ++ tailWord_1237704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237704).length < 2 ^ (prefixWord ++ tailWord_1237704).sum := by decide
  have hdescent : baseEnd_1237704 < baseStart_1237704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237763 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 5]
def baseStart_1237763 : Nat := 118140960795 + 1237763 * 2 ^ 59
def prefixEnd_1237763 : Nat := 4983230072969 + 3 ^ 40 * 1237763 * 2
def baseEnd_1237763 : Nat := 282474380156064880120061

theorem tailTrace_1237763 : CollatzResearch.WordTrace tailWord_1237763 prefixEnd_1237763 282474380156064880120061 := by
  unfold tailWord_1237763
  simp only [CollatzResearch.WordTrace]
  refine ⟨45144925414803518935645943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30096616943202345957097295 45144925414803518935645943)
  ·
    refine ⟨67717388122205278403468915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45144925414803518935645943 67717388122205278403468915)
    ·
      refine ⟨101576082183307917605203373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67717388122205278403468915 101576082183307917605203373)
      ·
        refine ⟨38091030818740469101951265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101576082183307917605203373 38091030818740469101951265)
        ·
          refine ⟨28568273114055351826463449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38091030818740469101951265 28568273114055351826463449)
          ·
            refine ⟨21426204835541513869847587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28568273114055351826463449 21426204835541513869847587)
            ·
              refine ⟨32139307253312270804771381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21426204835541513869847587 32139307253312270804771381)
              ·
                refine ⟨3013060054998025387947317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32139307253312270804771381 3013060054998025387947317)
                ·
                  refine ⟨282474380156064880120061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3013060054998025387947317 282474380156064880120061)
                  ·
                    rfl

theorem cell21_1237763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 5].length) (baseStart_1237763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237763 prefixEnd_1237763 := by exact prefixLift 1237763
  have htrace : WordTrace (prefixWord ++ tailWord_1237763) baseStart_1237763 baseEnd_1237763 := by
    simpa [prefixWord, tailWord_1237763, baseEnd_1237763] using wordTrace_append hprefix tailTrace_1237763
  have hstable : (prefixWord ++ tailWord_1237763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237763).length < 2 ^ (prefixWord ++ tailWord_1237763).sum := by decide
  have hdescent : baseEnd_1237763 < baseStart_1237763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237797 : List Nat := [1, 3, 1, 2, 3, 1, 4, 3, 3]
def baseStart_1237797 : Nat := 118140960795 + 1237797 * 2 ^ 59
def prefixEnd_1237797 : Nat := 4983230072969 + 3 ^ 40 * 1237797 * 2
def baseEnd_1237797 : Nat := 282482139419288376553325

theorem tailTrace_1237797 : CollatzResearch.WordTrace tailWord_1237797 prefixEnd_1237797 282482139419288376553325 := by
  unfold tailWord_1237797
  simp only [CollatzResearch.WordTrace]
  refine ⟨45146165496680342742383645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30097443664453561828255763 45146165496680342742383645)
  ·
    refine ⟨16929812061255128528393867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45146165496680342742383645 16929812061255128528393867)
    ·
      refine ⟨25394718091882692792590801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16929812061255128528393867 25394718091882692792590801)
      ·
        refine ⟨19046038568912019594443101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25394718091882692792590801 19046038568912019594443101)
        ·
          refine ⟨7142264463342007347916163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19046038568912019594443101 7142264463342007347916163)
          ·
            refine ⟨10713396695013011021874245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7142264463342007347916163 10713396695013011021874245)
            ·
              refine ⟨2008761880314939566601421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10713396695013011021874245 2008761880314939566601421)
              ·
                refine ⟨753285705118102337475533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2008761880314939566601421 753285705118102337475533)
                ·
                  refine ⟨282482139419288376553325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 753285705118102337475533 282482139419288376553325)
                  ·
                    rfl

theorem cell21_1237797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_1237797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237797 prefixEnd_1237797 := by exact prefixLift 1237797
  have htrace : WordTrace (prefixWord ++ tailWord_1237797) baseStart_1237797 baseEnd_1237797 := by
    simpa [prefixWord, tailWord_1237797, baseEnd_1237797] using wordTrace_append hprefix tailTrace_1237797
  have hstable : (prefixWord ++ tailWord_1237797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237797).length < 2 ^ (prefixWord ++ tailWord_1237797).sum := by decide
  have hdescent : baseEnd_1237797 < baseStart_1237797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237811 : List Nat := [1, 1, 1, 2, 6, 1, 3, 2, 4]
def baseStart_1237811 : Nat := 118140960795 + 1237811 * 2 ^ 59
def prefixEnd_1237811 : Nat := 4983230072969 + 3 ^ 40 * 1237811 * 2
def baseEnd_1237811 : Nat := 282485334410027463319963

theorem tailTrace_1237811 : CollatzResearch.WordTrace tailWord_1237811 prefixEnd_1237811 282485334410027463319963 := by
  unfold tailWord_1237811
  simp only [CollatzResearch.WordTrace]
  refine ⟨45146676118629623133393287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30097784079086415422262191 45146676118629623133393287)
  ·
    refine ⟨67720014177944434700089931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45146676118629623133393287 67720014177944434700089931)
    ·
      refine ⟨101580021266916652050134897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67720014177944434700089931 101580021266916652050134897)
      ·
        refine ⟨76185015950187489037601173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101580021266916652050134897 76185015950187489037601173)
        ·
          refine ⟨3571172622665038548637555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76185015950187489037601173 3571172622665038548637555)
          ·
            refine ⟨5356758933997557822956333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571172622665038548637555 5356758933997557822956333)
            ·
              refine ⟨2008784600249084183608625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5356758933997557822956333 2008784600249084183608625)
              ·
                refine ⟨1506588450186813137706469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2008784600249084183608625 1506588450186813137706469)
                ·
                  refine ⟨282485334410027463319963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1506588450186813137706469 282485334410027463319963)
                  ·
                    rfl

theorem cell21_1237811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 4].length) (baseStart_1237811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237811 prefixEnd_1237811 := by exact prefixLift 1237811
  have htrace : WordTrace (prefixWord ++ tailWord_1237811) baseStart_1237811 baseEnd_1237811 := by
    simpa [prefixWord, tailWord_1237811, baseEnd_1237811] using wordTrace_append hprefix tailTrace_1237811
  have hstable : (prefixWord ++ tailWord_1237811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237811).length < 2 ^ (prefixWord ++ tailWord_1237811).sum := by decide
  have hdescent : baseEnd_1237811 < baseStart_1237811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237814 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_1237814 : Nat := 118140960795 + 1237814 * 2 ^ 59
def prefixEnd_1237814 : Nat := 4983230072969 + 3 ^ 40 * 1237814 * 2
def baseEnd_1237814 : Nat := 282486019050900124769957

theorem tailTrace_1237814 : CollatzResearch.WordTrace tailWord_1237814 prefixEnd_1237814 282486019050900124769957 := by
  unfold tailWord_1237814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2821674096101172165359531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30097857025079169763834997 2821674096101172165359531)
  ·
    refine ⟨4232511144151758248039297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2821674096101172165359531 4232511144151758248039297)
    ·
      refine ⟨3174383358113818686029473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4232511144151758248039297 3174383358113818686029473)
      ·
        refine ⟨2380787518585364014522105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3174383358113818686029473 2380787518585364014522105)
        ·
          refine ⟨1785590638939023010891579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2380787518585364014522105 1785590638939023010891579)
          ·
            refine ⟨2678385958408534516337369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785590638939023010891579 2678385958408534516337369)
            ·
              refine ⟨2008789468806400887253027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2678385958408534516337369 2008789468806400887253027)
              ·
                refine ⟨3013184203209601330879541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008789468806400887253027 3013184203209601330879541)
                ·
                  refine ⟨282486019050900124769957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3013184203209601330879541 282486019050900124769957)
                  ·
                    rfl

theorem cell21_1237814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_1237814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237814 prefixEnd_1237814 := by exact prefixLift 1237814
  have htrace : WordTrace (prefixWord ++ tailWord_1237814) baseStart_1237814 baseEnd_1237814 := by
    simpa [prefixWord, tailWord_1237814, baseEnd_1237814] using wordTrace_append hprefix tailTrace_1237814
  have hstable : (prefixWord ++ tailWord_1237814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237814).length < 2 ^ (prefixWord ++ tailWord_1237814).sum := by decide
  have hdescent : baseEnd_1237814 < baseStart_1237814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237887 : List Nat := [1, 1, 2, 2, 1, 1, 8, 1, 4]
def baseStart_1237887 : Nat := 118140960795 + 1237887 * 2 ^ 59
def prefixEnd_1237887 : Nat := 4983230072969 + 3 ^ 40 * 1237887 * 2
def baseEnd_1237887 : Nat := 282502678645468220053141

theorem tailTrace_1237887 : CollatzResearch.WordTrace tailWord_1237887 prefixEnd_1237887 282502678645468220053141 := by
  unfold tailWord_1237887
  simp only [CollatzResearch.WordTrace]
  refine ⟨45149448066354288113159915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30099632044236192075439943 45149448066354288113159915)
  ·
    refine ⟨67724172099531432169739873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45149448066354288113159915 67724172099531432169739873)
    ·
      refine ⟨50793129074648574127304905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67724172099531432169739873 50793129074648574127304905)
      ·
        refine ⟨38094846805986430595478679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50793129074648574127304905 38094846805986430595478679)
        ·
          refine ⟨57142270208979645893218019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38094846805986430595478679 57142270208979645893218019)
          ·
            refine ⟨85713405313469468839827029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57142270208979645893218019 85713405313469468839827029)
            ·
              refine ⟨1004453968517220337966723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 85713405313469468839827029 1004453968517220337966723)
              ·
                refine ⟨1506680952775830506950085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004453968517220337966723 1506680952775830506950085)
                ·
                  refine ⟨282502678645468220053141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1506680952775830506950085 282502678645468220053141)
                  ·
                    rfl

theorem cell21_1237887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 4].length) (baseStart_1237887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237887 prefixEnd_1237887 := by exact prefixLift 1237887
  have htrace : WordTrace (prefixWord ++ tailWord_1237887) baseStart_1237887 baseEnd_1237887 := by
    simpa [prefixWord, tailWord_1237887, baseEnd_1237887] using wordTrace_append hprefix tailTrace_1237887
  have hstable : (prefixWord ++ tailWord_1237887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237887).length < 2 ^ (prefixWord ++ tailWord_1237887).sum := by decide
  have hdescent : baseEnd_1237887 < baseStart_1237887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237932 : List Nat := [2, 2, 1, 1, 1, 1, 2, 8, 3]
def baseStart_1237932 : Nat := 118140960795 + 1237932 * 2 ^ 59
def prefixEnd_1237932 : Nat := 4983230072969 + 3 ^ 40 * 1237932 * 2
def baseEnd_1237932 : Nat := 282512948258558141803049

theorem tailTrace_1237932 : CollatzResearch.WordTrace tailWord_1237932 prefixEnd_1237932 282512948258558141803049 := by
  unfold tailWord_1237932
  simp only [CollatzResearch.WordTrace]
  refine ⟨22575544675595630399274025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30100726234127507199032033 22575544675595630399274025)
  ·
    refine ⟨16931658506696722799455519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22575544675595630399274025 16931658506696722799455519)
    ·
      refine ⟨25397487760045084199183279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16931658506696722799455519 25397487760045084199183279)
      ·
        refine ⟨38096231640067626298774919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25397487760045084199183279 38096231640067626298774919)
        ·
          refine ⟨57144347460101439448162379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38096231640067626298774919 57144347460101439448162379)
          ·
            refine ⟨85716521190152159172243569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57144347460101439448162379 85716521190152159172243569)
            ·
              refine ⟨64287390892614119379182677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85716521190152159172243569 64287390892614119379182677)
              ·
                refine ⟨753367862022821711474797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 64287390892614119379182677 753367862022821711474797)
                ·
                  refine ⟨282512948258558141803049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 753367862022821711474797 282512948258558141803049)
                  ·
                    rfl

theorem cell21_1237932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_1237932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237932 prefixEnd_1237932 := by exact prefixLift 1237932
  have htrace : WordTrace (prefixWord ++ tailWord_1237932) baseStart_1237932 baseEnd_1237932 := by
    simpa [prefixWord, tailWord_1237932, baseEnd_1237932] using wordTrace_append hprefix tailTrace_1237932
  have hstable : (prefixWord ++ tailWord_1237932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237932).length < 2 ^ (prefixWord ++ tailWord_1237932).sum := by decide
  have hdescent : baseEnd_1237932 < baseStart_1237932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237946 : List Nat := [3, 1, 1, 1, 2, 1, 3, 5, 4]
def baseStart_1237946 : Nat := 118140960795 + 1237946 * 2 ^ 59
def prefixEnd_1237946 : Nat := 4983230072969 + 3 ^ 40 * 1237946 * 2
def baseEnd_1237946 : Nat := 282516143249297228569687

theorem tailTrace_1237946 : CollatzResearch.WordTrace tailWord_1237946 prefixEnd_1237946 282516143249297228569687 := by
  unfold tailWord_1237946
  simp only [CollatzResearch.WordTrace]
  refine ⟨11287899993285135297389423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30101066648760360793038461 11287899993285135297389423)
  ·
    refine ⟨16931849989927702946084135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11287899993285135297389423 16931849989927702946084135)
    ·
      refine ⟨25397774984891554419126203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16931849989927702946084135 25397774984891554419126203)
      ·
        refine ⟨38096662477337331628689305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25397774984891554419126203 38096662477337331628689305)
        ·
          refine ⟨28572496858002998721516979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38096662477337331628689305 28572496858002998721516979)
          ·
            refine ⟨42858745287004498082275469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28572496858002998721516979 42858745287004498082275469)
            ·
              refine ⟨16072029482626686780853301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42858745287004498082275469 16072029482626686780853301)
              ·
                refine ⟨1506752763996251885704997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16072029482626686780853301 1506752763996251885704997)
                ·
                  refine ⟨282516143249297228569687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1506752763996251885704997 282516143249297228569687)
                  ·
                    rfl

theorem cell21_1237946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_1237946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1237946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1237946 prefixEnd_1237946 := by exact prefixLift 1237946
  have htrace : WordTrace (prefixWord ++ tailWord_1237946) baseStart_1237946 baseEnd_1237946 := by
    simpa [prefixWord, tailWord_1237946, baseEnd_1237946] using wordTrace_append hprefix tailTrace_1237946
  have hstable : (prefixWord ++ tailWord_1237946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237946).length < 2 ^ (prefixWord ++ tailWord_1237946).sum := by decide
  have hdescent : baseEnd_1237946 < baseStart_1237946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238270 : List Nat := [4, 2, 2, 1, 1, 2, 4, 2, 3]
def baseStart_1238270 : Nat := 118140960795 + 1238270 * 2 ^ 59
def prefixEnd_1238270 : Nat := 4983230072969 + 3 ^ 40 * 1238270 * 2
def baseEnd_1238270 : Nat := 282590084463544665169025

theorem tailTrace_1238270 : CollatzResearch.WordTrace tailWord_1238270 prefixEnd_1238270 282590084463544665169025 := by
  unfold tailWord_1238270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5645427152995843065544033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30108944815977829682901509 5645427152995843065544033)
  ·
    refine ⟨4234070364746882299158025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5645427152995843065544033 4234070364746882299158025)
    ·
      refine ⟨3175552773560161724368519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4234070364746882299158025 3175552773560161724368519)
      ·
        refine ⟨4763329160340242586552779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3175552773560161724368519 4763329160340242586552779)
        ·
          refine ⟨7144993740510363879829169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4763329160340242586552779 7144993740510363879829169)
          ·
            refine ⟨5358745305382772909871877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7144993740510363879829169 5358745305382772909871877)
            ·
              refine ⟨1004764744759269920600977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5358745305382772909871877 1004764744759269920600977)
              ·
                refine ⟨753573558569452440450733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1004764744759269920600977 753573558569452440450733)
                ·
                  refine ⟨282590084463544665169025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 753573558569452440450733 282590084463544665169025)
                  ·
                    rfl

theorem cell21_1238270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_1238270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1238270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1238270 prefixEnd_1238270 := by exact prefixLift 1238270
  have htrace : WordTrace (prefixWord ++ tailWord_1238270) baseStart_1238270 baseEnd_1238270 := by
    simpa [prefixWord, tailWord_1238270, baseEnd_1238270] using wordTrace_append hprefix tailTrace_1238270
  have hstable : (prefixWord ++ tailWord_1238270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238270).length < 2 ^ (prefixWord ++ tailWord_1238270).sum := by decide
  have hdescent : baseEnd_1238270 < baseStart_1238270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238295 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 5]
def baseStart_1238295 : Nat := 118140960795 + 1238295 * 2 ^ 59
def prefixEnd_1238295 : Nat := 4983230072969 + 3 ^ 40 * 1238295 * 2
def baseEnd_1238295 : Nat := 282595789804150177252307

theorem tailTrace_1238295 : CollatzResearch.WordTrace tailWord_1238295 prefixEnd_1238295 282595789804150177252307 := by
  unfold tailWord_1238295
  simp only [CollatzResearch.WordTrace]
  refine ⟨45164329048876173794012339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30109552699250782529341559 45164329048876173794012339)
  ·
    refine ⟨67746493573314260691018509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45164329048876173794012339 67746493573314260691018509)
    ·
      refine ⟨25404935089992847759131941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67746493573314260691018509 25404935089992847759131941)
      ·
        refine ⟨4763425329373658954837239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25404935089992847759131941 4763425329373658954837239)
        ·
          refine ⟨7145137994060488432255859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4763425329373658954837239 7145137994060488432255859)
          ·
            refine ⟨10717706991090732648383789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7145137994060488432255859 10717706991090732648383789)
            ·
              refine ⟨4019140121659024743143921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10717706991090732648383789 4019140121659024743143921)
              ·
                refine ⟨3014355091244268557357941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4019140121659024743143921 3014355091244268557357941)
                ·
                  refine ⟨282595789804150177252307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3014355091244268557357941 282595789804150177252307)
                  ·
                    rfl

theorem cell21_1238295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 5].length) (baseStart_1238295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1238295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1238295 prefixEnd_1238295 := by exact prefixLift 1238295
  have htrace : WordTrace (prefixWord ++ tailWord_1238295) baseStart_1238295 baseEnd_1238295 := by
    simpa [prefixWord, tailWord_1238295, baseEnd_1238295] using wordTrace_append hprefix tailTrace_1238295
  have hstable : (prefixWord ++ tailWord_1238295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238295).length < 2 ^ (prefixWord ++ tailWord_1238295).sum := by decide
  have hdescent : baseEnd_1238295 < baseStart_1238295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238343 : List Nat := [1, 1, 4, 1, 2, 4, 3, 1, 4]
def baseStart_1238343 : Nat := 118140960795 + 1238343 * 2 ^ 59
def prefixEnd_1238343 : Nat := 4983230072969 + 3 ^ 40 * 1238343 * 2
def baseEnd_1238343 : Nat := 282606744058112760452209

theorem tailTrace_1238343 : CollatzResearch.WordTrace tailWord_1238343 prefixEnd_1238343 282606744058112760452209 := by
  unfold tailWord_1238343
  simp only [CollatzResearch.WordTrace]
  refine ⟨45166079752702277991759683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30110719835134851994506455 45166079752702277991759683)
  ·
    refine ⟨67749119629053416987639525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45166079752702277991759683 67749119629053416987639525)
    ·
      refine ⟨12702959930447515685182411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67749119629053416987639525 12702959930447515685182411)
      ·
        refine ⟨19054439895671273527773617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12702959930447515685182411 19054439895671273527773617)
        ·
          refine ⟨14290829921753455145830213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19054439895671273527773617 14290829921753455145830213)
          ·
            refine ⟨2679530610328772839843165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14290829921753455145830213 2679530610328772839843165)
            ·
              refine ⟨1004823978873289814941187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2679530610328772839843165 1004823978873289814941187)
              ·
                refine ⟨1507235968309934722411781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004823978873289814941187 1507235968309934722411781)
                ·
                  refine ⟨282606744058112760452209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1507235968309934722411781 282606744058112760452209)
                  ·
                    rfl

theorem cell21_1238343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 4].length) (baseStart_1238343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1238343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1238343 prefixEnd_1238343 := by exact prefixLift 1238343
  have htrace : WordTrace (prefixWord ++ tailWord_1238343) baseStart_1238343 baseEnd_1238343 := by
    simpa [prefixWord, tailWord_1238343, baseEnd_1238343] using wordTrace_append hprefix tailTrace_1238343
  have hstable : (prefixWord ++ tailWord_1238343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238343).length < 2 ^ (prefixWord ++ tailWord_1238343).sum := by decide
  have hdescent : baseEnd_1238343 < baseStart_1238343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238357 : List Nat := [1, 3, 2, 2, 3, 1, 4, 5]
def baseStart_1238357 : Nat := 118140960795 + 1238357 * 2 ^ 59
def prefixEnd_1238357 : Nat := 4983230072969 + 3 ^ 40 * 1238357 * 2
def baseEnd_1238357 : Nat := 94203313016283949072949

theorem tailTrace_1238357 : CollatzResearch.WordTrace tailWord_1238357 prefixEnd_1238357 94203313016283949072949 := by
  unfold tailWord_1238357
  simp only [CollatzResearch.WordTrace]
  refine ⟨45166590374651558382769325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30111060249767705588512883 45166590374651558382769325)
  ·
    refine ⟨16937471390494334393538497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45166590374651558382769325 16937471390494334393538497)
    ·
      refine ⟨12703103542870750795153873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16937471390494334393538497 12703103542870750795153873)
      ·
        refine ⟨9527327657153063096365405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12703103542870750795153873 9527327657153063096365405)
        ·
          refine ⟨3572747871432398661137027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9527327657153063096365405 3572747871432398661137027)
          ·
            refine ⟨5359121807148597991705541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3572747871432398661137027 5359121807148597991705541)
            ·
              refine ⟨1004835338840362123444789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5359121807148597991705541 1004835338840362123444789)
              ·
                refine ⟨94203313016283949072949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1004835338840362123444789 94203313016283949072949)
                ·
                  rfl

theorem cell21_1238357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 5].length) (baseStart_1238357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1238357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1238357 prefixEnd_1238357 := by exact prefixLift 1238357
  have htrace : WordTrace (prefixWord ++ tailWord_1238357) baseStart_1238357 baseEnd_1238357 := by
    simpa [prefixWord, tailWord_1238357, baseEnd_1238357] using wordTrace_append hprefix tailTrace_1238357
  have hstable : (prefixWord ++ tailWord_1238357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238357).length < 2 ^ (prefixWord ++ tailWord_1238357).sum := by decide
  have hdescent : baseEnd_1238357 < baseStart_1238357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238385 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 6]
def baseStart_1238385 : Nat := 118140960795 + 1238385 * 2 ^ 59
def prefixEnd_1238385 : Nat := 4983230072969 + 3 ^ 40 * 1238385 * 2
def baseEnd_1238385 : Nat := 282616329030330020752123

theorem tailTrace_1238385 : CollatzResearch.WordTrace tailWord_1238385 prefixEnd_1238385 282616329030330020752123 := by
  unfold tailWord_1238385
  simp only [CollatzResearch.WordTrace]
  refine ⟨45167611618550119164788609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30111741079033412776525739 45167611618550119164788609)
  ·
    refine ⟨33875708713912589373591457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45167611618550119164788609 33875708713912589373591457)
    ·
      refine ⟨25406781535434442030193593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33875708713912589373591457 25406781535434442030193593)
      ·
        refine ⟨19055086151575831522645195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25406781535434442030193593 19055086151575831522645195)
        ·
          refine ⟨28582629227363747283967793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19055086151575831522645195 28582629227363747283967793)
          ·
            refine ⟨21436971920522810462975845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28582629227363747283967793 21436971920522810462975845)
            ·
              refine ⟨4019432235098026961807971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21436971920522810462975845 4019432235098026961807971)
              ·
                refine ⟨6029148352647040442711957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4019432235098026961807971 6029148352647040442711957)
                ·
                  refine ⟨282616329030330020752123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6029148352647040442711957 282616329030330020752123)
                  ·
                    rfl

theorem cell21_1238385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_1238385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1238385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1238385 prefixEnd_1238385 := by exact prefixLift 1238385
  have htrace : WordTrace (prefixWord ++ tailWord_1238385) baseStart_1238385 baseEnd_1238385 := by
    simpa [prefixWord, tailWord_1238385, baseEnd_1238385] using wordTrace_append hprefix tailTrace_1238385
  have hstable : (prefixWord ++ tailWord_1238385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238385).length < 2 ^ (prefixWord ++ tailWord_1238385).sum := by decide
  have hdescent : baseEnd_1238385 < baseStart_1238385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238475 : List Nat := [1, 1, 1, 1, 3, 3, 2, 9]
def baseStart_1238475 : Nat := 118140960795 + 1238475 * 2 ^ 59
def prefixEnd_1238475 : Nat := 4983230072969 + 3 ^ 40 * 1238475 * 2
def baseEnd_1238475 : Nat := 94212289418836621417313

theorem tailTrace_1238475 : CollatzResearch.WordTrace tailWord_1238475 prefixEnd_1238475 94212289418836621417313 := by
  unfold tailWord_1238475
  simp only [CollatzResearch.WordTrace]
  refine ⟨45170894188224064535564879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30113929458816043023709919 45170894188224064535564879)
  ·
    refine ⟨67756341282336096803347319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45170894188224064535564879 67756341282336096803347319)
    ·
      refine ⟨101634511923504145205020979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67756341282336096803347319 101634511923504145205020979)
      ·
        refine ⟨152451767885256217807531469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101634511923504145205020979 152451767885256217807531469)
        ·
          refine ⟨57169412956971081677824301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152451767885256217807531469 57169412956971081677824301)
          ·
            refine ⟨21438529858864155629184113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57169412956971081677824301 21438529858864155629184113)
            ·
              refine ⟨16078897394148116721888085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21438529858864155629184113 16078897394148116721888085)
              ·
                refine ⟨94212289418836621417313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16078897394148116721888085 94212289418836621417313)
                ·
                  rfl

theorem cell21_1238475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 9].length) (baseStart_1238475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1238475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1238475 prefixEnd_1238475 := by exact prefixLift 1238475
  have htrace : WordTrace (prefixWord ++ tailWord_1238475) baseStart_1238475 baseEnd_1238475 := by
    simpa [prefixWord, tailWord_1238475, baseEnd_1238475] using wordTrace_append hprefix tailTrace_1238475
  have hstable : (prefixWord ++ tailWord_1238475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238475).length < 2 ^ (prefixWord ++ tailWord_1238475).sum := by decide
  have hdescent : baseEnd_1238475 < baseStart_1238475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
