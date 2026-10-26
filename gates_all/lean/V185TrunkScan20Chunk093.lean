import V185TrunkScan20Chunk092

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_565761 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 4]
def baseStart_565761 : Nat := 118140960795 + 565761 * 2 ^ 59
def prefixEnd_565761 : Nat := 4983230072969 + 3 ^ 40 * 565761 * 2
def baseEnd_565761 : Nat := 258228736505303281053883

theorem tailTrace_565761 : CollatzResearch.WordTrace tailWord_565761 prefixEnd_565761 258228736505303281053883 := by
  unfold tailWord_565761
  simp only [CollatzResearch.WordTrace]
  refine ⟨20634998903351996131257137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13756665935567997420838091 20634998903351996131257137)
  ·
    refine ⟨15476249177513997098442853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20634998903351996131257137 15476249177513997098442853)
    ·
      refine ⟨2901796720783874455958035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15476249177513997098442853 2901796720783874455958035)
      ·
        refine ⟨4352695081175811683937053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2901796720783874455958035 4352695081175811683937053)
        ·
          refine ⟨1632260655440929381476395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4352695081175811683937053 1632260655440929381476395)
          ·
            refine ⟨2448390983161394072214593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632260655440929381476395 2448390983161394072214593)
            ·
              refine ⟨1836293237371045554160945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2448390983161394072214593 1836293237371045554160945)
              ·
                refine ⟨1377219928028284165620709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1836293237371045554160945 1377219928028284165620709)
                ·
                  refine ⟨258228736505303281053883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1377219928028284165620709 258228736505303281053883)
                  ·
                    rfl

theorem cell20_565761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_565761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565761 prefixEnd_565761 := by exact prefixLift 565761
  have htrace : WordTrace (prefixWord ++ tailWord_565761) baseStart_565761 baseEnd_565761 := by
    simpa [prefixWord, tailWord_565761, baseEnd_565761] using wordTrace_append hprefix tailTrace_565761
  have hstable : (prefixWord ++ tailWord_565761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565761).length < 2 ^ (prefixWord ++ tailWord_565761).sum := by decide
  have hdescent : baseEnd_565761 < baseStart_565761 := by decide
  rcases family_descends (prefixWord ++ tailWord_565761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565764 : List Nat := [2, 3, 2, 3, 1, 3, 2, 4]
def baseStart_565764 : Nat := 118140960795 + 565764 * 2 ^ 59
def prefixEnd_565764 : Nat := 4983230072969 + 3 ^ 40 * 565764 * 2
def baseEnd_565764 : Nat := 86076701929016201317957

theorem tailTrace_565764 : CollatzResearch.WordTrace tailWord_565764 prefixEnd_565764 86076701929016201317957 := by
  unfold tailWord_565764
  simp only [CollatzResearch.WordTrace]
  refine ⟨10317554161170563821808173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13756738881560751762410897 10317554161170563821808173)
  ·
    refine ⟨3869082810438961433178065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10317554161170563821808173 3869082810438961433178065)
    ·
      refine ⟨2901812107829221074883549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3869082810438961433178065 2901812107829221074883549)
      ·
        refine ⟨1088179540435957903081331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2901812107829221074883549 1088179540435957903081331)
        ·
          refine ⟨1632269310653936854621997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088179540435957903081331 1632269310653936854621997)
          ·
            refine ⟨612100991495226320483249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1632269310653936854621997 612100991495226320483249)
            ·
              refine ⟨459075743621419740362437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612100991495226320483249 459075743621419740362437)
              ·
                refine ⟨86076701929016201317957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 459075743621419740362437 86076701929016201317957)
                ·
                  rfl

theorem cell20_565764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_565764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565764 prefixEnd_565764 := by exact prefixLift 565764
  have htrace : WordTrace (prefixWord ++ tailWord_565764) baseStart_565764 baseEnd_565764 := by
    simpa [prefixWord, tailWord_565764, baseEnd_565764] using wordTrace_append hprefix tailTrace_565764
  have hstable : (prefixWord ++ tailWord_565764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565764).length < 2 ^ (prefixWord ++ tailWord_565764).sum := by decide
  have hdescent : baseEnd_565764 < baseStart_565764 := by decide
  rcases family_descends (prefixWord ++ tailWord_565764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565795 : List Nat := [1, 1, 1, 4, 4, 2, 3, 2, 2]
def baseStart_565795 : Nat := 118140960795 + 565795 * 2 ^ 59
def prefixEnd_565795 : Nat := 4983230072969 + 3 ^ 40 * 565795 * 2
def baseEnd_565795 : Nat := 258244255031750273920411

theorem tailTrace_565795 : CollatzResearch.WordTrace tailWord_565795 prefixEnd_565795 258244255031750273920411 := by
  unfold tailWord_565795
  simp only [CollatzResearch.WordTrace]
  refine ⟨20636238985228819937994839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13757492656819213291996559 20636238985228819937994839)
  ·
    refine ⟨30954358477843229906992259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20636238985228819937994839 30954358477843229906992259)
    ·
      refine ⟨46431537716764844860488389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30954358477843229906992259 46431537716764844860488389)
      ·
        refine ⟨8705913321893408411341573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46431537716764844860488389 8705913321893408411341573)
        ·
          refine ⟨1632358747855014077126545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8705913321893408411341573 1632358747855014077126545)
          ·
            refine ⟨1224269060891260557844909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1632358747855014077126545 1224269060891260557844909)
            ·
              refine ⟨459100897834222709191841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1224269060891260557844909 459100897834222709191841)
              ·
                refine ⟨344325673375667031893881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459100897834222709191841 344325673375667031893881)
                ·
                  refine ⟨258244255031750273920411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344325673375667031893881 258244255031750273920411)
                  ·
                    rfl

theorem cell20_565795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 2].length) (baseStart_565795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565795 prefixEnd_565795 := by exact prefixLift 565795
  have htrace : WordTrace (prefixWord ++ tailWord_565795) baseStart_565795 baseEnd_565795 := by
    simpa [prefixWord, tailWord_565795, baseEnd_565795] using wordTrace_append hprefix tailTrace_565795
  have hstable : (prefixWord ++ tailWord_565795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565795).length < 2 ^ (prefixWord ++ tailWord_565795).sum := by decide
  have hdescent : baseEnd_565795 < baseStart_565795 := by decide
  rcases family_descends (prefixWord ++ tailWord_565795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565805 : List Nat := [1, 5, 4, 1, 1, 1, 1, 3, 3]
def baseStart_565805 : Nat := 118140960795 + 565805 * 2 ^ 59
def prefixEnd_565805 : Nat := 4983230072969 + 3 ^ 40 * 565805 * 2
def baseEnd_565805 : Nat := 258248819304234683587037

theorem tailTrace_565805 : CollatzResearch.WordTrace tailWord_565805 prefixEnd_565805 258248819304234683587037 := by
  unfold tailWord_565805
  simp only [CollatzResearch.WordTrace]
  refine ⟨20636603715192591645858869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13757735810128394430572579 20636603715192591645858869)
  ·
    refine ⟨1934681598299305466799269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20636603715192591645858869 1934681598299305466799269)
    ·
      refine ⟨362752799681119775024863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1934681598299305466799269 362752799681119775024863)
      ·
        refine ⟨544129199521679662537295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362752799681119775024863 544129199521679662537295)
        ·
          refine ⟨816193799282519493805943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544129199521679662537295 816193799282519493805943)
          ·
            refine ⟨1224290698923779240708915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816193799282519493805943 1224290698923779240708915)
            ·
              refine ⟨1836436048385668861063373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224290698923779240708915 1836436048385668861063373)
              ·
                refine ⟨688663518144625822898765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1836436048385668861063373 688663518144625822898765)
                ·
                  refine ⟨258248819304234683587037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 688663518144625822898765 258248819304234683587037)
                  ·
                    rfl

theorem cell20_565805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_565805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565805 prefixEnd_565805 := by exact prefixLift 565805
  have htrace : WordTrace (prefixWord ++ tailWord_565805) baseStart_565805 baseEnd_565805 := by
    simpa [prefixWord, tailWord_565805, baseEnd_565805] using wordTrace_append hprefix tailTrace_565805
  have hstable : (prefixWord ++ tailWord_565805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565805).length < 2 ^ (prefixWord ++ tailWord_565805).sum := by decide
  have hdescent : baseEnd_565805 < baseStart_565805 := by decide
  rcases family_descends (prefixWord ++ tailWord_565805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565861 : List Nat := [1, 3, 1, 3, 4, 2, 1, 5]
def baseStart_565861 : Nat := 118140960795 + 565861 * 2 ^ 59
def prefixEnd_565861 : Nat := 4983230072969 + 3 ^ 40 * 565861 * 2
def baseEnd_565861 : Nat := 86091459743382459240047

theorem tailTrace_565861 : CollatzResearch.WordTrace tailWord_565861 prefixEnd_565861 86091459743382459240047 := by
  unfold tailWord_565861
  simp only [CollatzResearch.WordTrace]
  refine ⟨20638646202989713209897437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13759097468659808806598291 20638646202989713209897437)
  ·
    refine ⟨7739492326121142453711539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20638646202989713209897437 7739492326121142453711539)
    ·
      refine ⟨11609238489181713680567309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7739492326121142453711539 11609238489181713680567309)
      ·
        refine ⟨4353464433443142630212741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11609238489181713680567309 4353464433443142630212741)
        ·
          refine ⟨816274581270589243164889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4353464433443142630212741 816274581270589243164889)
          ·
            refine ⟨612205935952941932373667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 816274581270589243164889 612205935952941932373667)
            ·
              refine ⟨918308903929412898560501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612205935952941932373667 918308903929412898560501)
              ·
                refine ⟨86091459743382459240047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 918308903929412898560501 86091459743382459240047)
                ·
                  rfl

theorem cell20_565861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 5].length) (baseStart_565861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565861 prefixEnd_565861 := by exact prefixLift 565861
  have htrace : WordTrace (prefixWord ++ tailWord_565861) baseStart_565861 baseEnd_565861 := by
    simpa [prefixWord, tailWord_565861, baseEnd_565861] using wordTrace_append hprefix tailTrace_565861
  have hstable : (prefixWord ++ tailWord_565861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565861).length < 2 ^ (prefixWord ++ tailWord_565861).sum := by decide
  have hdescent : baseEnd_565861 < baseStart_565861 := by decide
  rcases family_descends (prefixWord ++ tailWord_565861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565878 : List Nat := [5, 1, 1, 2, 3, 1, 3, 4]
def baseStart_565878 : Nat := 118140960795 + 565878 * 2 ^ 59
def prefixEnd_565878 : Nat := 4983230072969 + 3 ^ 40 * 565878 * 2
def baseEnd_565878 : Nat := 86094046164456958051135

theorem tailTrace_565878 : CollatzResearch.WordTrace tailWord_565878 prefixEnd_565878 86094046164456958051135 := by
  unfold tailWord_565878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289954140245507819579143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13759510829285416742177525 1289954140245507819579143)
  ·
    refine ⟨1934931210368261729368715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1289954140245507819579143 1934931210368261729368715)
    ·
      refine ⟨2902396815552392594053073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1934931210368261729368715 2902396815552392594053073)
      ·
        refine ⟨2176797611664294445539805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2902396815552392594053073 2176797611664294445539805)
        ·
          refine ⟨816299104374110417077427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2176797611664294445539805 816299104374110417077427)
          ·
            refine ⟨1224448656561165625616141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816299104374110417077427 1224448656561165625616141)
            ·
              refine ⟨459168246210437109606053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1224448656561165625616141 459168246210437109606053)
              ·
                refine ⟨86094046164456958051135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 459168246210437109606053 86094046164456958051135)
                ·
                  rfl

theorem cell20_565878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_565878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565878 prefixEnd_565878 := by exact prefixLift 565878
  have htrace : WordTrace (prefixWord ++ tailWord_565878) baseStart_565878 baseEnd_565878 := by
    simpa [prefixWord, tailWord_565878, baseEnd_565878] using wordTrace_append hprefix tailTrace_565878
  have hstable : (prefixWord ++ tailWord_565878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565878).length < 2 ^ (prefixWord ++ tailWord_565878).sum := by decide
  have hdescent : baseEnd_565878 < baseStart_565878 := by decide
  rcases family_descends (prefixWord ++ tailWord_565878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565889 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 5]
def baseStart_565889 : Nat := 118140960795 + 565889 * 2 ^ 59
def prefixEnd_565889 : Nat := 4983230072969 + 3 ^ 40 * 565889 * 2
def baseEnd_565889 : Nat := 258287159193103724786693

theorem tailTrace_565889 : CollatzResearch.WordTrace tailWord_565889 prefixEnd_565889 258287159193103724786693 := by
  unfold tailWord_565889
  simp only [CollatzResearch.WordTrace]
  refine ⟨20639667446888273991916721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13759778297925515994611147 20639667446888273991916721)
  ·
    refine ⟨15479750585166205493937541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20639667446888273991916721 15479750585166205493937541)
    ·
      refine ⟨2902453234718663530113289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15479750585166205493937541 2902453234718663530113289)
      ·
        refine ⟨2176839926038997647584967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2902453234718663530113289 2176839926038997647584967)
        ·
          refine ⟨3265259889058496471377451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2176839926038997647584967 3265259889058496471377451)
          ·
            refine ⟨4897889833587744707066177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3265259889058496471377451 4897889833587744707066177)
            ·
              refine ⟨3673417375190808530299633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4897889833587744707066177 3673417375190808530299633)
              ·
                refine ⟨2755063031393106397724725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3673417375190808530299633 2755063031393106397724725)
                ·
                  refine ⟨258287159193103724786693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2755063031393106397724725 258287159193103724786693)
                  ·
                    rfl

theorem cell20_565889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_565889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565889 prefixEnd_565889 := by exact prefixLift 565889
  have htrace : WordTrace (prefixWord ++ tailWord_565889) baseStart_565889 baseEnd_565889 := by
    simpa [prefixWord, tailWord_565889, baseEnd_565889] using wordTrace_append hprefix tailTrace_565889
  have hstable : (prefixWord ++ tailWord_565889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565889).length < 2 ^ (prefixWord ++ tailWord_565889).sum := by decide
  have hdescent : baseEnd_565889 < baseStart_565889 := by decide
  rcases family_descends (prefixWord ++ tailWord_565889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565892 : List Nat := [2, 3, 2, 1, 3, 1, 1, 5, 2]
def baseStart_565892 : Nat := 118140960795 + 565892 * 2 ^ 59
def prefixEnd_565892 : Nat := 4983230072969 + 3 ^ 40 * 565892 * 2
def baseEnd_565892 : Nat := 258288528474849047686681

theorem tailTrace_565892 : CollatzResearch.WordTrace tailWord_565892 prefixEnd_565892 258288528474849047686681 := by
  unfold tailWord_565892
  simp only [CollatzResearch.WordTrace]
  refine ⟨10319888432938702752137965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13759851243918270336183953 10319888432938702752137965)
  ·
    refine ⟨3869958162352013532051737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10319888432938702752137965 3869958162352013532051737)
    ·
      refine ⟨2902468621764010149038803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3869958162352013532051737 2902468621764010149038803)
      ·
        refine ⟨4353702932646015223558205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2902468621764010149038803 4353702932646015223558205)
        ·
          refine ⟨1632638599742255708834327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4353702932646015223558205 1632638599742255708834327)
          ·
            refine ⟨2448957899613383563251491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632638599742255708834327 2448957899613383563251491)
            ·
              refine ⟨3673436849420075344877237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2448957899613383563251491 3673436849420075344877237)
              ·
                refine ⟨344384704633132063582241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3673436849420075344877237 344384704633132063582241)
                ·
                  refine ⟨258288528474849047686681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344384704633132063582241 258288528474849047686681)
                  ·
                    rfl

theorem cell20_565892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_565892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565892 prefixEnd_565892 := by exact prefixLift 565892
  have htrace : WordTrace (prefixWord ++ tailWord_565892) baseStart_565892 baseEnd_565892 := by
    simpa [prefixWord, tailWord_565892, baseEnd_565892] using wordTrace_append hprefix tailTrace_565892
  have hstable : (prefixWord ++ tailWord_565892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565892).length < 2 ^ (prefixWord ++ tailWord_565892).sum := by decide
  have hdescent : baseEnd_565892 < baseStart_565892 := by decide
  rcases family_descends (prefixWord ++ tailWord_565892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565906 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_565906 : Nat := 118140960795 + 565906 * 2 ^ 59
def prefixEnd_565906 : Nat := 4983230072969 + 3 ^ 40 * 565906 * 2
def baseEnd_565906 : Nat := 258294918456327221219957

theorem tailTrace_565906 : CollatzResearch.WordTrace tailWord_565906 prefixEnd_565906 258294918456327221219957 := by
  unfold tailWord_565906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5160071871956671473821393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13760191658551123930190381 5160071871956671473821393)
  ·
    refine ⟨3870053903967503605366045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5160071871956671473821393 3870053903967503605366045)
    ·
      refine ⟨1451270213987813852012267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3870053903967503605366045 1451270213987813852012267)
      ·
        refine ⟨2176905320981720778018401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1451270213987813852012267 2176905320981720778018401)
        ·
          refine ⟨1632678990736290583513801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2176905320981720778018401 1632678990736290583513801)
          ·
            refine ⟨1224509243052217937635351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1632678990736290583513801 1224509243052217937635351)
            ·
              refine ⟨1836763864578326906453027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224509243052217937635351 1836763864578326906453027)
              ·
                refine ⟨2755145796867490359679541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1836763864578326906453027 2755145796867490359679541)
                ·
                  refine ⟨258294918456327221219957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2755145796867490359679541 258294918456327221219957)
                  ·
                    rfl

theorem cell20_565906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_565906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565906 prefixEnd_565906 := by exact prefixLift 565906
  have htrace : WordTrace (prefixWord ++ tailWord_565906) baseStart_565906 baseEnd_565906 := by
    simpa [prefixWord, tailWord_565906, baseEnd_565906] using wordTrace_append hprefix tailTrace_565906
  have hstable : (prefixWord ++ tailWord_565906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565906).length < 2 ^ (prefixWord ++ tailWord_565906).sum := by decide
  have hdescent : baseEnd_565906 < baseStart_565906 := by decide
  rcases family_descends (prefixWord ++ tailWord_565906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565913 : List Nat := [1, 2, 1, 2, 1, 2, 3, 6, 2]
def baseStart_565913 : Nat := 118140960795 + 565913 * 2 ^ 59
def prefixEnd_565913 : Nat := 4983230072969 + 3 ^ 40 * 565913 * 2
def baseEnd_565913 : Nat := 258298113447066307986595

theorem tailTrace_565913 : CollatzResearch.WordTrace tailWord_565913 prefixEnd_565913 258298113447066307986595 := by
  unfold tailWord_565913
  simp only [CollatzResearch.WordTrace]
  refine ⟨20640542798801326090790393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13760361865867550727193595 20640542798801326090790393)
  ·
    refine ⟨15480407099100994568092795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20640542798801326090790393 15480407099100994568092795)
    ·
      refine ⟨23220610648651491852139193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15480407099100994568092795 23220610648651491852139193)
      ·
        refine ⟨17415457986488618889104395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23220610648651491852139193 17415457986488618889104395)
        ·
          refine ⟨26123186979732928333656593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17415457986488618889104395 26123186979732928333656593)
          ·
            refine ⟨19592390234799696250242445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26123186979732928333656593 19592390234799696250242445)
            ·
              refine ⟨7347146338049886093840917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19592390234799696250242445 7347146338049886093840917)
              ·
                refine ⟨344397484596088410648793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7347146338049886093840917 344397484596088410648793)
                ·
                  refine ⟨258298113447066307986595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344397484596088410648793 258298113447066307986595)
                  ·
                    rfl

theorem cell20_565913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 2].length) (baseStart_565913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565913 prefixEnd_565913 := by exact prefixLift 565913
  have htrace : WordTrace (prefixWord ++ tailWord_565913) baseStart_565913 baseEnd_565913 := by
    simpa [prefixWord, tailWord_565913, baseEnd_565913] using wordTrace_append hprefix tailTrace_565913
  have hstable : (prefixWord ++ tailWord_565913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565913).length < 2 ^ (prefixWord ++ tailWord_565913).sum := by decide
  have hdescent : baseEnd_565913 < baseStart_565913 := by decide
  rcases family_descends (prefixWord ++ tailWord_565913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565937 : List Nat := [1, 2, 2, 6, 1, 1, 1, 6]
def baseStart_565937 : Nat := 118140960795 + 565937 * 2 ^ 59
def prefixEnd_565937 : Nat := 4983230072969 + 3 ^ 40 * 565937 * 2
def baseEnd_565937 : Nat := 86103022567009630395499

theorem tailTrace_565937 : CollatzResearch.WordTrace tailWord_565937 prefixEnd_565937 86103022567009630395499 := by
  unfold tailWord_565937
  simp only [CollatzResearch.WordTrace]
  refine ⟨20641418150714378189664065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13760945433809585459776043 20641418150714378189664065)
  ·
    refine ⟨15481063613035783642248049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20641418150714378189664065 15481063613035783642248049)
    ·
      refine ⟨11610797709776837731686037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15481063613035783642248049 11610797709776837731686037)
      ·
        refine ⟨544256142645789268672783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11610797709776837731686037 544256142645789268672783)
        ·
          refine ⟨816384213968683903009175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544256142645789268672783 816384213968683903009175)
          ·
            refine ⟨1224576320953025854513763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816384213968683903009175 1224576320953025854513763)
            ·
              refine ⟨1836864481429538781770645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224576320953025854513763 1836864481429538781770645)
              ·
                refine ⟨86103022567009630395499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1836864481429538781770645 86103022567009630395499)
                ·
                  rfl

theorem cell20_565937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 6].length) (baseStart_565937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565937 prefixEnd_565937 := by exact prefixLift 565937
  have htrace : WordTrace (prefixWord ++ tailWord_565937) baseStart_565937 baseEnd_565937 := by
    simpa [prefixWord, tailWord_565937, baseEnd_565937] using wordTrace_append hprefix tailTrace_565937
  have hstable : (prefixWord ++ tailWord_565937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565937).length < 2 ^ (prefixWord ++ tailWord_565937).sum := by decide
  have hdescent : baseEnd_565937 < baseStart_565937 := by decide
  rcases family_descends (prefixWord ++ tailWord_565937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566006 : List Nat := [5, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_566006 : Nat := 118140960795 + 566006 * 2 ^ 59
def prefixEnd_566006 : Nat := 4983230072969 + 3 ^ 40 * 566006 * 2
def baseEnd_566006 : Nat := 258340561181171317886215

theorem tailTrace_566006 : CollatzResearch.WordTrace tailWord_566006 prefixEnd_566006 258340561181171317886215 := by
  unfold tailWord_566006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290245924216525185870367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13762623191642935315950581 1290245924216525185870367)
  ·
    refine ⟨1935368886324787778805551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1290245924216525185870367 1935368886324787778805551)
    ·
      refine ⟨2903053329487181668208327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1935368886324787778805551 2903053329487181668208327)
      ·
        refine ⟨4354579994230772502312491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2903053329487181668208327 4354579994230772502312491)
        ·
          refine ⟨6531869991346158753468737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4354579994230772502312491 6531869991346158753468737)
          ·
            refine ⟨4898902493509619065101553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6531869991346158753468737 4898902493509619065101553)
            ·
              refine ⟨3674176870132214298826165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4898902493509619065101553 3674176870132214298826165)
              ·
                refine ⟨344454081574895090514953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3674176870132214298826165 344454081574895090514953)
                ·
                  refine ⟨258340561181171317886215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344454081574895090514953 258340561181171317886215)
                  ·
                    rfl

theorem cell20_566006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_566006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566006 prefixEnd_566006 := by exact prefixLift 566006
  have htrace : WordTrace (prefixWord ++ tailWord_566006) baseStart_566006 baseEnd_566006 := by
    simpa [prefixWord, tailWord_566006, baseEnd_566006] using wordTrace_append hprefix tailTrace_566006
  have hstable : (prefixWord ++ tailWord_566006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566006).length < 2 ^ (prefixWord ++ tailWord_566006).sum := by decide
  have hdescent : baseEnd_566006 < baseStart_566006 := by decide
  rcases family_descends (prefixWord ++ tailWord_566006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566020 : List Nat := [2, 3, 2, 2, 1, 1, 4, 2, 3]
def baseStart_566020 : Nat := 118140960795 + 566020 * 2 ^ 59
def prefixEnd_566020 : Nat := 4983230072969 + 3 ^ 40 * 566020 * 2
def baseEnd_566020 : Nat := 258346951162649491419491

theorem tailTrace_566020 : CollatzResearch.WordTrace tailWord_566020 prefixEnd_566020 258346951162649491419491 := by
  unfold tailWord_566020
  simp only [CollatzResearch.WordTrace]
  refine ⟨10322222704706841682467757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13762963606275788909957009 10322222704706841682467757)
  ·
    refine ⟨3870833514265065630925409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10322222704706841682467757 3870833514265065630925409)
    ·
      refine ⟨2903125135698799223194057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3870833514265065630925409 2903125135698799223194057)
      ·
        refine ⟨2177343851774099417395543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2903125135698799223194057 2177343851774099417395543)
        ·
          refine ⟨3266015777661149126093315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2177343851774099417395543 3266015777661149126093315)
          ·
            refine ⟨4899023666491723689139973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3266015777661149126093315 4899023666491723689139973)
            ·
              refine ⟨918566937467198191713745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4899023666491723689139973 918566937467198191713745)
              ·
                refine ⟨688925203100398643785309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 918566937467198191713745 688925203100398643785309)
                ·
                  refine ⟨258346951162649491419491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 688925203100398643785309 258346951162649491419491)
                  ·
                    rfl

theorem cell20_566020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_566020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566020 prefixEnd_566020 := by exact prefixLift 566020
  have htrace : WordTrace (prefixWord ++ tailWord_566020) baseStart_566020 baseEnd_566020 := by
    simpa [prefixWord, tailWord_566020, baseEnd_566020] using wordTrace_append hprefix tailTrace_566020
  have hstable : (prefixWord ++ tailWord_566020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566020).length < 2 ^ (prefixWord ++ tailWord_566020).sum := by decide
  have hdescent : baseEnd_566020 < baseStart_566020 := by decide
  rcases family_descends (prefixWord ++ tailWord_566020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566023 : List Nat := [1, 1, 4, 4, 1, 1, 4, 2, 2]
def baseStart_566023 : Nat := 118140960795 + 566023 * 2 ^ 59
def prefixEnd_566023 : Nat := 4983230072969 + 3 ^ 40 * 566023 * 2
def baseEnd_566023 : Nat := 258348320444394814319479

theorem tailTrace_566023 : CollatzResearch.WordTrace tailWord_566023 prefixEnd_566023 258348320444394814319479 := by
  unfold tailWord_566023
  simp only [CollatzResearch.WordTrace]
  refine ⟨20644554828402814877294723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13763036552268543251529815 20644554828402814877294723)
  ·
    refine ⟨30966832242604222315942085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20644554828402814877294723 30966832242604222315942085)
    ·
      refine ⟨5806281045488291684239141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30966832242604222315942085 5806281045488291684239141)
      ·
        refine ⟨1088677696029054690794839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5806281045488291684239141 1088677696029054690794839)
        ·
          refine ⟨1633016544043582036192259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088677696029054690794839 1633016544043582036192259)
          ·
            refine ⟨2449524816065373054288389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633016544043582036192259 2449524816065373054288389)
            ·
              refine ⟨459285903012257447679073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2449524816065373054288389 459285903012257447679073)
              ·
                refine ⟨344464427259193085759305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459285903012257447679073 344464427259193085759305)
                ·
                  refine ⟨258348320444394814319479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344464427259193085759305 258348320444394814319479)
                  ·
                    rfl

theorem cell20_566023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 2].length) (baseStart_566023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566023 prefixEnd_566023 := by exact prefixLift 566023
  have htrace : WordTrace (prefixWord ++ tailWord_566023) baseStart_566023 baseEnd_566023 := by
    simpa [prefixWord, tailWord_566023, baseEnd_566023] using wordTrace_append hprefix tailTrace_566023
  have hstable : (prefixWord ++ tailWord_566023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566023).length < 2 ^ (prefixWord ++ tailWord_566023).sum := by decide
  have hdescent : baseEnd_566023 < baseStart_566023 := by decide
  rcases family_descends (prefixWord ++ tailWord_566023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566048 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 6]
def baseStart_566048 : Nat := 118140960795 + 566048 * 2 ^ 59
def prefixEnd_566048 : Nat := 4983230072969 + 3 ^ 40 * 566048 * 2
def baseEnd_566048 : Nat := 258359731125605838486043

theorem tailTrace_566048 : CollatzResearch.WordTrace tailWord_566048 prefixEnd_566048 258359731125605838486043 := by
  unfold tailWord_566048
  simp only [CollatzResearch.WordTrace]
  refine ⟨10322733326656122073477399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13763644435541496097969865 10322733326656122073477399)
  ·
    refine ⟨15484099989984183110216099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10322733326656122073477399 15484099989984183110216099)
    ·
      refine ⟨23226149984976274665324149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15484099989984183110216099 23226149984976274665324149)
      ·
        refine ⟨2177451561091525749874139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23226149984976274665324149 2177451561091525749874139)
        ·
          refine ⟨3266177341637288624811209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2177451561091525749874139 3266177341637288624811209)
          ·
            refine ⟨2449633006227966468608407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3266177341637288624811209 2449633006227966468608407)
            ·
              refine ⟨3674449509341949702912611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2449633006227966468608407 3674449509341949702912611)
              ·
                refine ⟨5511674264012924554368917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3674449509341949702912611 5511674264012924554368917)
                ·
                  refine ⟨258359731125605838486043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5511674264012924554368917 258359731125605838486043)
                  ·
                    rfl

theorem cell20_566048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_566048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566048 prefixEnd_566048 := by exact prefixLift 566048
  have htrace : WordTrace (prefixWord ++ tailWord_566048) baseStart_566048 baseEnd_566048 := by
    simpa [prefixWord, tailWord_566048, baseEnd_566048] using wordTrace_append hprefix tailTrace_566048
  have hstable : (prefixWord ++ tailWord_566048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566048).length < 2 ^ (prefixWord ++ tailWord_566048).sum := by decide
  have hdescent : baseEnd_566048 < baseStart_566048 := by decide
  rcases family_descends (prefixWord ++ tailWord_566048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566079 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 5]
def baseStart_566079 : Nat := 118140960795 + 566079 * 2 ^ 59
def prefixEnd_566079 : Nat := 4983230072969 + 3 ^ 40 * 566079 * 2
def baseEnd_566079 : Nat := 258373880370307508452583

theorem tailTrace_566079 : CollatzResearch.WordTrace tailWord_566079 prefixEnd_566079 258373880370307508452583 := by
  unfold tailWord_566079
  simp only [CollatzResearch.WordTrace]
  refine ⟨20646597316199936441333291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13764398210799957627555527 20646597316199936441333291)
  ·
    refine ⟨30969895974299904661999937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20646597316199936441333291 30969895974299904661999937)
    ·
      refine ⟨23227421980724928496499953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30969895974299904661999937 23227421980724928496499953)
      ·
        refine ⟨17420566485543696372374965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23227421980724928496499953 17420566485543696372374965)
        ·
          refine ⟨1633178108019721534910153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17420566485543696372374965 1633178108019721534910153)
          ·
            refine ⟨1224883581014791151182615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1633178108019721534910153 1224883581014791151182615)
            ·
              refine ⟨1837325371522186726773923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224883581014791151182615 1837325371522186726773923)
              ·
                refine ⟨2755988057283280090160885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837325371522186726773923 2755988057283280090160885)
                ·
                  refine ⟨258373880370307508452583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2755988057283280090160885 258373880370307508452583)
                  ·
                    rfl

theorem cell20_566079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_566079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566079 prefixEnd_566079 := by exact prefixLift 566079
  have htrace : WordTrace (prefixWord ++ tailWord_566079) baseStart_566079 baseEnd_566079 := by
    simpa [prefixWord, tailWord_566079, baseEnd_566079] using wordTrace_append hprefix tailTrace_566079
  have hstable : (prefixWord ++ tailWord_566079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566079).length < 2 ^ (prefixWord ++ tailWord_566079).sum := by decide
  have hdescent : baseEnd_566079 < baseStart_566079 := by decide
  rcases family_descends (prefixWord ++ tailWord_566079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566107 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 12]
def baseStart_566107 : Nat := 118140960795 + 566107 * 2 ^ 59
def prefixEnd_566107 : Nat := 4983230072969 + 3 ^ 40 * 566107 * 2
def baseEnd_566107 : Nat := 258386660333263855519135

theorem tailTrace_566107 : CollatzResearch.WordTrace tailWord_566107 prefixEnd_566107 258386660333263855519135 := by
  unfold tailWord_566107
  simp only [CollatzResearch.WordTrace]
  refine ⟨20647618560098497223352575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13765079040065664815568383 20647618560098497223352575)
  ·
    refine ⟨30971427840147745835028863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20647618560098497223352575 30971427840147745835028863)
    ·
      refine ⟨46457141760221618752543295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30971427840147745835028863 46457141760221618752543295)
      ·
        refine ⟨69685712640332428128814943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46457141760221618752543295 69685712640332428128814943)
        ·
          refine ⟨104528568960498642193222415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69685712640332428128814943 104528568960498642193222415)
          ·
            refine ⟨156792853440747963289833623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104528568960498642193222415 156792853440747963289833623)
            ·
              refine ⟨235189280161121944934750435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156792853440747963289833623 235189280161121944934750435)
              ·
                refine ⟨352783920241682917402125653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235189280161121944934750435 352783920241682917402125653)
                ·
                  refine ⟨258386660333263855519135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 352783920241682917402125653 258386660333263855519135)
                  ·
                    rfl

theorem cell20_566107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_566107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566107 prefixEnd_566107 := by exact prefixLift 566107
  have htrace : WordTrace (prefixWord ++ tailWord_566107) baseStart_566107 baseEnd_566107 := by
    simpa [prefixWord, tailWord_566107, baseEnd_566107] using wordTrace_append hprefix tailTrace_566107
  have hstable : (prefixWord ++ tailWord_566107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566107).length < 2 ^ (prefixWord ++ tailWord_566107).sum := by decide
  have hdescent : baseEnd_566107 < baseStart_566107 := by decide
  rcases family_descends (prefixWord ++ tailWord_566107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566120 : List Nat := [2, 1, 4, 2, 1, 2, 3, 3, 2]
def baseStart_566120 : Nat := 118140960795 + 566120 * 2 ^ 59
def prefixEnd_566120 : Nat := 4983230072969 + 3 ^ 40 * 566120 * 2
def baseEnd_566120 : Nat := 258392593887493588085749

theorem tailTrace_566120 : CollatzResearch.WordTrace tailWord_566120 prefixEnd_566120 258392593887493588085749 := by
  unfold tailWord_566120
  simp only [CollatzResearch.WordTrace]
  refine ⟨10324046354525700221787907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13765395139367600295717209 10324046354525700221787907)
  ·
    refine ⟨15486069531788550332681861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10324046354525700221787907 15486069531788550332681861)
    ·
      refine ⟨2903638037210353187377849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15486069531788550332681861 2903638037210353187377849)
      ·
        refine ⟨2177728527907764890533387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2903638037210353187377849 2177728527907764890533387)
        ·
          refine ⟨3266592791861647335800081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2177728527907764890533387 3266592791861647335800081)
          ·
            refine ⟨2449944593896235501850061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3266592791861647335800081 2449944593896235501850061)
            ·
              refine ⟨918729222711088313193773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2449944593896235501850061 918729222711088313193773)
              ·
                refine ⟨344523458516658117447665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 918729222711088313193773 344523458516658117447665)
                ·
                  refine ⟨258392593887493588085749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344523458516658117447665 258392593887493588085749)
                  ·
                    rfl

theorem cell20_566120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 2].length) (baseStart_566120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566120 prefixEnd_566120 := by exact prefixLift 566120
  have htrace : WordTrace (prefixWord ++ tailWord_566120) baseStart_566120 baseEnd_566120 := by
    simpa [prefixWord, tailWord_566120, baseEnd_566120] using wordTrace_append hprefix tailTrace_566120
  have hstable : (prefixWord ++ tailWord_566120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566120).length < 2 ^ (prefixWord ++ tailWord_566120).sum := by decide
  have hdescent : baseEnd_566120 < baseStart_566120 := by decide
  rcases family_descends (prefixWord ++ tailWord_566120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566134 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_566134 : Nat := 118140960795 + 566134 * 2 ^ 59
def prefixEnd_566134 : Nat := 4983230072969 + 3 ^ 40 * 566134 * 2
def baseEnd_566134 : Nat := 258398983868971761619025

theorem tailTrace_566134 : CollatzResearch.WordTrace tailWord_566134 prefixEnd_566134 258398983868971761619025 := by
  unfold tailWord_566134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290537708187542552161591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13765735554000453889723637 1290537708187542552161591)
  ·
    refine ⟨1935806562281313828242387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1290537708187542552161591 1935806562281313828242387)
    ·
      refine ⟨2903709843421970742363581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1935806562281313828242387 2903709843421970742363581)
      ·
        refine ⟨1088891191283239028386343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2903709843421970742363581 1088891191283239028386343)
        ·
          refine ⟨1633336786924858542579515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088891191283239028386343 1633336786924858542579515)
          ·
            refine ⟨2450005180387287813869273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633336786924858542579515 2450005180387287813869273)
            ·
              refine ⟨1837503885290465860401955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2450005180387287813869273 1837503885290465860401955)
              ·
                refine ⟨2756255827935698790602933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837503885290465860401955 2756255827935698790602933)
                ·
                  refine ⟨258398983868971761619025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2756255827935698790602933 258398983868971761619025)
                  ·
                    rfl

theorem cell20_566134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_566134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566134 prefixEnd_566134 := by exact prefixLift 566134
  have htrace : WordTrace (prefixWord ++ tailWord_566134) baseStart_566134 baseEnd_566134 := by
    simpa [prefixWord, tailWord_566134, baseEnd_566134] using wordTrace_append hprefix tailTrace_566134
  have hstable : (prefixWord ++ tailWord_566134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566134).length < 2 ^ (prefixWord ++ tailWord_566134).sum := by decide
  have hdescent : baseEnd_566134 < baseStart_566134 := by decide
  rcases family_descends (prefixWord ++ tailWord_566134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566141 : List Nat := [1, 4, 1, 1, 2, 1, 2, 6, 2]
def baseStart_566141 : Nat := 118140960795 + 566141 * 2 ^ 59
def prefixEnd_566141 : Nat := 4983230072969 + 3 ^ 40 * 566141 * 2
def baseEnd_566141 : Nat := 258402178859710848385663

theorem tailTrace_566141 : CollatzResearch.WordTrace tailWord_566141 prefixEnd_566141 258402178859710848385663 := by
  unfold tailWord_566141
  simp only [CollatzResearch.WordTrace]
  refine ⟨20648858641975321030090277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13765905761316880686726851 20648858641975321030090277)
  ·
    refine ⟨3871660995370372693141927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20648858641975321030090277 3871660995370372693141927)
    ·
      refine ⟨5807491493055559039712891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3871660995370372693141927 5807491493055559039712891)
      ·
        refine ⟨8711237239583338559569337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5807491493055559039712891 8711237239583338559569337)
        ·
          refine ⟨6533427929687503919677003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8711237239583338559569337 6533427929687503919677003)
          ·
            refine ⟨9800141894531255879515505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6533427929687503919677003 9800141894531255879515505)
            ·
              refine ⟨7350106420898441909636629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9800141894531255879515505 7350106420898441909636629)
              ·
                refine ⟨344536238479614464514217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7350106420898441909636629 344536238479614464514217)
                ·
                  refine ⟨258402178859710848385663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344536238479614464514217 258402178859710848385663)
                  ·
                    rfl

theorem cell20_566141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_566141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566141 prefixEnd_566141 := by exact prefixLift 566141
  have htrace : WordTrace (prefixWord ++ tailWord_566141) baseStart_566141 baseEnd_566141 := by
    simpa [prefixWord, tailWord_566141, baseEnd_566141] using wordTrace_append hprefix tailTrace_566141
  have hstable : (prefixWord ++ tailWord_566141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566141).length < 2 ^ (prefixWord ++ tailWord_566141).sum := by decide
  have hdescent : baseEnd_566141 < baseStart_566141 := by decide
  rcases family_descends (prefixWord ++ tailWord_566141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566151 : List Nat := [1, 1, 4, 2, 3, 3, 2, 1, 3]
def baseStart_566151 : Nat := 118140960795 + 566151 * 2 ^ 59
def prefixEnd_566151 : Nat := 4983230072969 + 3 ^ 40 * 566151 * 2
def baseEnd_566151 : Nat := 258406743132195258052289

theorem tailTrace_566151 : CollatzResearch.WordTrace tailWord_566151 prefixEnd_566151 258406743132195258052289 := by
  unfold tailWord_566151
  simp only [CollatzResearch.WordTrace]
  refine ⟨20649223371939092737954307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13766148914626061825302871 20649223371939092737954307)
  ·
    refine ⟨30973835057908639106931461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20649223371939092737954307 30973835057908639106931461)
    ·
      refine ⟨5807594073357869832549649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30973835057908639106931461 5807594073357869832549649)
      ·
        refine ⟨4355695555018402374412237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5807594073357869832549649 4355695555018402374412237)
        ·
          refine ⟨1633385833131900890404589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4355695555018402374412237 1633385833131900890404589)
          ·
            refine ⟨612519687424462833901721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1633385833131900890404589 612519687424462833901721)
            ·
              refine ⟨459389765568347125426291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612519687424462833901721 459389765568347125426291)
              ·
                refine ⟨689084648352520688139437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459389765568347125426291 689084648352520688139437)
                ·
                  refine ⟨258406743132195258052289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 689084648352520688139437 258406743132195258052289)
                  ·
                    rfl

theorem cell20_566151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 3].length) (baseStart_566151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566151 prefixEnd_566151 := by exact prefixLift 566151
  have htrace : WordTrace (prefixWord ++ tailWord_566151) baseStart_566151 baseEnd_566151 := by
    simpa [prefixWord, tailWord_566151, baseEnd_566151] using wordTrace_append hprefix tailTrace_566151
  have hstable : (prefixWord ++ tailWord_566151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566151).length < 2 ^ (prefixWord ++ tailWord_566151).sum := by decide
  have hdescent : baseEnd_566151 < baseStart_566151 := by decide
  rcases family_descends (prefixWord ++ tailWord_566151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566176 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 7]
def baseStart_566176 : Nat := 118140960795 + 566176 * 2 ^ 59
def prefixEnd_566176 : Nat := 4983230072969 + 3 ^ 40 * 566176 * 2
def baseEnd_566176 : Nat := 258418153813406282218853

theorem tailTrace_566176 : CollatzResearch.WordTrace tailWord_566176 prefixEnd_566176 258418153813406282218853 := by
  unfold tailWord_566176
  simp only [CollatzResearch.WordTrace]
  refine ⟨10325067598424261003807191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13766756797899014671742921 10325067598424261003807191)
  ·
    refine ⟨15487601397636391505710787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10325067598424261003807191 15487601397636391505710787)
    ·
      refine ⟨23231402096454587258566181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15487601397636391505710787 23231402096454587258566181)
      ·
        refine ⟨4355887893085235110981159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23231402096454587258566181 4355887893085235110981159)
        ·
          refine ⟨6533831839627852666471739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4355887893085235110981159 6533831839627852666471739)
          ·
            refine ⟨9800747759441778999707609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6533831839627852666471739 9800747759441778999707609)
            ·
              refine ⟨7350560819581334249780707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9800747759441778999707609 7350560819581334249780707)
              ·
                refine ⟨11025841229372001374671061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7350560819581334249780707 11025841229372001374671061)
                ·
                  refine ⟨258418153813406282218853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11025841229372001374671061 258418153813406282218853)
                  ·
                    rfl

theorem cell20_566176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_566176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566176 prefixEnd_566176 := by exact prefixLift 566176
  have htrace : WordTrace (prefixWord ++ tailWord_566176) baseStart_566176 baseEnd_566176 := by
    simpa [prefixWord, tailWord_566176, baseEnd_566176] using wordTrace_append hprefix tailTrace_566176
  have hstable : (prefixWord ++ tailWord_566176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566176).length < 2 ^ (prefixWord ++ tailWord_566176).sum := by decide
  have hdescent : baseEnd_566176 < baseStart_566176 := by decide
  rcases family_descends (prefixWord ++ tailWord_566176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566234 : List Nat := [3, 1, 1, 2, 4, 2, 2, 3, 2]
def baseStart_566234 : Nat := 118140960795 + 566234 * 2 ^ 59
def prefixEnd_566234 : Nat := 4983230072969 + 3 ^ 40 * 566234 * 2
def baseEnd_566234 : Nat := 258444626593815858285283

theorem tailTrace_566234 : CollatzResearch.WordTrace tailWord_566234 prefixEnd_566234 258444626593815858285283 := by
  unfold tailWord_566234
  simp only [CollatzResearch.WordTrace]
  refine ⟨5163062657659599478306439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13768167087092265275483837 5163062657659599478306439)
  ·
    refine ⟨7744593986489399217459659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5163062657659599478306439 7744593986489399217459659)
    ·
      refine ⟨11616890979734098826189489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7744593986489399217459659 11616890979734098826189489)
      ·
        refine ⟨8712668234800574119642117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11616890979734098826189489 8712668234800574119642117)
        ·
          refine ⟨1633625294025107647432897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8712668234800574119642117 1633625294025107647432897)
          ·
            refine ⟨1225218970518830735574673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1633625294025107647432897 1225218970518830735574673)
            ·
              refine ⟨918914227889123051681005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225218970518830735574673 918914227889123051681005)
              ·
                refine ⟨344592835458421144380377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 918914227889123051681005 344592835458421144380377)
                ·
                  refine ⟨258444626593815858285283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344592835458421144380377 258444626593815858285283)
                  ·
                    rfl

theorem cell20_566234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_566234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566234 prefixEnd_566234 := by exact prefixLift 566234
  have htrace : WordTrace (prefixWord ++ tailWord_566234) baseStart_566234 baseEnd_566234 := by
    simpa [prefixWord, tailWord_566234, baseEnd_566234] using wordTrace_append hprefix tailTrace_566234
  have hstable : (prefixWord ++ tailWord_566234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566234).length < 2 ^ (prefixWord ++ tailWord_566234).sum := by decide
  have hdescent : baseEnd_566234 < baseStart_566234 := by decide
  rcases family_descends (prefixWord ++ tailWord_566234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566255 : List Nat := [1, 1, 2, 1, 4, 3, 2, 4, 2]
def baseStart_566255 : Nat := 118140960795 + 566255 * 2 ^ 59
def prefixEnd_566255 : Nat := 4983230072969 + 3 ^ 40 * 566255 * 2
def baseEnd_566255 : Nat := 258454211566033118585197

theorem tailTrace_566255 : CollatzResearch.WordTrace tailWord_566255 prefixEnd_566255 258454211566033118585197 := by
  unfold tailWord_566255
  simp only [CollatzResearch.WordTrace]
  refine ⟨20653016563562318499740219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13768677709041545666493479 20653016563562318499740219)
  ·
    refine ⟨30979524845343477749610329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20653016563562318499740219 30979524845343477749610329)
    ·
      refine ⟨23234643634007608312207747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30979524845343477749610329 23234643634007608312207747)
      ·
        refine ⟨34851965451011412468311621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23234643634007608312207747 34851965451011412468311621)
        ·
          refine ⟨6534743522064639837808429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34851965451011412468311621 6534743522064639837808429)
          ·
            refine ⟨2450528820774239939178161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6534743522064639837808429 2450528820774239939178161)
            ·
              refine ⟨1837896615580679954383621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2450528820774239939178161 1837896615580679954383621)
              ·
                refine ⟨344605615421377491446929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1837896615580679954383621 344605615421377491446929)
                ·
                  refine ⟨258454211566033118585197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344605615421377491446929 258454211566033118585197)
                  ·
                    rfl

theorem cell20_566255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 2].length) (baseStart_566255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566255 prefixEnd_566255 := by exact prefixLift 566255
  have htrace : WordTrace (prefixWord ++ tailWord_566255) baseStart_566255 baseEnd_566255 := by
    simpa [prefixWord, tailWord_566255, baseEnd_566255] using wordTrace_append hprefix tailTrace_566255
  have hstable : (prefixWord ++ tailWord_566255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566255).length < 2 ^ (prefixWord ++ tailWord_566255).sum := by decide
  have hdescent : baseEnd_566255 < baseStart_566255 := by decide
  rcases family_descends (prefixWord ++ tailWord_566255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566283 : List Nat := [1, 1, 1, 1, 6, 3, 1, 6]
def baseStart_566283 : Nat := 118140960795 + 566283 * 2 ^ 59
def prefixEnd_566283 : Nat := 4983230072969 + 3 ^ 40 * 566283 * 2
def baseEnd_566283 : Nat := 86155663842996488550583

theorem tailTrace_566283 : CollatzResearch.WordTrace tailWord_566283 prefixEnd_566283 86155663842996488550583 := by
  unfold tailWord_566283
  simp only [CollatzResearch.WordTrace]
  refine ⟨20654037807460879281759503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13769358538307252854506335 20654037807460879281759503)
  ·
    refine ⟨30981056711191318922639255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20654037807460879281759503 30981056711191318922639255)
    ·
      refine ⟨46471585066786978383958883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30981056711191318922639255 46471585066786978383958883)
      ·
        refine ⟨69707377600180467575938325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46471585066786978383958883 69707377600180467575938325)
        ·
          refine ⟨3267533325008459417622109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69707377600180467575938325 3267533325008459417622109)
          ·
            refine ⟨1225324996878172281608291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3267533325008459417622109 1225324996878172281608291)
            ·
              refine ⟨1837987495317258422412437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225324996878172281608291 1837987495317258422412437)
              ·
                refine ⟨86155663842996488550583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1837987495317258422412437 86155663842996488550583)
                ·
                  rfl

theorem cell20_566283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 6].length) (baseStart_566283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566283 prefixEnd_566283 := by exact prefixLift 566283
  have htrace : WordTrace (prefixWord ++ tailWord_566283) baseStart_566283 baseEnd_566283 := by
    simpa [prefixWord, tailWord_566283, baseEnd_566283] using wordTrace_append hprefix tailTrace_566283
  have hstable : (prefixWord ++ tailWord_566283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566283).length < 2 ^ (prefixWord ++ tailWord_566283).sum := by decide
  have hdescent : baseEnd_566283 < baseStart_566283 := by decide
  rcases family_descends (prefixWord ++ tailWord_566283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566297 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 6]
def baseStart_566297 : Nat := 118140960795 + 566297 * 2 ^ 59
def prefixEnd_566297 : Nat := 4983230072969 + 3 ^ 40 * 566297 * 2
def baseEnd_566297 : Nat := 258473381510467639185025

theorem tailTrace_566297 : CollatzResearch.WordTrace tailWord_566297 prefixEnd_566297 258473381510467639185025 := by
  unfold tailWord_566297
  simp only [CollatzResearch.WordTrace]
  refine ⟨20654548429410159672769145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13769698952940106448512763 20654548429410159672769145)
  ·
    refine ⟨15490911322057619754576859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20654548429410159672769145 15490911322057619754576859)
    ·
      refine ⟨23236366983086429631865289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15490911322057619754576859 23236366983086429631865289)
      ·
        refine ⟨17427275237314822223898967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23236366983086429631865289 17427275237314822223898967)
        ·
          refine ⟨26140912855972233335848451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17427275237314822223898967 26140912855972233335848451)
          ·
            refine ⟨39211369283958350003772677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26140912855972233335848451 39211369283958350003772677)
            ·
              refine ⟨7352131740742190625707377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39211369283958350003772677 7352131740742190625707377)
              ·
                refine ⟨5514098805556642969280533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7352131740742190625707377 5514098805556642969280533)
                ·
                  refine ⟨258473381510467639185025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5514098805556642969280533 258473381510467639185025)
                  ·
                    rfl

theorem cell20_566297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_566297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566297 prefixEnd_566297 := by exact prefixLift 566297
  have htrace : WordTrace (prefixWord ++ tailWord_566297) baseStart_566297 baseEnd_566297 := by
    simpa [prefixWord, tailWord_566297, baseEnd_566297] using wordTrace_append hprefix tailTrace_566297
  have hstable : (prefixWord ++ tailWord_566297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566297).length < 2 ^ (prefixWord ++ tailWord_566297).sum := by decide
  have hdescent : baseEnd_566297 < baseStart_566297 := by decide
  rcases family_descends (prefixWord ++ tailWord_566297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566300 : List Nat := [2, 2, 3, 1, 4, 2, 6]
def baseStart_566300 : Nat := 118140960795 + 566300 * 2 ^ 59
def prefixEnd_566300 : Nat := 4983230072969 + 3 ^ 40 * 566300 * 2
def baseEnd_566300 : Nat := 28719416754690329120557

theorem tailTrace_566300 : CollatzResearch.WordTrace tailWord_566300 prefixEnd_566300 28719416754690329120557 := by
  unfold tailWord_566300
  simp only [CollatzResearch.WordTrace]
  refine ⟨10327328924199645592564177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13769771898932860790085569 10327328924199645592564177)
  ·
    refine ⟨7745496693149734194423133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10327328924199645592564177 7745496693149734194423133)
    ·
      refine ⟨2904561259931150322908675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7745496693149734194423133 2904561259931150322908675)
      ·
        refine ⟨4356841889896725484363013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2904561259931150322908675 4356841889896725484363013)
        ·
          refine ⟨816907854355636028318065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4356841889896725484363013 816907854355636028318065)
          ·
            refine ⟨612680890766727021238549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 816907854355636028318065 612680890766727021238549)
            ·
              refine ⟨28719416754690329120557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 612680890766727021238549 28719416754690329120557)
              ·
                rfl

theorem cell20_566300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 6].length) (baseStart_566300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566300 prefixEnd_566300 := by exact prefixLift 566300
  have htrace : WordTrace (prefixWord ++ tailWord_566300) baseStart_566300 baseEnd_566300 := by
    simpa [prefixWord, tailWord_566300, baseEnd_566300] using wordTrace_append hprefix tailTrace_566300
  have hstable : (prefixWord ++ tailWord_566300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566300).length < 2 ^ (prefixWord ++ tailWord_566300).sum := by decide
  have hdescent : baseEnd_566300 < baseStart_566300 := by decide
  rcases family_descends (prefixWord ++ tailWord_566300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566321 : List Nat := [1, 2, 2, 3, 1, 2, 4, 5]
def baseStart_566321 : Nat := 118140960795 + 566321 * 2 ^ 59
def prefixEnd_566321 : Nat := 4983230072969 + 3 ^ 40 * 566321 * 2
def baseEnd_566321 : Nat := 86161445254810074128309

theorem tailTrace_566321 : CollatzResearch.WordTrace tailWord_566321 prefixEnd_566321 86161445254810074128309 := by
  unfold tailWord_566321
  simp only [CollatzResearch.WordTrace]
  refine ⟨20655423781323211771642817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13770282520882141181095211 20655423781323211771642817)
  ·
    refine ⟨15491567835992408828732113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20655423781323211771642817 15491567835992408828732113)
    ·
      refine ⟨11618675876994306621549085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15491567835992408828732113 11618675876994306621549085)
      ·
        refine ⟨4357003453872864983080907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11618675876994306621549085 4357003453872864983080907)
        ·
          refine ⟨6535505180809297474621361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4357003453872864983080907 6535505180809297474621361)
          ·
            refine ⟨4901628885606973105966021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6535505180809297474621361 4901628885606973105966021)
            ·
              refine ⟨919055416051307457368629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4901628885606973105966021 919055416051307457368629)
              ·
                refine ⟨86161445254810074128309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 919055416051307457368629 86161445254810074128309)
                ·
                  rfl

theorem cell20_566321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 5].length) (baseStart_566321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566321 prefixEnd_566321 := by exact prefixLift 566321
  have htrace : WordTrace (prefixWord ++ tailWord_566321) baseStart_566321 baseEnd_566321 := by
    simpa [prefixWord, tailWord_566321, baseEnd_566321] using wordTrace_append hprefix tailTrace_566321
  have hstable : (prefixWord ++ tailWord_566321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566321).length < 2 ^ (prefixWord ++ tailWord_566321).sum := by decide
  have hdescent : baseEnd_566321 < baseStart_566321 := by decide
  rcases family_descends (prefixWord ++ tailWord_566321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566335 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 6]
def baseStart_566335 : Nat := 118140960795 + 566335 * 2 ^ 59
def prefixEnd_566335 : Nat := 4983230072969 + 3 ^ 40 * 566335 * 2
def baseEnd_566335 : Nat := 258490725745908395918203

theorem tailTrace_566335 : CollatzResearch.WordTrace tailWord_566335 prefixEnd_566335 258490725745908395918203 := by
  unfold tailWord_566335
  simp only [CollatzResearch.WordTrace]
  refine ⟨20655934403272492162652459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13770622935514994775101639 20655934403272492162652459)
  ·
    refine ⟨30983901604908738243978689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20655934403272492162652459 30983901604908738243978689)
    ·
      refine ⟨23237926203681553682984017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30983901604908738243978689 23237926203681553682984017)
      ·
        refine ⟨17428444652761165262238013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23237926203681553682984017 17428444652761165262238013)
        ·
          refine ⟨6535666744785436973339255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17428444652761165262238013 6535666744785436973339255)
          ·
            refine ⟨9803500117178155460008883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6535666744785436973339255 9803500117178155460008883)
            ·
              refine ⟨14705250175767233190013325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9803500117178155460008883 14705250175767233190013325)
              ·
                refine ⟨5514468815912712446254997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14705250175767233190013325 5514468815912712446254997)
                ·
                  refine ⟨258490725745908395918203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5514468815912712446254997 258490725745908395918203)
                  ·
                    rfl

theorem cell20_566335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_566335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566335 prefixEnd_566335 := by exact prefixLift 566335
  have htrace : WordTrace (prefixWord ++ tailWord_566335) baseStart_566335 baseEnd_566335 := by
    simpa [prefixWord, tailWord_566335, baseEnd_566335] using wordTrace_append hprefix tailTrace_566335
  have hstable : (prefixWord ++ tailWord_566335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566335).length < 2 ^ (prefixWord ++ tailWord_566335).sum := by decide
  have hdescent : baseEnd_566335 < baseStart_566335 := by decide
  rcases family_descends (prefixWord ++ tailWord_566335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566358 : List Nat := [5, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_566358 : Nat := 118140960795 + 566358 * 2 ^ 59
def prefixEnd_566358 : Nat := 4983230072969 + 3 ^ 40 * 566358 * 2
def baseEnd_566358 : Nat := 258501223572622538151443

theorem tailTrace_566358 : CollatzResearch.WordTrace tailWord_566358 prefixEnd_566358 258501223572622538151443 := by
  unfold tailWord_566358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1291048330136822943171233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13771182188126111393826485 1291048330136822943171233)
  ·
    refine ⟨968286247602617207378425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1291048330136822943171233 968286247602617207378425)
    ·
      refine ⟨726214685701962905533819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 968286247602617207378425 726214685701962905533819)
      ·
        refine ⟨1089322028552944358300729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726214685701962905533819 1089322028552944358300729)
        ·
          refine ⟨816991521414708268725547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1089322028552944358300729 816991521414708268725547)
          ·
            refine ⟨1225487282122062403088321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816991521414708268725547 1225487282122062403088321)
            ·
              refine ⟨919115461591546802316241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225487282122062403088321 919115461591546802316241)
              ·
                refine ⟨689336596193660101737181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 919115461591546802316241 689336596193660101737181)
                ·
                  refine ⟨258501223572622538151443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 689336596193660101737181 258501223572622538151443)
                  ·
                    rfl

theorem cell20_566358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_566358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566358 prefixEnd_566358 := by exact prefixLift 566358
  have htrace : WordTrace (prefixWord ++ tailWord_566358) baseStart_566358 baseEnd_566358 := by
    simpa [prefixWord, tailWord_566358, baseEnd_566358] using wordTrace_append hprefix tailTrace_566358
  have hstable : (prefixWord ++ tailWord_566358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566358).length < 2 ^ (prefixWord ++ tailWord_566358).sum := by decide
  have hdescent : baseEnd_566358 < baseStart_566358 := by decide
  rcases family_descends (prefixWord ++ tailWord_566358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566365 : List Nat := [1, 4, 4, 1, 2, 1, 1, 4, 2]
def baseStart_566365 : Nat := 118140960795 + 566365 * 2 ^ 59
def prefixEnd_566365 : Nat := 4983230072969 + 3 ^ 40 * 566365 * 2
def baseEnd_566365 : Nat := 258504418563361624918081

theorem tailTrace_566365 : CollatzResearch.WordTrace tailWord_566365 prefixEnd_566365 258504418563361624918081 := by
  unfold tailWord_566365
  simp only [CollatzResearch.WordTrace]
  refine ⟨20657028593163807286244549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13771352395442538190829699 20657028593163807286244549)
  ·
    refine ⟨3873192861218213866170853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20657028593163807286244549 3873192861218213866170853)
    ·
      refine ⟨726223661478415099907035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3873192861218213866170853 726223661478415099907035)
      ·
        refine ⟨1089335492217622649860553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726223661478415099907035 1089335492217622649860553)
        ·
          refine ⟨817001619163216987395415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1089335492217622649860553 817001619163216987395415)
          ·
            refine ⟨1225502428744825481093123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817001619163216987395415 1225502428744825481093123)
            ·
              refine ⟨1838253643117238221639685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225502428744825481093123 1838253643117238221639685)
              ·
                refine ⟨344672558084482166557441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1838253643117238221639685 344672558084482166557441)
                ·
                  refine ⟨258504418563361624918081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344672558084482166557441 258504418563361624918081)
                  ·
                    rfl

theorem cell20_566365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_566365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566365 prefixEnd_566365 := by exact prefixLift 566365
  have htrace : WordTrace (prefixWord ++ tailWord_566365) baseStart_566365 baseEnd_566365 := by
    simpa [prefixWord, tailWord_566365, baseEnd_566365] using wordTrace_append hprefix tailTrace_566365
  have hstable : (prefixWord ++ tailWord_566365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566365).length < 2 ^ (prefixWord ++ tailWord_566365).sum := by decide
  have hdescent : baseEnd_566365 < baseStart_566365 := by decide
  rcases family_descends (prefixWord ++ tailWord_566365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566428 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 4]
def baseStart_566428 : Nat := 118140960795 + 566428 * 2 ^ 59
def prefixEnd_566428 : Nat := 4983230072969 + 3 ^ 40 * 566428 * 2
def baseEnd_566428 : Nat := 258533173480013405817823

theorem tailTrace_566428 : CollatzResearch.WordTrace tailWord_566428 prefixEnd_566428 258533173480013405817823 := by
  unfold tailWord_566428
  simp only [CollatzResearch.WordTrace]
  refine ⟨10329663195967784522893969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13772884261290379363858625 10329663195967784522893969)
  ·
    refine ⟨7747247396975838392170477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10329663195967784522893969 7747247396975838392170477)
    ·
      refine ⟨2905217773865939397063929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7747247396975838392170477 2905217773865939397063929)
      ·
        refine ⟨2178913330399454547797947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2905217773865939397063929 2178913330399454547797947)
        ·
          refine ⟨3268369995599181821696921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2178913330399454547797947 3268369995599181821696921)
          ·
            refine ⟨2451277496699386366272691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3268369995599181821696921 2451277496699386366272691)
            ·
              refine ⟨3676916245049079549409037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2451277496699386366272691 3676916245049079549409037)
              ·
                refine ⟨1378843591893404831028389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3676916245049079549409037 1378843591893404831028389)
                ·
                  refine ⟨258533173480013405817823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1378843591893404831028389 258533173480013405817823)
                  ·
                    rfl

theorem cell20_566428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_566428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566428 prefixEnd_566428 := by exact prefixLift 566428
  have htrace : WordTrace (prefixWord ++ tailWord_566428) baseStart_566428 baseEnd_566428 := by
    simpa [prefixWord, tailWord_566428, baseEnd_566428] using wordTrace_append hprefix tailTrace_566428
  have hstable : (prefixWord ++ tailWord_566428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566428).length < 2 ^ (prefixWord ++ tailWord_566428).sum := by decide
  have hdescent : baseEnd_566428 < baseStart_566428 := by decide
  rcases family_descends (prefixWord ++ tailWord_566428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566462 : List Nat := [4, 2, 1, 1, 3, 1, 3, 3, 2]
def baseStart_566462 : Nat := 118140960795 + 566462 * 2 ^ 59
def prefixEnd_566462 : Nat := 4983230072969 + 3 ^ 40 * 566462 * 2
def baseEnd_566462 : Nat := 258548692006460398684351

theorem tailTrace_566462 : CollatzResearch.WordTrace tailWord_566462 prefixEnd_566462 258548692006460398684351 := by
  unfold tailWord_566462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2582570809226549106565705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13773710982541595235017093 2582570809226549106565705)
  ·
    refine ⟨1936928106919911829924279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2582570809226549106565705 1936928106919911829924279)
    ·
      refine ⟨2905392160379867744886419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1936928106919911829924279 2905392160379867744886419)
      ·
        refine ⟨4358088240569801617329629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2905392160379867744886419 4358088240569801617329629)
        ·
          refine ⟨1634283090213675606498611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4358088240569801617329629 1634283090213675606498611)
          ·
            refine ⟨2451424635320513409747917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1634283090213675606498611 2451424635320513409747917)
            ·
              refine ⟨919284238245192528655469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2451424635320513409747917 919284238245192528655469)
              ·
                refine ⟨344731589341947198245801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 919284238245192528655469 344731589341947198245801)
                ·
                  refine ⟨258548692006460398684351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344731589341947198245801 258548692006460398684351)
                  ·
                    rfl

theorem cell20_566462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_566462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566462 prefixEnd_566462 := by exact prefixLift 566462
  have htrace : WordTrace (prefixWord ++ tailWord_566462) baseStart_566462 baseEnd_566462 := by
    simpa [prefixWord, tailWord_566462, baseEnd_566462] using wordTrace_append hprefix tailTrace_566462
  have hstable : (prefixWord ++ tailWord_566462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566462).length < 2 ^ (prefixWord ++ tailWord_566462).sum := by decide
  have hdescent : baseEnd_566462 < baseStart_566462 := by decide
  rcases family_descends (prefixWord ++ tailWord_566462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566497 : List Nat := [1, 2, 3, 1, 3, 3, 1, 3, 3]
def baseStart_566497 : Nat := 118140960795 + 566497 * 2 ^ 59
def prefixEnd_566497 : Nat := 4983230072969 + 3 ^ 40 * 566497 * 2
def baseEnd_566497 : Nat := 258564666960155832517541

theorem tailTrace_566497 : CollatzResearch.WordTrace tailWord_566497 prefixEnd_566497 258564666960155832517541 := by
  unfold tailWord_566497
  simp only [CollatzResearch.WordTrace]
  refine ⟨20661843028685593830049745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13774562019123729220033163 20661843028685593830049745)
  ·
    refine ⟨15496382271514195372537309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20661843028685593830049745 15496382271514195372537309)
    ·
      refine ⟨5811143351817823264701491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15496382271514195372537309 5811143351817823264701491)
      ·
        refine ⟨8716715027726734897052237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5811143351817823264701491 8716715027726734897052237)
        ·
          refine ⟨3268768135397525586394589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8716715027726734897052237 3268768135397525586394589)
          ·
            refine ⟨1225788050774072094897971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3268768135397525586394589 1225788050774072094897971)
            ·
              refine ⟨1838682076161108142346957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225788050774072094897971 1838682076161108142346957)
              ·
                refine ⟨689505778560415553380109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1838682076161108142346957 689505778560415553380109)
                ·
                  refine ⟨258564666960155832517541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 689505778560415553380109 258564666960155832517541)
                  ·
                    rfl

theorem cell20_566497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_566497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566497 prefixEnd_566497 := by exact prefixLift 566497
  have htrace : WordTrace (prefixWord ++ tailWord_566497) baseStart_566497 baseEnd_566497 := by
    simpa [prefixWord, tailWord_566497, baseEnd_566497] using wordTrace_append hprefix tailTrace_566497
  have hstable : (prefixWord ++ tailWord_566497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566497).length < 2 ^ (prefixWord ++ tailWord_566497).sum := by decide
  have hdescent : baseEnd_566497 < baseStart_566497 := by decide
  rcases family_descends (prefixWord ++ tailWord_566497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566563 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 6]
def baseStart_566563 : Nat := 118140960795 + 566563 * 2 ^ 59
def prefixEnd_566563 : Nat := 4983230072969 + 3 ^ 40 * 566563 * 2
def baseEnd_566563 : Nat := 258594791158552936317271

theorem tailTrace_566563 : CollatzResearch.WordTrace tailWord_566563 prefixEnd_566563 258594791158552936317271 := by
  unfold tailWord_566563
  simp only [CollatzResearch.WordTrace]
  refine ⟨20664250246446487101952343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13776166830964324734634895 20664250246446487101952343)
  ·
    refine ⟨30996375369669730652928515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20664250246446487101952343 30996375369669730652928515)
    ·
      refine ⟨46494563054504595979392773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30996375369669730652928515 46494563054504595979392773)
      ·
        refine ⟨8717730572719611746136145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46494563054504595979392773 8717730572719611746136145)
        ·
          refine ⟨6538297929539708809602109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8717730572719611746136145 6538297929539708809602109)
          ·
            refine ⟨2451861723577390803600791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6538297929539708809602109 2451861723577390803600791)
            ·
              refine ⟨3677792585366086205401187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2451861723577390803600791 3677792585366086205401187)
              ·
                refine ⟨5516688878049129308101781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3677792585366086205401187 5516688878049129308101781)
                ·
                  refine ⟨258594791158552936317271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5516688878049129308101781 258594791158552936317271)
                  ·
                    rfl

theorem cell20_566563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_566563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566563 prefixEnd_566563 := by exact prefixLift 566563
  have htrace : WordTrace (prefixWord ++ tailWord_566563) baseStart_566563 baseEnd_566563 := by
    simpa [prefixWord, tailWord_566563, baseEnd_566563] using wordTrace_append hprefix tailTrace_566563
  have hstable : (prefixWord ++ tailWord_566563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566563).length < 2 ^ (prefixWord ++ tailWord_566563).sum := by decide
  have hdescent : baseEnd_566563 < baseStart_566563 := by decide
  rcases family_descends (prefixWord ++ tailWord_566563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566580 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 6]
def baseStart_566580 : Nat := 118140960795 + 566580 * 2 ^ 59
def prefixEnd_566580 : Nat := 4983230072969 + 3 ^ 40 * 566580 * 2
def baseEnd_566580 : Nat := 258602550421776432750535

theorem tailTrace_566580 : CollatzResearch.WordTrace tailWord_566580 prefixEnd_566580 258602550421776432750535 := by
  unfold tailWord_566580
  simp only [CollatzResearch.WordTrace]
  refine ⟨10332435143692449502660597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13776580191589932670214129 10332435143692449502660597)
  ·
    refine ⟨968665794721167140874431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10332435143692449502660597 968665794721167140874431)
    ·
      refine ⟨1452998692081750711311647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 968665794721167140874431 1452998692081750711311647)
      ·
        refine ⟨2179498038122626066967471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1452998692081750711311647 2179498038122626066967471)
        ·
          refine ⟨3269247057183939100451207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2179498038122626066967471 3269247057183939100451207)
          ·
            refine ⟨4903870585775908650676811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3269247057183939100451207 4903870585775908650676811)
            ·
              refine ⟨7355805878663862976015217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4903870585775908650676811 7355805878663862976015217)
              ·
                refine ⟨5516854408997897232011413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7355805878663862976015217 5516854408997897232011413)
                ·
                  refine ⟨258602550421776432750535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5516854408997897232011413 258602550421776432750535)
                  ·
                    rfl

theorem cell20_566580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_566580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566580 prefixEnd_566580 := by exact prefixLift 566580
  have htrace : WordTrace (prefixWord ++ tailWord_566580) baseStart_566580 baseEnd_566580 := by
    simpa [prefixWord, tailWord_566580, baseEnd_566580] using wordTrace_append hprefix tailTrace_566580
  have hstable : (prefixWord ++ tailWord_566580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566580).length < 2 ^ (prefixWord ++ tailWord_566580).sum := by decide
  have hdescent : baseEnd_566580 < baseStart_566580 := by decide
  rcases family_descends (prefixWord ++ tailWord_566580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566601 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 4]
def baseStart_566601 : Nat := 118140960795 + 566601 * 2 ^ 59
def prefixEnd_566601 : Nat := 4983230072969 + 3 ^ 40 * 566601 * 2
def baseEnd_566601 : Nat := 258612135393993693050449

theorem tailTrace_566601 : CollatzResearch.WordTrace tailWord_566601 prefixEnd_566601 258612135393993693050449 := by
  unfold tailWord_566601
  simp only [CollatzResearch.WordTrace]
  refine ⟨20665636220308819591835657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13777090813539213061223771 20665636220308819591835657)
  ·
    refine ⟨15499227165231614693876743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20665636220308819591835657 15499227165231614693876743)
    ·
      refine ⟨23248840747847422040815115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15499227165231614693876743 23248840747847422040815115)
      ·
        refine ⟨34873261121771133061222673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23248840747847422040815115 34873261121771133061222673)
        ·
          refine ⟨26154945841328349795917005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34873261121771133061222673 26154945841328349795917005)
          ·
            refine ⟨9808104690498131173468877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26154945841328349795917005 9808104690498131173468877)
            ·
              refine ⟨3678039258936799190050829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9808104690498131173468877 3678039258936799190050829)
              ·
                refine ⟨1379264722101299696269061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3678039258936799190050829 1379264722101299696269061)
                ·
                  refine ⟨258612135393993693050449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1379264722101299696269061 258612135393993693050449)
                  ·
                    rfl

theorem cell20_566601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_566601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566601 prefixEnd_566601 := by exact prefixLift 566601
  have htrace : WordTrace (prefixWord ++ tailWord_566601) baseStart_566601 baseEnd_566601 := by
    simpa [prefixWord, tailWord_566601, baseEnd_566601] using wordTrace_append hprefix tailTrace_566601
  have hstable : (prefixWord ++ tailWord_566601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566601).length < 2 ^ (prefixWord ++ tailWord_566601).sum := by decide
  have hdescent : baseEnd_566601 < baseStart_566601 := by decide
  rcases family_descends (prefixWord ++ tailWord_566601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566608 : List Nat := [2, 1, 1, 1, 1, 5, 2, 7]
def baseStart_566608 : Nat := 118140960795 + 566608 * 2 ^ 59
def prefixEnd_566608 : Nat := 4983230072969 + 3 ^ 40 * 566608 * 2
def baseEnd_566608 : Nat := 86205110128244259939029

theorem tailTrace_566608 : CollatzResearch.WordTrace tailWord_566608 prefixEnd_566608 86205110128244259939029 := by
  unfold tailWord_566608
  simp only [CollatzResearch.WordTrace]
  refine ⟨10332945765641729893670239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13777261020855639858226985 10332945765641729893670239)
  ·
    refine ⟨15499418648462594840505359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10332945765641729893670239 15499418648462594840505359)
    ·
      refine ⟨23249127972693892260758039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15499418648462594840505359 23249127972693892260758039)
      ·
        refine ⟨34873691959040838391137059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23249127972693892260758039 34873691959040838391137059)
        ·
          refine ⟨52310537938561257586705589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34873691959040838391137059 52310537938561257586705589)
          ·
            refine ⟨4904112931740117898753649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52310537938561257586705589 4904112931740117898753649)
            ·
              refine ⟨3678084698805088424065237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4904112931740117898753649 3678084698805088424065237)
              ·
                refine ⟨86205110128244259939029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3678084698805088424065237 86205110128244259939029)
                ·
                  rfl

theorem cell20_566608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_566608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566608 prefixEnd_566608 := by exact prefixLift 566608
  have htrace : WordTrace (prefixWord ++ tailWord_566608) baseStart_566608 baseEnd_566608 := by
    simpa [prefixWord, tailWord_566608, baseEnd_566608] using wordTrace_append hprefix tailTrace_566608
  have hstable : (prefixWord ++ tailWord_566608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566608).length < 2 ^ (prefixWord ++ tailWord_566608).sum := by decide
  have hdescent : baseEnd_566608 < baseStart_566608 := by decide
  rcases family_descends (prefixWord ++ tailWord_566608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566611 : List Nat := [1, 1, 1, 2, 1, 1, 9, 1, 3]
def baseStart_566611 : Nat := 118140960795 + 566611 * 2 ^ 59
def prefixEnd_566611 : Nat := 4983230072969 + 3 ^ 40 * 566611 * 2
def baseEnd_566611 : Nat := 258616699666478102717075

theorem tailTrace_566611 : CollatzResearch.WordTrace tailWord_566611 prefixEnd_566611 258616699666478102717075 := by
  unfold tailWord_566611
  simp only [CollatzResearch.WordTrace]
  refine ⟨20666000950272591299699687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13777333966848394199799791 20666000950272591299699687)
  ·
    refine ⟨30999001425408886949549531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20666000950272591299699687 30999001425408886949549531)
    ·
      refine ⟨46498502138113330424324297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30999001425408886949549531 46498502138113330424324297)
      ·
        refine ⟨34873876603584997818243223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46498502138113330424324297 34873876603584997818243223)
        ·
          refine ⟨52310814905377496727364835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34873876603584997818243223 52310814905377496727364835)
          ·
            refine ⟨78466222358066245091047253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52310814905377496727364835 78466222358066245091047253)
            ·
              refine ⟨459763021629294404830355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 78466222358066245091047253 459763021629294404830355)
              ·
                refine ⟨689644532443941607245533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459763021629294404830355 689644532443941607245533)
                ·
                  refine ⟨258616699666478102717075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 689644532443941607245533 258616699666478102717075)
                  ·
                    rfl

theorem cell20_566611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 3].length) (baseStart_566611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566611 prefixEnd_566611 := by exact prefixLift 566611
  have htrace : WordTrace (prefixWord ++ tailWord_566611) baseStart_566611 baseEnd_566611 := by
    simpa [prefixWord, tailWord_566611, baseEnd_566611] using wordTrace_append hprefix tailTrace_566611
  have hstable : (prefixWord ++ tailWord_566611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566611).length < 2 ^ (prefixWord ++ tailWord_566611).sum := by decide
  have hdescent : baseEnd_566611 < baseStart_566611 := by decide
  rcases family_descends (prefixWord ++ tailWord_566611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566631 : List Nat := [1, 1, 5, 1, 5, 1, 1, 3, 2]
def baseStart_566631 : Nat := 118140960795 + 566631 * 2 ^ 59
def prefixEnd_566631 : Nat := 4983230072969 + 3 ^ 40 * 566631 * 2
def baseEnd_566631 : Nat := 258625828211446922050327

theorem tailTrace_566631 : CollatzResearch.WordTrace tailWord_566631 prefixEnd_566631 258625828211446922050327 := by
  unfold tailWord_566631
  simp only [CollatzResearch.WordTrace]
  refine ⟨20666730410200134715427747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13777820273466756476951831 20666730410200134715427747)
  ·
    refine ⟨31000095615300202073141621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20666730410200134715427747 31000095615300202073141621)
    ·
      refine ⟨2906258963934393944357027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31000095615300202073141621 2906258963934393944357027)
      ·
        refine ⟨4359388445901590916535541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2906258963934393944357027 4359388445901590916535541)
        ·
          refine ⟨408692666803274148425207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4359388445901590916535541 408692666803274148425207)
          ·
            refine ⟨613039000204911222637811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408692666803274148425207 613039000204911222637811)
            ·
              refine ⟨919558500307366833956717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613039000204911222637811 919558500307366833956717)
              ·
                refine ⟨344834437615262562733769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 919558500307366833956717 344834437615262562733769)
                ·
                  refine ⟨258625828211446922050327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344834437615262562733769 258625828211446922050327)
                  ·
                    rfl

theorem cell20_566631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 2].length) (baseStart_566631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566631 prefixEnd_566631 := by exact prefixLift 566631
  have htrace : WordTrace (prefixWord ++ tailWord_566631) baseStart_566631 baseEnd_566631 := by
    simpa [prefixWord, tailWord_566631, baseEnd_566631] using wordTrace_append hprefix tailTrace_566631
  have hstable : (prefixWord ++ tailWord_566631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566631).length < 2 ^ (prefixWord ++ tailWord_566631).sum := by decide
  have hdescent : baseEnd_566631 < baseStart_566631 := by decide
  rcases family_descends (prefixWord ++ tailWord_566631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566656 : List Nat := [2, 1, 1, 2, 1, 2, 1, 8, 2]
def baseStart_566656 : Nat := 118140960795 + 566656 * 2 ^ 59
def prefixEnd_566656 : Nat := 4983230072969 + 3 ^ 40 * 566656 * 2
def baseEnd_566656 : Nat := 258637238892657946216891

theorem tailTrace_566656 : CollatzResearch.WordTrace tailWord_566656 prefixEnd_566656 258637238892657946216891 := by
  unfold tailWord_566656
  simp only [CollatzResearch.WordTrace]
  refine ⟨10333821117554781992543911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13778428156739709323391881 10333821117554781992543911)
  ·
    refine ⟨15500731676332172988815867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10333821117554781992543911 15500731676332172988815867)
    ·
      refine ⟨23251097514498259483223801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15500731676332172988815867 23251097514498259483223801)
      ·
        refine ⟨17438323135873694612417851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23251097514498259483223801 17438323135873694612417851)
        ·
          refine ⟨26157484703810541918626777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17438323135873694612417851 26157484703810541918626777)
          ·
            refine ⟨19618113527857906438970083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26157484703810541918626777 19618113527857906438970083)
            ·
              refine ⟨29427170291786859658455125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19618113527857906438970083 29427170291786859658455125)
              ·
                refine ⟨344849651856877261622521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 29427170291786859658455125 344849651856877261622521)
                ·
                  refine ⟨258637238892657946216891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344849651856877261622521 258637238892657946216891)
                  ·
                    rfl

theorem cell20_566656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 2].length) (baseStart_566656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566656 prefixEnd_566656 := by exact prefixLift 566656
  have htrace : WordTrace (prefixWord ++ tailWord_566656) baseStart_566656 baseEnd_566656 := by
    simpa [prefixWord, tailWord_566656, baseEnd_566656] using wordTrace_append hprefix tailTrace_566656
  have hstable : (prefixWord ++ tailWord_566656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566656).length < 2 ^ (prefixWord ++ tailWord_566656).sum := by decide
  have hdescent : baseEnd_566656 < baseStart_566656 := by decide
  rcases family_descends (prefixWord ++ tailWord_566656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566663 : List Nat := [1, 1, 4, 2, 2, 3, 2, 5]
def baseStart_566663 : Nat := 118140960795 + 566663 * 2 ^ 59
def prefixEnd_566663 : Nat := 4983230072969 + 3 ^ 40 * 566663 * 2
def baseEnd_566663 : Nat := 86213477961132344327843

theorem tailTrace_566663 : CollatzResearch.WordTrace tailWord_566663 prefixEnd_566663 86213477961132344327843 := by
  unfold tailWord_566663
  simp only [CollatzResearch.WordTrace]
  refine ⟨20667897546084204180592643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13778598364056136120395095 20667897546084204180592643)
  ·
    refine ⟨31001846319126306270888965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20667897546084204180592643 31001846319126306270888965)
    ·
      refine ⟨5812846184836182425791681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31001846319126306270888965 5812846184836182425791681)
      ·
        refine ⟨4359634638627136819343761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5812846184836182425791681 4359634638627136819343761)
        ·
          refine ⟨3269725978970352614507821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4359634638627136819343761 3269725978970352614507821)
          ·
            refine ⟨1226147242113882230440433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3269725978970352614507821 1226147242113882230440433)
            ·
              refine ⟨919610431585411672830325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1226147242113882230440433 919610431585411672830325)
              ·
                refine ⟨86213477961132344327843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 919610431585411672830325 86213477961132344327843)
                ·
                  rfl

theorem cell20_566663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 5].length) (baseStart_566663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566663 prefixEnd_566663 := by exact prefixLift 566663
  have htrace : WordTrace (prefixWord ++ tailWord_566663) baseStart_566663 baseEnd_566663 := by
    simpa [prefixWord, tailWord_566663, baseEnd_566663] using wordTrace_append hprefix tailTrace_566663
  have hstable : (prefixWord ++ tailWord_566663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566663).length < 2 ^ (prefixWord ++ tailWord_566663).sum := by decide
  have hdescent : baseEnd_566663 < baseStart_566663 := by decide
  rcases family_descends (prefixWord ++ tailWord_566663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566677 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 4]
def baseStart_566677 : Nat := 118140960795 + 566677 * 2 ^ 59
def prefixEnd_566677 : Nat := 4983230072969 + 3 ^ 40 * 566677 * 2
def baseEnd_566677 : Nat := 258646823864875206516805

theorem tailTrace_566677 : CollatzResearch.WordTrace tailWord_566677 prefixEnd_566677 258646823864875206516805 := by
  unfold tailWord_566677
  simp only [CollatzResearch.WordTrace]
  refine ⟨20668408168033484571602285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13778938778688989714401523 20668408168033484571602285)
  ·
    refine ⟨7750653063012556714350857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20668408168033484571602285 7750653063012556714350857)
    ·
      refine ⟨5812989797259417535763143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7750653063012556714350857 5812989797259417535763143)
      ·
        refine ⟨8719484695889126303644715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5812989797259417535763143 8719484695889126303644715)
        ·
          refine ⟨13079227043833689455467073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8719484695889126303644715 13079227043833689455467073)
          ·
            refine ⟨9809420282875267091600305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13079227043833689455467073 9809420282875267091600305)
            ·
              refine ⟨7357065212156450318700229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9809420282875267091600305 7357065212156450318700229)
              ·
                refine ⟨1379449727279334434756293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7357065212156450318700229 1379449727279334434756293)
                ·
                  refine ⟨258646823864875206516805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1379449727279334434756293 258646823864875206516805)
                  ·
                    rfl

theorem cell20_566677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_566677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566677 prefixEnd_566677 := by exact prefixLift 566677
  have htrace : WordTrace (prefixWord ++ tailWord_566677) baseStart_566677 baseEnd_566677 := by
    simpa [prefixWord, tailWord_566677, baseEnd_566677] using wordTrace_append hprefix tailTrace_566677
  have hstable : (prefixWord ++ tailWord_566677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566677).length < 2 ^ (prefixWord ++ tailWord_566677).sum := by decide
  have hdescent : baseEnd_566677 < baseStart_566677 := by decide
  rcases family_descends (prefixWord ++ tailWord_566677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566701 : List Nat := [1, 5, 2, 2, 1, 9]
def baseStart_566701 : Nat := 118140960795 + 566701 * 2 ^ 59
def prefixEnd_566701 : Nat := 4983230072969 + 3 ^ 40 * 566701 * 2
def baseEnd_566701 : Nat := 9579917708105103322841

theorem tailTrace_566701 : CollatzResearch.WordTrace tailWord_566701 prefixEnd_566701 9579917708105103322841 := by
  unfold tailWord_566701
  simp only [CollatzResearch.WordTrace]
  refine ⟨20669283519946536670475957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13779522346631024446983971 20669283519946536670475957)
  ·
    refine ⟨1937745329994987812857121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20669283519946536670475957 1937745329994987812857121)
    ·
      refine ⟨1453308997496240859642841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1937745329994987812857121 1453308997496240859642841)
      ·
        refine ⟨1089981748122180644732131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1453308997496240859642841 1089981748122180644732131)
        ·
          refine ⟨1634972622183270967098197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089981748122180644732131 1634972622183270967098197)
          ·
            refine ⟨9579917708105103322841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1634972622183270967098197 9579917708105103322841)
            ·
              rfl

theorem cell20_566701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 9].length) (baseStart_566701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566701 prefixEnd_566701 := by exact prefixLift 566701
  have htrace : WordTrace (prefixWord ++ tailWord_566701) baseStart_566701 baseEnd_566701 := by
    simpa [prefixWord, tailWord_566701, baseEnd_566701] using wordTrace_append hprefix tailTrace_566701
  have hstable : (prefixWord ++ tailWord_566701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566701).length < 2 ^ (prefixWord ++ tailWord_566701).sum := by decide
  have hdescent : baseEnd_566701 < baseStart_566701 := by decide
  rcases family_descends (prefixWord ++ tailWord_566701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566729 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 7]
def baseStart_566729 : Nat := 118140960795 + 566729 * 2 ^ 59
def prefixEnd_566729 : Nat := 4983230072969 + 3 ^ 40 * 566729 * 2
def baseEnd_566729 : Nat := 258670558081794136783259

theorem tailTrace_566729 : CollatzResearch.WordTrace tailWord_566729 prefixEnd_566729 258670558081794136783259 := by
  unfold tailWord_566729
  simp only [CollatzResearch.WordTrace]
  refine ⟨20670304763845097452495241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13780203175896731634996827 20670304763845097452495241)
  ·
    refine ⟨15502728572883823089371431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20670304763845097452495241 15502728572883823089371431)
    ·
      refine ⟨23254092859325734634057147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15502728572883823089371431 23254092859325734634057147)
      ·
        refine ⟨34881139288988601951085721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23254092859325734634057147 34881139288988601951085721)
        ·
          refine ⟨26160854466741451463314291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34881139288988601951085721 26160854466741451463314291)
          ·
            refine ⟨39241281700112177194971437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26160854466741451463314291 39241281700112177194971437)
            ·
              refine ⟨14715480637542066448114289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39241281700112177194971437 14715480637542066448114289)
              ·
                refine ⟨11036610478156549836085717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14715480637542066448114289 11036610478156549836085717)
                ·
                  refine ⟨258670558081794136783259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11036610478156549836085717 258670558081794136783259)
                  ·
                    rfl

theorem cell20_566729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_566729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566729 prefixEnd_566729 := by exact prefixLift 566729
  have htrace : WordTrace (prefixWord ++ tailWord_566729) baseStart_566729 baseEnd_566729 := by
    simpa [prefixWord, tailWord_566729, baseEnd_566729] using wordTrace_append hprefix tailTrace_566729
  have hstable : (prefixWord ++ tailWord_566729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566729).length < 2 ^ (prefixWord ++ tailWord_566729).sum := by decide
  have hdescent : baseEnd_566729 < baseStart_566729 := by decide
  rcases family_descends (prefixWord ++ tailWord_566729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566732 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 4]
def baseStart_566732 : Nat := 118140960795 + 566732 * 2 ^ 59
def prefixEnd_566732 : Nat := 4983230072969 + 3 ^ 40 * 566732 * 2
def baseEnd_566732 : Nat := 258671927363539459683247

theorem tailTrace_566732 : CollatzResearch.WordTrace tailWord_566732 prefixEnd_566732 258671927363539459683247 := by
  unfold tailWord_566732
  simp only [CollatzResearch.WordTrace]
  refine ⟨10335207091417114482427225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13780276121889485976569633 10335207091417114482427225)
  ·
    refine ⟨7751405318562835861820419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10335207091417114482427225 7751405318562835861820419)
    ·
      refine ⟨11627107977844253792730629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7751405318562835861820419 11627107977844253792730629)
      ·
        refine ⟨2180082745845797586136993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11627107977844253792730629 2180082745845797586136993)
        ·
          refine ⟨1635062059384348189602745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2180082745845797586136993 1635062059384348189602745)
          ·
            refine ⟨1226296544538261142202059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1635062059384348189602745 1226296544538261142202059)
            ·
              refine ⟨1839444816807391713303089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226296544538261142202059 1839444816807391713303089)
              ·
                refine ⟨1379583612605543784977317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1839444816807391713303089 1379583612605543784977317)
                ·
                  refine ⟨258671927363539459683247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1379583612605543784977317 258671927363539459683247)
                  ·
                    rfl

theorem cell20_566732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_566732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566732 prefixEnd_566732 := by exact prefixLift 566732
  have htrace : WordTrace (prefixWord ++ tailWord_566732) baseStart_566732 baseEnd_566732 := by
    simpa [prefixWord, tailWord_566732, baseEnd_566732] using wordTrace_append hprefix tailTrace_566732
  have hstable : (prefixWord ++ tailWord_566732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566732).length < 2 ^ (prefixWord ++ tailWord_566732).sum := by decide
  have hdescent : baseEnd_566732 < baseStart_566732 := by decide
  rcases family_descends (prefixWord ++ tailWord_566732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566749 : List Nat := [1, 4, 3, 1, 1, 2, 1, 5, 2]
def baseStart_566749 : Nat := 118140960795 + 566749 * 2 ^ 59
def prefixEnd_566749 : Nat := 4983230072969 + 3 ^ 40 * 566749 * 2
def baseEnd_566749 : Nat := 258679686626762956116511

theorem tailTrace_566749 : CollatzResearch.WordTrace tailWord_566749 prefixEnd_566749 258679686626762956116511 := by
  unfold tailWord_566749
  simp only [CollatzResearch.WordTrace]
  refine ⟨20671034223772640868223301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13780689482515093912148867 20671034223772640868223301)
  ·
    refine ⟨3875818916957370162791869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20671034223772640868223301 3875818916957370162791869)
    ·
      refine ⟨1453432093859013811046951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3875818916957370162791869 1453432093859013811046951)
      ·
        refine ⟨2180148140788520716570427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1453432093859013811046951 2180148140788520716570427)
        ·
          refine ⟨3270222211182781074855641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2180148140788520716570427 3270222211182781074855641)
          ·
            refine ⟨2452666658387085806141731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3270222211182781074855641 2452666658387085806141731)
            ·
              refine ⟨3678999987580628709212597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2452666658387085806141731 3678999987580628709212597)
              ·
                refine ⟨344906248835683941488681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3678999987580628709212597 344906248835683941488681)
                ·
                  refine ⟨258679686626762956116511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344906248835683941488681 258679686626762956116511)
                  ·
                    rfl

theorem cell20_566749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_566749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566749 prefixEnd_566749 := by exact prefixLift 566749
  have htrace : WordTrace (prefixWord ++ tailWord_566749) baseStart_566749 baseEnd_566749 := by
    simpa [prefixWord, tailWord_566749, baseEnd_566749] using wordTrace_append hprefix tailTrace_566749
  have hstable : (prefixWord ++ tailWord_566749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566749).length < 2 ^ (prefixWord ++ tailWord_566749).sum := by decide
  have hdescent : baseEnd_566749 < baseStart_566749 := by decide
  rcases family_descends (prefixWord ++ tailWord_566749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566760 : List Nat := [2, 1, 4, 1, 1, 2, 9]
def baseStart_566760 : Nat := 118140960795 + 566760 * 2 ^ 59
def prefixEnd_566760 : Nat := 4983230072969 + 3 ^ 40 * 566760 * 2
def baseEnd_566760 : Nat := 28742745258499534083311

theorem tailTrace_566760 : CollatzResearch.WordTrace tailWord_566760 prefixEnd_566760 28742745258499534083311 := by
  unfold tailWord_566760
  simp only [CollatzResearch.WordTrace]
  refine ⟨10335717713366394873436867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13780956951155193164582489 10335717713366394873436867)
  ·
    refine ⟨15503576570049592310155301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10335717713366394873436867 15503576570049592310155301)
    ·
      refine ⟨2906920606884298558154119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15503576570049592310155301 2906920606884298558154119)
      ·
        refine ⟨4360380910326447837231179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2906920606884298558154119 4360380910326447837231179)
        ·
          refine ⟨6540571365489671755846769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4360380910326447837231179 6540571365489671755846769)
          ·
            refine ⟨4905428524117253816885077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6540571365489671755846769 4905428524117253816885077)
            ·
              refine ⟨28742745258499534083311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4905428524117253816885077 28742745258499534083311)
              ·
                rfl

theorem cell20_566760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 9].length) (baseStart_566760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566760 prefixEnd_566760 := by exact prefixLift 566760
  have htrace : WordTrace (prefixWord ++ tailWord_566760) baseStart_566760 baseEnd_566760 := by
    simpa [prefixWord, tailWord_566760, baseEnd_566760] using wordTrace_append hprefix tailTrace_566760
  have hstable : (prefixWord ++ tailWord_566760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566760).length < 2 ^ (prefixWord ++ tailWord_566760).sum := by decide
  have hdescent : baseEnd_566760 < baseStart_566760 := by decide
  rcases family_descends (prefixWord ++ tailWord_566760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566770 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_566770 : Nat := 118140960795 + 566770 * 2 ^ 59
def prefixEnd_566770 : Nat := 4983230072969 + 3 ^ 40 * 566770 * 2
def baseEnd_566770 : Nat := 258689271598980216416425

theorem tailTrace_566770 : CollatzResearch.WordTrace tailWord_566770 prefixEnd_566770 258689271598980216416425 := by
  unfold tailWord_566770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5167950039174140363684441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13781200104464374303158509 5167950039174140363684441)
  ·
    refine ⟨3875962529380605272763331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5167950039174140363684441 3875962529380605272763331)
    ·
      refine ⟨5813943794070907909144997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3875962529380605272763331 5813943794070907909144997)
      ·
        refine ⟨1090114461388295232964687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5813943794070907909144997 1090114461388295232964687)
        ·
          refine ⟨1635171692082442849447031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1090114461388295232964687 1635171692082442849447031)
          ·
            refine ⟨2452757538123664274170547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1635171692082442849447031 2452757538123664274170547)
            ·
              refine ⟨3679136307185496411255821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2452757538123664274170547 3679136307185496411255821)
              ·
                refine ⟨1379676115194561154220933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3679136307185496411255821 1379676115194561154220933)
                ·
                  refine ⟨258689271598980216416425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1379676115194561154220933 258689271598980216416425)
                  ·
                    rfl

theorem cell20_566770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_566770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566770 prefixEnd_566770 := by exact prefixLift 566770
  have htrace : WordTrace (prefixWord ++ tailWord_566770) baseStart_566770 baseEnd_566770 := by
    simpa [prefixWord, tailWord_566770, baseEnd_566770] using wordTrace_append hprefix tailTrace_566770
  have hstable : (prefixWord ++ tailWord_566770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566770).length < 2 ^ (prefixWord ++ tailWord_566770).sum := by decide
  have hdescent : baseEnd_566770 < baseStart_566770 := by decide
  rcases family_descends (prefixWord ++ tailWord_566770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566790 : List Nat := [6, 2, 1, 1, 2, 1, 1, 6]
def baseStart_566790 : Nat := 118140960795 + 566790 * 2 ^ 59
def prefixEnd_566790 : Nat := 4983230072969 + 3 ^ 40 * 566790 * 2
def baseEnd_566790 : Nat := 86232800047983011916559

theorem tailTrace_566790 : CollatzResearch.WordTrace tailWord_566790 prefixEnd_566790 86232800047983011916559 := by
  unfold tailWord_566790
  simp only [CollatzResearch.WordTrace]
  refine ⟨646016550519503277202057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13781686411082736580310549 646016550519503277202057)
  ·
    refine ⟨484512412889627457901543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 646016550519503277202057 484512412889627457901543)
    ·
      refine ⟨726768619334441186852315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 484512412889627457901543 726768619334441186852315)
      ·
        refine ⟨1090152929001661780278473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726768619334441186852315 1090152929001661780278473)
        ·
          refine ⟨817614696751246335208855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1090152929001661780278473 817614696751246335208855)
          ·
            refine ⟨1226422045126869502813283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817614696751246335208855 1226422045126869502813283)
            ·
              refine ⟨1839633067690304254219925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226422045126869502813283 1839633067690304254219925)
              ·
                refine ⟨86232800047983011916559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1839633067690304254219925 86232800047983011916559)
                ·
                  rfl

theorem cell20_566790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_566790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566790 prefixEnd_566790 := by exact prefixLift 566790
  have htrace : WordTrace (prefixWord ++ tailWord_566790) baseStart_566790 baseEnd_566790 := by
    simpa [prefixWord, tailWord_566790, baseEnd_566790] using wordTrace_append hprefix tailTrace_566790
  have hstable : (prefixWord ++ tailWord_566790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566790).length < 2 ^ (prefixWord ++ tailWord_566790).sum := by decide
  have hdescent : baseEnd_566790 < baseStart_566790 := by decide
  rcases family_descends (prefixWord ++ tailWord_566790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566794 : List Nat := [3, 1, 2, 2, 2, 4, 2, 4]
def baseStart_566794 : Nat := 118140960795 + 566794 * 2 ^ 59
def prefixEnd_566794 : Nat := 4983230072969 + 3 ^ 40 * 566794 * 2
def baseEnd_566794 : Nat := 86233408617647599872109

theorem tailTrace_566794 : CollatzResearch.WordTrace tailWord_566794 prefixEnd_566794 86233408617647599872109 := by
  unfold tailWord_566794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5168168877152403388402859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13781783672406409035740957 5168168877152403388402859)
  ·
    refine ⟨7752253315728605082604289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5168168877152403388402859 7752253315728605082604289)
    ·
      refine ⟨5814189986796453811953217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7752253315728605082604289 5814189986796453811953217)
      ·
        refine ⟨4360642490097340358964913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5814189986796453811953217 4360642490097340358964913)
        ·
          refine ⟨3270481867573005269223685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4360642490097340358964913 3270481867573005269223685)
          ·
            refine ⟨613215350169938487979441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3270481867573005269223685 613215350169938487979441)
            ·
              refine ⟨459911512627453865984581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 613215350169938487979441 459911512627453865984581)
              ·
                refine ⟨86233408617647599872109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 459911512627453865984581 86233408617647599872109)
                ·
                  rfl

theorem cell20_566794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_566794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566794 prefixEnd_566794 := by exact prefixLift 566794
  have htrace : WordTrace (prefixWord ++ tailWord_566794) baseStart_566794 baseEnd_566794 := by
    simpa [prefixWord, tailWord_566794, baseEnd_566794] using wordTrace_append hprefix tailTrace_566794
  have hstable : (prefixWord ++ tailWord_566794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566794).length < 2 ^ (prefixWord ++ tailWord_566794).sum := by decide
  have hdescent : baseEnd_566794 < baseStart_566794 := by decide
  rcases family_descends (prefixWord ++ tailWord_566794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566839 : List Nat := [1, 1, 3, 1, 2, 4, 4, 1, 3]
def baseStart_566839 : Nat := 118140960795 + 566839 * 2 ^ 59
def prefixEnd_566839 : Nat := 4983230072969 + 3 ^ 40 * 566839 * 2
def baseEnd_566839 : Nat := 258720765079122643116143

theorem tailTrace_566839 : CollatzResearch.WordTrace tailWord_566839 prefixEnd_566839 258720765079122643116143 := by
  unfold tailWord_566839
  simp only [CollatzResearch.WordTrace]
  refine ⟨20674316793446586238999571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13782877862297724159333047 20674316793446586238999571)
  ·
    refine ⟨31011475190169879358499357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20674316793446586238999571 31011475190169879358499357)
    ·
      refine ⟨11629303196313704759437259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31011475190169879358499357 11629303196313704759437259)
      ·
        refine ⟨17443954794470557139155889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11629303196313704759437259 17443954794470557139155889)
        ·
          refine ⟨13082966095852917854366917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17443954794470557139155889 13082966095852917854366917)
          ·
            refine ⟨2453056142972422097693797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13082966095852917854366917 2453056142972422097693797)
            ·
              refine ⟨459948026807329143317587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2453056142972422097693797 459948026807329143317587)
              ·
                refine ⟨689922040210993714976381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459948026807329143317587 689922040210993714976381)
                ·
                  refine ⟨258720765079122643116143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 689922040210993714976381 258720765079122643116143)
                  ·
                    rfl

theorem cell20_566839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 3].length) (baseStart_566839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566839 prefixEnd_566839 := by exact prefixLift 566839
  have htrace : WordTrace (prefixWord ++ tailWord_566839) baseStart_566839 baseEnd_566839 := by
    simpa [prefixWord, tailWord_566839, baseEnd_566839] using wordTrace_append hprefix tailTrace_566839
  have hstable : (prefixWord ++ tailWord_566839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566839).length < 2 ^ (prefixWord ++ tailWord_566839).sum := by decide
  have hdescent : baseEnd_566839 < baseStart_566839 := by decide
  rcases family_descends (prefixWord ++ tailWord_566839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566870 : List Nat := [5, 2, 2, 2, 9]
def baseStart_566870 : Nat := 118140960795 + 566870 * 2 ^ 59
def prefixEnd_566870 : Nat := 4983230072969 + 3 ^ 40 * 566870 * 2
def baseEnd_566870 : Nat := 3194258201528695223243

theorem tailTrace_566870 : CollatzResearch.WordTrace tailWord_566870 prefixEnd_566870 3194258201528695223243 := by
  unfold tailWord_566870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1292215466020892408336129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13783631637556185688918709 1292215466020892408336129)
  ·
    refine ⟨969161599515669306252097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1292215466020892408336129 969161599515669306252097)
    ·
      refine ⟨726871199636751979689073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 969161599515669306252097 726871199636751979689073)
      ·
        refine ⟨545153399727563984766805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 726871199636751979689073 545153399727563984766805)
        ·
          refine ⟨3194258201528695223243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 545153399727563984766805 3194258201528695223243)
          ·
            rfl

theorem cell20_566870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 9].length) (baseStart_566870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566870 prefixEnd_566870 := by exact prefixLift 566870
  have htrace : WordTrace (prefixWord ++ tailWord_566870) baseStart_566870 baseEnd_566870 := by
    simpa [prefixWord, tailWord_566870, baseEnd_566870] using wordTrace_append hprefix tailTrace_566870
  have hstable : (prefixWord ++ tailWord_566870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566870).length < 2 ^ (prefixWord ++ tailWord_566870).sum := by decide
  have hdescent : baseEnd_566870 < baseStart_566870 := by decide
  rcases family_descends (prefixWord ++ tailWord_566870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566905 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 4]
def baseStart_566905 : Nat := 118140960795 + 566905 * 2 ^ 59
def prefixEnd_566905 : Nat := 4983230072969 + 3 ^ 40 * 566905 * 2
def baseEnd_566905 : Nat := 258750889277519746915873

theorem tailTrace_566905 : CollatzResearch.WordTrace tailWord_566905 prefixEnd_566905 258750889277519746915873 := by
  unfold tailWord_566905
  simp only [CollatzResearch.WordTrace]
  refine ⟨20676724011207479510902169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13784482674138319673934779 20676724011207479510902169)
  ·
    refine ⟨15507543008405609633176627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20676724011207479510902169 15507543008405609633176627)
    ·
      refine ⟨23261314512608414449764941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15507543008405609633176627 23261314512608414449764941)
      ·
        refine ⟨8722992942228155418661853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23261314512608414449764941 8722992942228155418661853)
        ·
          refine ⟨3271122353335558281998195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8722992942228155418661853 3271122353335558281998195)
          ·
            refine ⟨4906683530003337422997293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3271122353335558281998195 4906683530003337422997293)
            ·
              refine ⟨1840006323751251533623985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4906683530003337422997293 1840006323751251533623985)
              ·
                refine ⟨1380004742813438650217989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1840006323751251533623985 1380004742813438650217989)
                ·
                  refine ⟨258750889277519746915873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1380004742813438650217989 258750889277519746915873)
                  ·
                    rfl

theorem cell20_566905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_566905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566905 prefixEnd_566905 := by exact prefixLift 566905
  have htrace : WordTrace (prefixWord ++ tailWord_566905) baseStart_566905 baseEnd_566905 := by
    simpa [prefixWord, tailWord_566905, baseEnd_566905] using wordTrace_append hprefix tailTrace_566905
  have hstable : (prefixWord ++ tailWord_566905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566905).length < 2 ^ (prefixWord ++ tailWord_566905).sum := by decide
  have hdescent : baseEnd_566905 < baseStart_566905 := by decide
  rcases family_descends (prefixWord ++ tailWord_566905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566936 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 5]
def baseStart_566936 : Nat := 118140960795 + 566936 * 2 ^ 59
def prefixEnd_566936 : Nat := 4983230072969 + 3 ^ 40 * 566936 * 2
def baseEnd_566936 : Nat := 258765038522221416882413

theorem tailTrace_566936 : CollatzResearch.WordTrace tailWord_566936 prefixEnd_566936 258765038522221416882413 := by
  unfold tailWord_566936
  simp only [CollatzResearch.WordTrace]
  refine ⟨10338927337047585902640331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13785236449396781203520441 10338927337047585902640331)
  ·
    refine ⟨15508391005571378853960497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10338927337047585902640331 15508391005571378853960497)
    ·
      refine ⟨11631293254178534140470373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15508391005571378853960497 11631293254178534140470373)
      ·
        refine ⟨2180867485158475151338195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11631293254178534140470373 2180867485158475151338195)
        ·
          refine ⟨3271301227737712727007293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2180867485158475151338195 3271301227737712727007293)
          ·
            refine ⟨1226737960401642272627735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3271301227737712727007293 1226737960401642272627735)
            ·
              refine ⟨1840106940602463408941603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226737960401642272627735 1840106940602463408941603)
              ·
                refine ⟨2760160410903695113412405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840106940602463408941603 2760160410903695113412405)
                ·
                  refine ⟨258765038522221416882413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2760160410903695113412405 258765038522221416882413)
                  ·
                    rfl

theorem cell20_566936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_566936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566936 prefixEnd_566936 := by exact prefixLift 566936
  have htrace : WordTrace (prefixWord ++ tailWord_566936) baseStart_566936 baseEnd_566936 := by
    simpa [prefixWord, tailWord_566936, baseEnd_566936] using wordTrace_append hprefix tailTrace_566936
  have hstable : (prefixWord ++ tailWord_566936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566936).length < 2 ^ (prefixWord ++ tailWord_566936).sum := by decide
  have hdescent : baseEnd_566936 < baseStart_566936 := by decide
  rcases family_descends (prefixWord ++ tailWord_566936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566967 : List Nat := [1, 1, 3, 1, 5, 1, 4, 4]
def baseStart_566967 : Nat := 118140960795 + 566967 * 2 ^ 59
def prefixEnd_566967 : Nat := 4983230072969 + 3 ^ 40 * 566967 * 2
def baseEnd_566967 : Nat := 86259729255641028949651

theorem tailTrace_566967 : CollatzResearch.WordTrace tailWord_566967 prefixEnd_566967 86259729255641028949651 := by
  unfold tailWord_566967
  simp only [CollatzResearch.WordTrace]
  refine ⟨20678985336982864099659155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13785990224655242733106103 20678985336982864099659155)
  ·
    refine ⟨31018478005474296149488733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20678985336982864099659155 31018478005474296149488733)
    ·
      refine ⟨11631929252052861056058275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31018478005474296149488733 11631929252052861056058275)
      ·
        refine ⟨17447893878079291584087413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11631929252052861056058275 17447893878079291584087413)
        ·
          refine ⟨1635740051069933586008195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17447893878079291584087413 1635740051069933586008195)
          ·
            refine ⟨2453610076604900379012293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1635740051069933586008195 2453610076604900379012293)
            ·
              refine ⟨460051889363418821064805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2453610076604900379012293 460051889363418821064805)
              ·
                refine ⟨86259729255641028949651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 460051889363418821064805 86259729255641028949651)
                ·
                  rfl

theorem cell20_566967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 4].length) (baseStart_566967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566967 prefixEnd_566967 := by exact prefixLift 566967
  have htrace : WordTrace (prefixWord ++ tailWord_566967) baseStart_566967 baseEnd_566967 := by
    simpa [prefixWord, tailWord_566967, baseEnd_566967] using wordTrace_append hprefix tailTrace_566967
  have hstable : (prefixWord ++ tailWord_566967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566967).length < 2 ^ (prefixWord ++ tailWord_566967).sum := by decide
  have hdescent : baseEnd_566967 < baseStart_566967 := by decide
  rcases family_descends (prefixWord ++ tailWord_566967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566974 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_566974 : Nat := 118140960795 + 566974 * 2 ^ 59
def prefixEnd_566974 : Nat := 4983230072969 + 3 ^ 40 * 566974 * 2
def baseEnd_566974 : Nat := 258782382757662173615591

theorem tailTrace_566974 : CollatzResearch.WordTrace tailWord_566974 prefixEnd_566974 258782382757662173615591 := by
  unfold tailWord_566974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2584905080994688036895497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13786160431971669530109317 2584905080994688036895497)
  ·
    refine ⟨1938678810746016027671623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2584905080994688036895497 1938678810746016027671623)
    ·
      refine ⟨2908018216119024041507435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1938678810746016027671623 2908018216119024041507435)
      ·
        refine ⟨4362027324178536062261153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2908018216119024041507435 4362027324178536062261153)
        ·
          refine ⟨3271520493133902046695865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4362027324178536062261153 3271520493133902046695865)
          ·
            refine ⟨2453640369850426535021899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3271520493133902046695865 2453640369850426535021899)
            ·
              refine ⟨3680460554775639802532849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453640369850426535021899 3680460554775639802532849)
              ·
                refine ⟨2760345416081729851899637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3680460554775639802532849 2760345416081729851899637)
                ·
                  refine ⟨258782382757662173615591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2760345416081729851899637 258782382757662173615591)
                  ·
                    rfl

theorem cell20_566974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_566974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566974 prefixEnd_566974 := by exact prefixLift 566974
  have htrace : WordTrace (prefixWord ++ tailWord_566974) baseStart_566974 baseEnd_566974 := by
    simpa [prefixWord, tailWord_566974, baseEnd_566974] using wordTrace_append hprefix tailTrace_566974
  have hstable : (prefixWord ++ tailWord_566974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566974).length < 2 ^ (prefixWord ++ tailWord_566974).sum := by decide
  have hdescent : baseEnd_566974 < baseStart_566974 := by decide
  rcases family_descends (prefixWord ++ tailWord_566974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566994 : List Nat := [3, 2, 2, 2, 2, 2, 3, 2, 2]
def baseStart_566994 : Nat := 118140960795 + 566994 * 2 ^ 59
def prefixEnd_566994 : Nat := 4983230072969 + 3 ^ 40 * 566994 * 2
def baseEnd_566994 : Nat := 258791511302630992948843

theorem tailTrace_566994 : CollatzResearch.WordTrace tailWord_566994 prefixEnd_566994 258791511302630992948843 := by
  unfold tailWord_566994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5169992526971261927723009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13786646738590031807261357 5169992526971261927723009)
  ·
    refine ⟨3877494395228446445792257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5169992526971261927723009 3877494395228446445792257)
    ·
      refine ⟨2908120796421334834344193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3877494395228446445792257 2908120796421334834344193)
      ·
        refine ⟨2181090597316001125758145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2908120796421334834344193 2181090597316001125758145)
        ·
          refine ⟨1635817947987000844318609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2181090597316001125758145 1635817947987000844318609)
          ·
            refine ⟨1226863460990250633238957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1635817947987000844318609 1226863460990250633238957)
            ·
              refine ⟨460073797871343987464609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1226863460990250633238957 460073797871343987464609)
              ·
                refine ⟨345055348403507990598457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 460073797871343987464609 345055348403507990598457)
                ·
                  refine ⟨258791511302630992948843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345055348403507990598457 258791511302630992948843)
                  ·
                    rfl

theorem cell20_566994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_566994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_566994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_566994 prefixEnd_566994 := by exact prefixLift 566994
  have htrace : WordTrace (prefixWord ++ tailWord_566994) baseStart_566994 baseEnd_566994 := by
    simpa [prefixWord, tailWord_566994, baseEnd_566994] using wordTrace_append hprefix tailTrace_566994
  have hstable : (prefixWord ++ tailWord_566994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566994).length < 2 ^ (prefixWord ++ tailWord_566994).sum := by decide
  have hdescent : baseEnd_566994 < baseStart_566994 := by decide
  rcases family_descends (prefixWord ++ tailWord_566994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567004 : List Nat := [2, 2, 5, 1, 3, 1, 2, 1, 3]
def baseStart_567004 : Nat := 118140960795 + 567004 * 2 ^ 59
def prefixEnd_567004 : Nat := 4983230072969 + 3 ^ 40 * 567004 * 2
def baseEnd_567004 : Nat := 258796075575115402615469

theorem tailTrace_567004 : CollatzResearch.WordTrace tailWord_567004 prefixEnd_567004 258796075575115402615469 := by
  unfold tailWord_567004
  simp only [CollatzResearch.WordTrace]
  refine ⟨10340167418924409709378033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13786889891899212945837377 10340167418924409709378033)
  ·
    refine ⟨7755125564193307282033525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10340167418924409709378033 7755125564193307282033525)
    ·
      refine ⟨727043021643122557690643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7755125564193307282033525 727043021643122557690643)
      ·
        refine ⟨1090564532464683836535965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 727043021643122557690643 1090564532464683836535965)
        ·
          refine ⟨408961699674256438700987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1090564532464683836535965 408961699674256438700987)
          ·
            refine ⟨613442549511384658051481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408961699674256438700987 613442549511384658051481)
            ·
              refine ⟨460081912133538493538611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 613442549511384658051481 460081912133538493538611)
              ·
                refine ⟨690122868200307740307917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460081912133538493538611 690122868200307740307917)
                ·
                  refine ⟨258796075575115402615469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 690122868200307740307917 258796075575115402615469)
                  ·
                    rfl

theorem cell20_567004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_567004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567004 prefixEnd_567004 := by exact prefixLift 567004
  have htrace : WordTrace (prefixWord ++ tailWord_567004) baseStart_567004 baseEnd_567004 := by
    simpa [prefixWord, tailWord_567004, baseEnd_567004] using wordTrace_append hprefix tailTrace_567004
  have hstable : (prefixWord ++ tailWord_567004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567004).length < 2 ^ (prefixWord ++ tailWord_567004).sum := by decide
  have hdescent : baseEnd_567004 < baseStart_567004 := by decide
  rcases family_descends (prefixWord ++ tailWord_567004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567012 : List Nat := [2, 3, 1, 1, 1, 3, 3, 3, 3]
def baseStart_567012 : Nat := 118140960795 + 567012 * 2 ^ 59
def prefixEnd_567012 : Nat := 4983230072969 + 3 ^ 40 * 567012 * 2
def baseEnd_567012 : Nat := 258799726993102930348769

theorem tailTrace_567012 : CollatzResearch.WordTrace tailWord_567012 prefixEnd_567012 258799726993102930348769 := by
  unfold tailWord_567012
  simp only [CollatzResearch.WordTrace]
  refine ⟨10340313310909918392523645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13787084414546557856698193 10340313310909918392523645)
  ·
    refine ⟨3877617491591219397196367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10340313310909918392523645 3877617491591219397196367)
    ·
      refine ⟨5816426237386829095794551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3877617491591219397196367 5816426237386829095794551)
      ·
        refine ⟨8724639356080243643691827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5816426237386829095794551 8724639356080243643691827)
        ·
          refine ⟨13086959034120365465537741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8724639356080243643691827 13086959034120365465537741)
          ·
            refine ⟨4907609637795137049576653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13086959034120365465537741 4907609637795137049576653)
            ·
              refine ⟨1840353614173176393591245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4907609637795137049576653 1840353614173176393591245)
              ·
                refine ⟨690132605314941147596717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1840353614173176393591245 690132605314941147596717)
                ·
                  refine ⟨258799726993102930348769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 690132605314941147596717 258799726993102930348769)
                  ·
                    rfl

theorem cell20_567012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_567012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567012 prefixEnd_567012 := by exact prefixLift 567012
  have htrace : WordTrace (prefixWord ++ tailWord_567012) baseStart_567012 baseEnd_567012 := by
    simpa [prefixWord, tailWord_567012, baseEnd_567012] using wordTrace_append hprefix tailTrace_567012
  have hstable : (prefixWord ++ tailWord_567012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567012).length < 2 ^ (prefixWord ++ tailWord_567012).sum := by decide
  have hdescent : baseEnd_567012 < baseStart_567012 := by decide
  rcases family_descends (prefixWord ++ tailWord_567012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567026 : List Nat := [3, 2, 1, 3, 1, 1, 1, 8]
def baseStart_567026 : Nat := 118140960795 + 567026 * 2 ^ 59
def prefixEnd_567026 : Nat := 4983230072969 + 3 ^ 40 * 567026 * 2
def baseEnd_567026 : Nat := 86268705658193701294015

theorem tailTrace_567026 : CollatzResearch.WordTrace tailWord_567026 prefixEnd_567026 86268705658193701294015 := by
  unfold tailWord_567026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5170284310942279294014233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13787424829179411450704621 5170284310942279294014233)
  ·
    refine ⟨3877713233206709470510675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5170284310942279294014233 3877713233206709470510675)
    ·
      refine ⟨5816569849810064205766013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3877713233206709470510675 5816569849810064205766013)
      ·
        refine ⟨2181213693678774077162255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5816569849810064205766013 2181213693678774077162255)
        ·
          refine ⟨3271820540518161115743383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2181213693678774077162255 3271820540518161115743383)
          ·
            refine ⟨4907730810777241673615075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3271820540518161115743383 4907730810777241673615075)
            ·
              refine ⟨7361596216165862510422613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4907730810777241673615075 7361596216165862510422613)
              ·
                refine ⟨86268705658193701294015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7361596216165862510422613 86268705658193701294015)
                ·
                  rfl

theorem cell20_567026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_567026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567026 prefixEnd_567026 := by exact prefixLift 567026
  have htrace : WordTrace (prefixWord ++ tailWord_567026) baseStart_567026 baseEnd_567026 := by
    simpa [prefixWord, tailWord_567026, baseEnd_567026] using wordTrace_append hprefix tailTrace_567026
  have hstable : (prefixWord ++ tailWord_567026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567026).length < 2 ^ (prefixWord ++ tailWord_567026).sum := by decide
  have hdescent : baseEnd_567026 < baseStart_567026 := by decide
  rcases family_descends (prefixWord ++ tailWord_567026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567036 : List Nat := [2, 2, 2, 1, 3, 1, 2, 5, 2]
def baseStart_567036 : Nat := 118140960795 + 567036 * 2 ^ 59
def prefixEnd_567036 : Nat := 4983230072969 + 3 ^ 40 * 567036 * 2
def baseEnd_567036 : Nat := 258810681247065513548671

theorem tailTrace_567036 : CollatzResearch.WordTrace tailWord_567036 prefixEnd_567036 258810681247065513548671 := by
  unfold tailWord_567036
  simp only [CollatzResearch.WordTrace]
  refine ⟨10340750986866444441960481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13787667982488592589280641 10340750986866444441960481)
  ·
    refine ⟨7755563240149833331470361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10340750986866444441960481 7755563240149833331470361)
    ·
      refine ⟨5816672430112374998602771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7755563240149833331470361 5816672430112374998602771)
      ·
        refine ⟨8725008645168562497904157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5816672430112374998602771 8725008645168562497904157)
        ·
          refine ⟨3271878241938210936714059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8725008645168562497904157 3271878241938210936714059)
          ·
            refine ⟨4907817362907316405071089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3271878241938210936714059 4907817362907316405071089)
            ·
              refine ⟨3680863022180487303803317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4907817362907316405071089 3680863022180487303803317)
              ·
                refine ⟨345080908329420684731561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3680863022180487303803317 345080908329420684731561)
                ·
                  refine ⟨258810681247065513548671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345080908329420684731561 258810681247065513548671)
                  ·
                    rfl

theorem cell20_567036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_567036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567036 prefixEnd_567036 := by exact prefixLift 567036
  have htrace : WordTrace (prefixWord ++ tailWord_567036) baseStart_567036 baseEnd_567036 := by
    simpa [prefixWord, tailWord_567036, baseEnd_567036] using wordTrace_append hprefix tailTrace_567036
  have hstable : (prefixWord ++ tailWord_567036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567036).length < 2 ^ (prefixWord ++ tailWord_567036).sum := by decide
  have hdescent : baseEnd_567036 < baseStart_567036 := by decide
  rcases family_descends (prefixWord ++ tailWord_567036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567040 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 6]
def baseStart_567040 : Nat := 118140960795 + 567040 * 2 ^ 59
def prefixEnd_567040 : Nat := 4983230072969 + 3 ^ 40 * 567040 * 2
def baseEnd_567040 : Nat := 258812506956059277415321

theorem tailTrace_567040 : CollatzResearch.WordTrace tailWord_567040 prefixEnd_567040 258812506956059277415321 := by
  unfold tailWord_567040
  simp only [CollatzResearch.WordTrace]
  refine ⟨10340823932859198783533287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13787765243812265044711049 10340823932859198783533287)
  ·
    refine ⟨15511235899288798175299931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10340823932859198783533287 15511235899288798175299931)
    ·
      refine ⟨23266853848933197262949897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15511235899288798175299931 23266853848933197262949897)
      ·
        refine ⟨17450140386699897947212423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23266853848933197262949897 17450140386699897947212423)
        ·
          refine ⟨26175210580049846920818635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17450140386699897947212423 26175210580049846920818635)
          ·
            refine ⟨39262815870074770381227953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26175210580049846920818635 39262815870074770381227953)
            ·
              refine ⟨29447111902556077785920965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39262815870074770381227953 29447111902556077785920965)
              ·
                refine ⟨5521333481729264584860181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29447111902556077785920965 5521333481729264584860181)
                ·
                  refine ⟨258812506956059277415321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5521333481729264584860181 258812506956059277415321)
                  ·
                    rfl

theorem cell20_567040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_567040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567040 prefixEnd_567040 := by exact prefixLift 567040
  have htrace : WordTrace (prefixWord ++ tailWord_567040) baseStart_567040 baseEnd_567040 := by
    simpa [prefixWord, tailWord_567040, baseEnd_567040] using wordTrace_append hprefix tailTrace_567040
  have hstable : (prefixWord ++ tailWord_567040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567040).length < 2 ^ (prefixWord ++ tailWord_567040).sum := by decide
  have hdescent : baseEnd_567040 < baseStart_567040 := by decide
  rcases family_descends (prefixWord ++ tailWord_567040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567050 : List Nat := [3, 1, 2, 2, 1, 3, 1, 4, 3]
def baseStart_567050 : Nat := 118140960795 + 567050 * 2 ^ 59
def prefixEnd_567050 : Nat := 4983230072969 + 3 ^ 40 * 567050 * 2
def baseEnd_567050 : Nat := 258817071228543687081947

theorem tailTrace_567050 : CollatzResearch.WordTrace tailWord_567050 prefixEnd_567050 258817071228543687081947 := by
  unfold tailWord_567050
  simp only [CollatzResearch.WordTrace]
  refine ⟨5170503148920542318732651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13788008397121446183287069 5170503148920542318732651)
  ·
    refine ⟨7755754723380813478098977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5170503148920542318732651 7755754723380813478098977)
    ·
      refine ⟨5816816042535610108574233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7755754723380813478098977 5816816042535610108574233)
      ·
        refine ⟨4362612031901707581430675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5816816042535610108574233 4362612031901707581430675)
        ·
          refine ⟨6543918047852561372146013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4362612031901707581430675 6543918047852561372146013)
          ·
            refine ⟨2453969267944710514554755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6543918047852561372146013 2453969267944710514554755)
            ·
              refine ⟨3680953901917065771832133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453969267944710514554755 3680953901917065771832133)
              ·
                refine ⟨690178856609449832218525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3680953901917065771832133 690178856609449832218525)
                ·
                  refine ⟨258817071228543687081947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 690178856609449832218525 258817071228543687081947)
                  ·
                    rfl

theorem cell20_567050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_567050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567050 prefixEnd_567050 := by exact prefixLift 567050
  have htrace : WordTrace (prefixWord ++ tailWord_567050) baseStart_567050 baseEnd_567050 := by
    simpa [prefixWord, tailWord_567050, baseEnd_567050] using wordTrace_append hprefix tailTrace_567050
  have hstable : (prefixWord ++ tailWord_567050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567050).length < 2 ^ (prefixWord ++ tailWord_567050).sum := by decide
  have hdescent : baseEnd_567050 < baseStart_567050 := by decide
  rcases family_descends (prefixWord ++ tailWord_567050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567064 : List Nat := [2, 1, 2, 3, 1, 1, 5, 5]
def baseStart_567064 : Nat := 118140960795 + 567064 * 2 ^ 59
def prefixEnd_567064 : Nat := 4983230072969 + 3 ^ 40 * 567064 * 2
def baseEnd_567064 : Nat := 86274487070007286871741

theorem tailTrace_567064 : CollatzResearch.WordTrace tailWord_567064 prefixEnd_567064 86274487070007286871741 := by
  unfold tailWord_567064
  simp only [CollatzResearch.WordTrace]
  refine ⟨10341261608815724832970123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13788348811754299777293497 10341261608815724832970123)
  ·
    refine ⟨15511892413223587249455185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10341261608815724832970123 15511892413223587249455185)
    ·
      refine ⟨11633919309917690437091389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15511892413223587249455185 11633919309917690437091389)
      ·
        refine ⟨4362719741219133913909271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11633919309917690437091389 4362719741219133913909271)
        ·
          refine ⟨6544079611828700870863907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4362719741219133913909271 6544079611828700870863907)
          ·
            refine ⟨9816119417743051306295861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6544079611828700870863907 9816119417743051306295861)
            ·
              refine ⟨920261195413411059965237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9816119417743051306295861 920261195413411059965237)
              ·
                refine ⟨86274487070007286871741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 920261195413411059965237 86274487070007286871741)
                ·
                  rfl

theorem cell20_567064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_567064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567064 prefixEnd_567064 := by exact prefixLift 567064
  have htrace : WordTrace (prefixWord ++ tailWord_567064) baseStart_567064 baseEnd_567064 := by
    simpa [prefixWord, tailWord_567064, baseEnd_567064] using wordTrace_append hprefix tailTrace_567064
  have hstable : (prefixWord ++ tailWord_567064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567064).length < 2 ^ (prefixWord ++ tailWord_567064).sum := by decide
  have hdescent : baseEnd_567064 < baseStart_567064 := by decide
  rcases family_descends (prefixWord ++ tailWord_567064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567070 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_567070 : Nat := 118140960795 + 567070 * 2 ^ 59
def prefixEnd_567070 : Nat := 4983230072969 + 3 ^ 40 * 567070 * 2
def baseEnd_567070 : Nat := 258826199773512506415199

theorem tailTrace_567070 : CollatzResearch.WordTrace tailWord_567070 prefixEnd_567070 258826199773512506415199 := by
  unfold tailWord_567070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2585342756951214086332333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13788494703739808460439109 2585342756951214086332333)
  ·
    refine ⟨969503533856705282374625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2585342756951214086332333 969503533856705282374625)
    ·
      refine ⟨727127650392528961780969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 969503533856705282374625 727127650392528961780969)
      ·
        refine ⟨545345737794396721335727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 727127650392528961780969 545345737794396721335727)
        ·
          refine ⟨818018606691595082003591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545345737794396721335727 818018606691595082003591)
          ·
            refine ⟨1227027910037392623005387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818018606691595082003591 1227027910037392623005387)
            ·
              refine ⟨1840541865056088934508081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227027910037392623005387 1840541865056088934508081)
              ·
                refine ⟨1380406398792066700881061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1840541865056088934508081 1380406398792066700881061)
                ·
                  refine ⟨258826199773512506415199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1380406398792066700881061 258826199773512506415199)
                  ·
                    rfl

theorem cell20_567070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_567070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567070 prefixEnd_567070 := by exact prefixLift 567070
  have htrace : WordTrace (prefixWord ++ tailWord_567070) baseStart_567070 baseEnd_567070 := by
    simpa [prefixWord, tailWord_567070, baseEnd_567070] using wordTrace_append hprefix tailTrace_567070
  have hstable : (prefixWord ++ tailWord_567070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567070).length < 2 ^ (prefixWord ++ tailWord_567070).sum := by decide
  have hdescent : baseEnd_567070 < baseStart_567070 := by decide
  rcases family_descends (prefixWord ++ tailWord_567070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567091 : List Nat := [1, 1, 1, 2, 7, 1, 2, 3, 2]
def baseStart_567091 : Nat := 118140960795 + 567091 * 2 ^ 59
def prefixEnd_567091 : Nat := 4983230072969 + 3 ^ 40 * 567091 * 2
def baseEnd_567091 : Nat := 258835784745729766715113

theorem tailTrace_567091 : CollatzResearch.WordTrace tailWord_567091 prefixEnd_567091 258835784745729766715113 := by
  unfold tailWord_567091
  simp only [CollatzResearch.WordTrace]
  refine ⟨20683507988533633277173127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13789005325689088851448751 20683507988533633277173127)
  ·
    refine ⟨31025261982800449915759691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20683507988533633277173127 31025261982800449915759691)
    ·
      refine ⟨46537892974200674873639537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31025261982800449915759691 46537892974200674873639537)
      ·
        refine ⟨34903419730650506155229653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46537892974200674873639537 34903419730650506155229653)
        ·
          refine ⟨818048899937121238013195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 34903419730650506155229653 818048899937121238013195)
          ·
            refine ⟨1227073349905681857019793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818048899937121238013195 1227073349905681857019793)
            ·
              refine ⟨920305012429261392764845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1227073349905681857019793 920305012429261392764845)
              ·
                refine ⟨345114379660973022286817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 920305012429261392764845 345114379660973022286817)
                ·
                  refine ⟨258835784745729766715113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345114379660973022286817 258835784745729766715113)
                  ·
                    rfl

theorem cell20_567091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 2].length) (baseStart_567091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567091 prefixEnd_567091 := by exact prefixLift 567091
  have htrace : WordTrace (prefixWord ++ tailWord_567091) baseStart_567091 baseEnd_567091 := by
    simpa [prefixWord, tailWord_567091, baseEnd_567091] using wordTrace_append hprefix tailTrace_567091
  have hstable : (prefixWord ++ tailWord_567091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567091).length < 2 ^ (prefixWord ++ tailWord_567091).sum := by decide
  have hdescent : baseEnd_567091 < baseStart_567091 := by decide
  rcases family_descends (prefixWord ++ tailWord_567091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567109 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 5]
def baseStart_567109 : Nat := 118140960795 + 567109 * 2 ^ 59
def prefixEnd_567109 : Nat := 4983230072969 + 3 ^ 40 * 567109 * 2
def baseEnd_567109 : Nat := 258844000436201704115039

theorem tailTrace_567109 : CollatzResearch.WordTrace tailWord_567109 prefixEnd_567109 258844000436201704115039 := by
  unfold tailWord_567109
  simp only [CollatzResearch.WordTrace]
  refine ⟨20684164502468422351328381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13789443001645614900885587 20684164502468422351328381)
  ·
    refine ⟨7756561688425658381748143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20684164502468422351328381 7756561688425658381748143)
    ·
      refine ⟨11634842532638487572622215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7756561688425658381748143 11634842532638487572622215)
      ·
        refine ⟨17452263798957731358933323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11634842532638487572622215 17452263798957731358933323)
        ·
          refine ⟨26178395698436597038399985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17452263798957731358933323 26178395698436597038399985)
          ·
            refine ⟨19633796773827447778799989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26178395698436597038399985 19633796773827447778799989)
            ·
              refine ⟨1840668447546323229262499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19633796773827447778799989 1840668447546323229262499)
              ·
                refine ⟨2761002671319484843893749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840668447546323229262499 2761002671319484843893749)
                ·
                  refine ⟨258844000436201704115039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2761002671319484843893749 258844000436201704115039)
                  ·
                    rfl

theorem cell20_567109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_567109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567109 prefixEnd_567109 := by exact prefixLift 567109
  have htrace : WordTrace (prefixWord ++ tailWord_567109) baseStart_567109 baseEnd_567109 := by
    simpa [prefixWord, tailWord_567109, baseEnd_567109] using wordTrace_append hprefix tailTrace_567109
  have hstable : (prefixWord ++ tailWord_567109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567109).length < 2 ^ (prefixWord ++ tailWord_567109).sum := by decide
  have hdescent : baseEnd_567109 < baseStart_567109 := by decide
  rcases family_descends (prefixWord ++ tailWord_567109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567112 : List Nat := [2, 1, 3, 1, 1, 4, 2, 4, 2]
def baseStart_567112 : Nat := 118140960795 + 567112 * 2 ^ 59
def prefixEnd_567112 : Nat := 4983230072969 + 3 ^ 40 * 567112 * 2
def baseEnd_567112 : Nat := 258845369717947027015027

theorem tailTrace_567112 : CollatzResearch.WordTrace tailWord_567112 prefixEnd_567112 258845369717947027015027 := by
  unfold tailWord_567112
  simp only [CollatzResearch.WordTrace]
  refine ⟨10342136960728776931843795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13789515947638369242458393 10342136960728776931843795)
  ·
    refine ⟨15513205441093165397765693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10342136960728776931843795 15513205441093165397765693)
    ·
      refine ⟨5817452040409937024162135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15513205441093165397765693 5817452040409937024162135)
      ·
        refine ⟨8726178060614905536243203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5817452040409937024162135 8726178060614905536243203)
        ·
          refine ⟨13089267090922358304364805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8726178060614905536243203 13089267090922358304364805)
          ·
            refine ⟨2454237579547942182068401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13089267090922358304364805 2454237579547942182068401)
            ·
              refine ⟨1840678184660956636551301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2454237579547942182068401 1840678184660956636551301)
              ·
                refine ⟨345127159623929369353369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1840678184660956636551301 345127159623929369353369)
                ·
                  refine ⟨258845369717947027015027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345127159623929369353369 258845369717947027015027)
                  ·
                    rfl

theorem cell20_567112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 2].length) (baseStart_567112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567112 prefixEnd_567112 := by exact prefixLift 567112
  have htrace : WordTrace (prefixWord ++ tailWord_567112) baseStart_567112 baseEnd_567112 := by
    simpa [prefixWord, tailWord_567112, baseEnd_567112] using wordTrace_append hprefix tailTrace_567112
  have hstable : (prefixWord ++ tailWord_567112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567112).length < 2 ^ (prefixWord ++ tailWord_567112).sum := by decide
  have hdescent : baseEnd_567112 < baseStart_567112 := by decide
  rcases family_descends (prefixWord ++ tailWord_567112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567171 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 4]
def baseStart_567171 : Nat := 118140960795 + 567171 * 2 ^ 59
def prefixEnd_567171 : Nat := 4983230072969 + 3 ^ 40 * 567171 * 2
def baseEnd_567171 : Nat := 258872298925605044048119

theorem tailTrace_567171 : CollatzResearch.WordTrace tailWord_567171 prefixEnd_567171 258872298925605044048119 := by
  unfold tailWord_567171
  simp only [CollatzResearch.WordTrace]
  refine ⟨20686425828243806940085367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13790950552162537960056911 20686425828243806940085367)
  ·
    refine ⟨31029638742365710410128051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20686425828243806940085367 31029638742365710410128051)
    ·
      refine ⟨46544458113548565615192077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31029638742365710410128051 46544458113548565615192077)
      ·
        refine ⟨17454171792580712105697029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46544458113548565615192077 17454171792580712105697029)
        ·
          refine ⟨3272657211108883519818193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17454171792580712105697029 3272657211108883519818193)
          ·
            refine ⟨2454492908331662639863645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3272657211108883519818193 2454492908331662639863645)
            ·
              refine ⟨920434840624373489948867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2454492908331662639863645 920434840624373489948867)
              ·
                refine ⟨1380652260936560234923301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 920434840624373489948867 1380652260936560234923301)
                ·
                  refine ⟨258872298925605044048119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1380652260936560234923301 258872298925605044048119)
                  ·
                    rfl

theorem cell20_567171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 4].length) (baseStart_567171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567171 prefixEnd_567171 := by exact prefixLift 567171
  have htrace : WordTrace (prefixWord ++ tailWord_567171) baseStart_567171 baseEnd_567171 := by
    simpa [prefixWord, tailWord_567171, baseEnd_567171] using wordTrace_append hprefix tailTrace_567171
  have hstable : (prefixWord ++ tailWord_567171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567171).length < 2 ^ (prefixWord ++ tailWord_567171).sum := by decide
  have hdescent : baseEnd_567171 < baseStart_567171 := by decide
  rcases family_descends (prefixWord ++ tailWord_567171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567237 : List Nat := [1, 3, 1, 1, 1, 1, 1, 11]
def baseStart_567237 : Nat := 118140960795 + 567237 * 2 ^ 59
def prefixEnd_567237 : Nat := 4983230072969 + 3 ^ 40 * 567237 * 2
def baseEnd_567237 : Nat := 86300807708000715949283

theorem tailTrace_567237 : CollatzResearch.WordTrace tailWord_567237 prefixEnd_567237 86300807708000715949283 := by
  unfold tailWord_567237
  simp only [CollatzResearch.WordTrace]
  refine ⟨20688833046004700211987965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13792555364003133474658643 20688833046004700211987965)
  ·
    refine ⟨7758312392251762579495487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20688833046004700211987965 7758312392251762579495487)
    ·
      refine ⟨11637468588377643869243231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7758312392251762579495487 11637468588377643869243231)
      ·
        refine ⟨17456202882566465803864847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11637468588377643869243231 17456202882566465803864847)
        ·
          refine ⟨26184304323849698705797271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17456202882566465803864847 26184304323849698705797271)
          ·
            refine ⟨39276456485774548058695907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26184304323849698705797271 39276456485774548058695907)
            ·
              refine ⟨58914684728661822088043861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39276456485774548058695907 58914684728661822088043861)
              ·
                refine ⟨86300807708000715949283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 58914684728661822088043861 86300807708000715949283)
                ·
                  rfl

theorem cell20_567237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 11].length) (baseStart_567237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567237 prefixEnd_567237 := by exact prefixLift 567237
  have htrace : WordTrace (prefixWord ++ tailWord_567237) baseStart_567237 baseEnd_567237 := by
    simpa [prefixWord, tailWord_567237, baseEnd_567237] using wordTrace_append hprefix tailTrace_567237
  have hstable : (prefixWord ++ tailWord_567237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567237).length < 2 ^ (prefixWord ++ tailWord_567237).sum := by decide
  have hdescent : baseEnd_567237 < baseStart_567237 := by decide
  rcases family_descends (prefixWord ++ tailWord_567237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567240 : List Nat := [2, 1, 3, 1, 4, 1, 2, 3, 3]
def baseStart_567240 : Nat := 118140960795 + 567240 * 2 ^ 59
def prefixEnd_567240 : Nat := 4983230072969 + 3 ^ 40 * 567240 * 2
def baseEnd_567240 : Nat := 258903792405747470747837

theorem tailTrace_567240 : CollatzResearch.WordTrace tailWord_567240 prefixEnd_567240 258903792405747470747837 := by
  unfold tailWord_567240
  simp only [CollatzResearch.WordTrace]
  refine ⟨10344471232496915862173587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13792628309995887816231449 10344471232496915862173587)
  ·
    refine ⟨15516706848745373793260381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10344471232496915862173587 15516706848745373793260381)
    ·
      refine ⟨5818765068279515172472643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15516706848745373793260381 5818765068279515172472643)
      ·
        refine ⟨8728147602419272758708965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5818765068279515172472643 8728147602419272758708965)
        ·
          refine ⟨1636527675453613642257931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8728147602419272758708965 1636527675453613642257931)
          ·
            refine ⟨2454791513180420463386897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1636527675453613642257931 2454791513180420463386897)
            ·
              refine ⟨1841093634885315347540173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2454791513180420463386897 1841093634885315347540173)
              ·
                refine ⟨690410113081993255327565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1841093634885315347540173 690410113081993255327565)
                ·
                  refine ⟨258903792405747470747837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 690410113081993255327565 258903792405747470747837)
                  ·
                    rfl

theorem cell20_567240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_567240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567240 prefixEnd_567240 := by exact prefixLift 567240
  have htrace : WordTrace (prefixWord ++ tailWord_567240) baseStart_567240 baseEnd_567240 := by
    simpa [prefixWord, tailWord_567240, baseEnd_567240] using wordTrace_append hprefix tailTrace_567240
  have hstable : (prefixWord ++ tailWord_567240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567240).length < 2 ^ (prefixWord ++ tailWord_567240).sum := by decide
  have hdescent : baseEnd_567240 < baseStart_567240 := by decide
  rcases family_descends (prefixWord ++ tailWord_567240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567250 : List Nat := [3, 2, 2, 3, 2, 1, 3, 4]
def baseStart_567250 : Nat := 118140960795 + 567250 * 2 ^ 59
def prefixEnd_567250 : Nat := 4983230072969 + 3 ^ 40 * 567250 * 2
def baseEnd_567250 : Nat := 86302785559410626804821

theorem tailTrace_567250 : CollatzResearch.WordTrace tailWord_567250 prefixEnd_567250 86302785559410626804821 := by
  unfold tailWord_567250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5172326798739400858052801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13792871463305068954807469 5172326798739400858052801)
  ·
    refine ⟨3879245099054550643539601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5172326798739400858052801 3879245099054550643539601)
    ·
      refine ⟨2909433824290912982654701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3879245099054550643539601 2909433824290912982654701)
      ·
        refine ⟨1091037684109092368495513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2909433824290912982654701 1091037684109092368495513)
        ·
          refine ⟨818278263081819276371635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1091037684109092368495513 818278263081819276371635)
          ·
            refine ⟨1227417394622728914557453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818278263081819276371635 1227417394622728914557453)
            ·
              refine ⟨460281522983523342959045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1227417394622728914557453 460281522983523342959045)
              ·
                refine ⟨86302785559410626804821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 460281522983523342959045 86302785559410626804821)
                ·
                  rfl

theorem cell20_567250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_567250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567250 prefixEnd_567250 := by exact prefixLift 567250
  have htrace : WordTrace (prefixWord ++ tailWord_567250) baseStart_567250 baseEnd_567250 := by
    simpa [prefixWord, tailWord_567250, baseEnd_567250] using wordTrace_append hprefix tailTrace_567250
  have hstable : (prefixWord ++ tailWord_567250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567250).length < 2 ^ (prefixWord ++ tailWord_567250).sum := by decide
  have hdescent : baseEnd_567250 < baseStart_567250 := by decide
  rcases family_descends (prefixWord ++ tailWord_567250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567268 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 6]
def baseStart_567268 : Nat := 118140960795 + 567268 * 2 ^ 59
def prefixEnd_567268 : Nat := 4983230072969 + 3 ^ 40 * 567268 * 2
def baseEnd_567268 : Nat := 258916572368703817814389

theorem tailTrace_567268 : CollatzResearch.WordTrace tailWord_567268 prefixEnd_567268 258916572368703817814389 := by
  unfold tailWord_567268
  simp only [CollatzResearch.WordTrace]
  refine ⟨10344981854446196253183229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13793309139261595004244305 10344981854446196253183229)
  ·
    refine ⟨3879368195417323594943711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10344981854446196253183229 3879368195417323594943711)
    ·
      refine ⟨5819052293125985392415567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3879368195417323594943711 5819052293125985392415567)
      ·
        refine ⟨8728578439688978088623351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5819052293125985392415567 8728578439688978088623351)
        ·
          refine ⟨13092867659533467132935027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8728578439688978088623351 13092867659533467132935027)
          ·
            refine ⟨19639301489300200699402541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13092867659533467132935027 19639301489300200699402541)
            ·
              refine ⟨7364738058487575262275953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19639301489300200699402541 7364738058487575262275953)
              ·
                refine ⟨5523553543865681446706965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7364738058487575262275953 5523553543865681446706965)
                ·
                  refine ⟨258916572368703817814389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5523553543865681446706965 258916572368703817814389)
                  ·
                    rfl

theorem cell20_567268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_567268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567268 prefixEnd_567268 := by exact prefixLift 567268
  have htrace : WordTrace (prefixWord ++ tailWord_567268) baseStart_567268 baseEnd_567268 := by
    simpa [prefixWord, tailWord_567268, baseEnd_567268] using wordTrace_append hprefix tailTrace_567268
  have hstable : (prefixWord ++ tailWord_567268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567268).length < 2 ^ (prefixWord ++ tailWord_567268).sum := by decide
  have hdescent : baseEnd_567268 < baseStart_567268 := by decide
  rcases family_descends (prefixWord ++ tailWord_567268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567278 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_567278 : Nat := 118140960795 + 567278 * 2 ^ 59
def prefixEnd_567278 : Nat := 4983230072969 + 3 ^ 40 * 567278 * 2
def baseEnd_567278 : Nat := 258921136641188227481015

theorem tailTrace_567278 : CollatzResearch.WordTrace tailWord_567278 prefixEnd_567278 258921136641188227481015 := by
  unfold tailWord_567278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2586291054857020526778811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13793552292570776142820325 2586291054857020526778811)
  ·
    refine ⟨3879436582285530790168217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2586291054857020526778811 3879436582285530790168217)
    ·
      refine ⟨2909577436714148092626163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3879436582285530790168217 2909577436714148092626163)
      ·
        refine ⟨4364366155071222138939245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2909577436714148092626163 4364366155071222138939245)
        ·
          refine ⟨1636637308151708302102217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4364366155071222138939245 1636637308151708302102217)
          ·
            refine ⟨1227477981113781226576663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1636637308151708302102217 1227477981113781226576663)
            ·
              refine ⟨1841216971670671839864995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227477981113781226576663 1841216971670671839864995)
              ·
                refine ⟨2761825457506007759797493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1841216971670671839864995 2761825457506007759797493)
                ·
                  refine ⟨258921136641188227481015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2761825457506007759797493 258921136641188227481015)
                  ·
                    rfl

theorem cell20_567278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_567278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567278 prefixEnd_567278 := by exact prefixLift 567278
  have htrace : WordTrace (prefixWord ++ tailWord_567278) baseStart_567278 baseEnd_567278 := by
    simpa [prefixWord, tailWord_567278, baseEnd_567278] using wordTrace_append hprefix tailTrace_567278
  have hstable : (prefixWord ++ tailWord_567278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567278).length < 2 ^ (prefixWord ++ tailWord_567278).sum := by decide
  have hdescent : baseEnd_567278 < baseStart_567278 := by decide
  rcases family_descends (prefixWord ++ tailWord_567278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567299 : List Nat := [1, 1, 1, 3, 2, 1, 1, 7, 3]
def baseStart_567299 : Nat := 118140960795 + 567299 * 2 ^ 59
def prefixEnd_567299 : Nat := 4983230072969 + 3 ^ 40 * 567299 * 2
def baseEnd_567299 : Nat := 258930721613405487780929

theorem tailTrace_567299 : CollatzResearch.WordTrace tailWord_567299 prefixEnd_567299 258930721613405487780929 := by
  unfold tailWord_567299
  simp only [CollatzResearch.WordTrace]
  refine ⟨20691094371780084800744951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13794062914520056533829967 20691094371780084800744951)
  ·
    refine ⟨31036641557670127201117427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20691094371780084800744951 31036641557670127201117427)
    ·
      refine ⟨46554962336505190801676141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31036641557670127201117427 46554962336505190801676141)
      ·
        refine ⟨17458110876189446550628553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46554962336505190801676141 17458110876189446550628553)
        ·
          refine ⟨13093583157142084912971415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17458110876189446550628553 13093583157142084912971415)
          ·
            refine ⟨19640374735713127369457123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13093583157142084912971415 19640374735713127369457123)
            ·
              refine ⟨29460562103569691054185685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19640374735713127369457123 29460562103569691054185685)
              ·
                refine ⟨690481924302414634082477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29460562103569691054185685 690481924302414634082477)
                ·
                  refine ⟨258930721613405487780929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 690481924302414634082477 258930721613405487780929)
                  ·
                    rfl

theorem cell20_567299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 3].length) (baseStart_567299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567299 prefixEnd_567299 := by exact prefixLift 567299
  have htrace : WordTrace (prefixWord ++ tailWord_567299) baseStart_567299 baseEnd_567299 := by
    simpa [prefixWord, tailWord_567299, baseEnd_567299] using wordTrace_append hprefix tailTrace_567299
  have hstable : (prefixWord ++ tailWord_567299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567299).length < 2 ^ (prefixWord ++ tailWord_567299).sum := by decide
  have hdescent : baseEnd_567299 < baseStart_567299 := by decide
  rcases family_descends (prefixWord ++ tailWord_567299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567323 : List Nat := [1, 1, 1, 1, 1, 1, 3, 9, 2]
def baseStart_567323 : Nat := 118140960795 + 567323 * 2 ^ 59
def prefixEnd_567323 : Nat := 4983230072969 + 3 ^ 40 * 567323 * 2
def baseEnd_567323 : Nat := 258941675867368070980831

theorem tailTrace_567323 : CollatzResearch.WordTrace tailWord_567323 prefixEnd_567323 258941675867368070980831 := by
  unfold tailWord_567323
  simp only [CollatzResearch.WordTrace]
  refine ⟨20691969723693136899618623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13794646482462091266412415 20691969723693136899618623)
  ·
    refine ⟨31037954585539705349427935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20691969723693136899618623 31037954585539705349427935)
    ·
      refine ⟨46556931878309558024141903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31037954585539705349427935 46556931878309558024141903)
      ·
        refine ⟨69835397817464337036212855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46556931878309558024141903 69835397817464337036212855)
        ·
          refine ⟨104753096726196505554319283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69835397817464337036212855 104753096726196505554319283)
          ·
            refine ⟨157129645089294758331478925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104753096726196505554319283 157129645089294758331478925)
            ·
              refine ⟨58923616908485534374304597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157129645089294758331478925 58923616908485534374304597)
              ·
                refine ⟨345255567823157427974441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 58923616908485534374304597 345255567823157427974441)
                ·
                  refine ⟨258941675867368070980831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345255567823157427974441 258941675867368070980831)
                  ·
                    rfl

theorem cell20_567323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 2].length) (baseStart_567323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567323 prefixEnd_567323 := by exact prefixLift 567323
  have htrace : WordTrace (prefixWord ++ tailWord_567323) baseStart_567323 baseEnd_567323 := by
    simpa [prefixWord, tailWord_567323, baseEnd_567323] using wordTrace_append hprefix tailTrace_567323
  have hstable : (prefixWord ++ tailWord_567323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567323).length < 2 ^ (prefixWord ++ tailWord_567323).sum := by decide
  have hdescent : baseEnd_567323 < baseStart_567323 := by decide
  rcases family_descends (prefixWord ++ tailWord_567323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567336 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 4]
def baseStart_567336 : Nat := 118140960795 + 567336 * 2 ^ 59
def prefixEnd_567336 : Nat := 4983230072969 + 3 ^ 40 * 567336 * 2
def baseEnd_567336 : Nat := 258947609421597803547445

theorem tailTrace_567336 : CollatzResearch.WordTrace tailWord_567336 prefixEnd_567336 258947609421597803547445 := by
  unfold tailWord_567336
  simp only [CollatzResearch.WordTrace]
  refine ⟨10346221936323020059920931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13794962581764026746561241 10346221936323020059920931)
  ·
    refine ⟨15519332904484530089881397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10346221936323020059920931 15519332904484530089881397)
    ·
      refine ⟨1454937459795424695926381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15519332904484530089881397 1454937459795424695926381)
      ·
        refine ⟨545601547423284260972393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1454937459795424695926381 545601547423284260972393)
        ·
          refine ⟨409201160567463195729295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 545601547423284260972393 409201160567463195729295)
          ·
            refine ⟨613801740851194793593943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409201160567463195729295 613801740851194793593943)
            ·
              refine ⟨920702611276792190390915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613801740851194793593943 920702611276792190390915)
              ·
                refine ⟨1381053916915188285586373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 920702611276792190390915 1381053916915188285586373)
                ·
                  refine ⟨258947609421597803547445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1381053916915188285586373 258947609421597803547445)
                  ·
                    rfl

theorem cell20_567336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 4].length) (baseStart_567336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567336 prefixEnd_567336 := by exact prefixLift 567336
  have htrace : WordTrace (prefixWord ++ tailWord_567336) baseStart_567336 baseEnd_567336 := by
    simpa [prefixWord, tailWord_567336, baseEnd_567336] using wordTrace_append hprefix tailTrace_567336
  have hstable : (prefixWord ++ tailWord_567336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567336).length < 2 ^ (prefixWord ++ tailWord_567336).sum := by decide
  have hdescent : baseEnd_567336 < baseStart_567336 := by decide
  rcases family_descends (prefixWord ++ tailWord_567336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567351 : List Nat := [1, 1, 3, 1, 2, 2, 3, 7]
def baseStart_567351 : Nat := 118140960795 + 567351 * 2 ^ 59
def prefixEnd_567351 : Nat := 4983230072969 + 3 ^ 40 * 567351 * 2
def baseEnd_567351 : Nat := 86318151943441472682461

theorem tailTrace_567351 : CollatzResearch.WordTrace tailWord_567351 prefixEnd_567351 86318151943441472682461 := by
  unfold tailWord_567351
  simp only [CollatzResearch.WordTrace]
  refine ⟨20692990967591697681637907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13795327311727798454425271 20692990967591697681637907)
  ·
    refine ⟨31039486451387546522456861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20692990967591697681637907 31039486451387546522456861)
    ·
      refine ⟨11639807419270329945921323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31039486451387546522456861 11639807419270329945921323)
      ·
        refine ⟨17459711128905494918881985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11639807419270329945921323 17459711128905494918881985)
        ·
          refine ⟨13094783346679121189161489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17459711128905494918881985 13094783346679121189161489)
          ·
            refine ⟨9821087510009340891871117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13094783346679121189161489 9821087510009340891871117)
            ·
              refine ⟨3682907816253502834451669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9821087510009340891871117 3682907816253502834451669)
              ·
                refine ⟨86318151943441472682461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3682907816253502834451669 86318151943441472682461)
                ·
                  rfl

theorem cell20_567351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 7].length) (baseStart_567351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567351 prefixEnd_567351 := by exact prefixLift 567351
  have htrace : WordTrace (prefixWord ++ tailWord_567351) baseStart_567351 baseEnd_567351 := by
    simpa [prefixWord, tailWord_567351, baseEnd_567351] using wordTrace_append hprefix tailTrace_567351
  have hstable : (prefixWord ++ tailWord_567351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567351).length < 2 ^ (prefixWord ++ tailWord_567351).sum := by decide
  have hdescent : baseEnd_567351 < baseStart_567351 := by decide
  rcases family_descends (prefixWord ++ tailWord_567351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567392 : List Nat := [2, 1, 1, 3, 2, 4, 2, 2, 3]
def baseStart_567392 : Nat := 118140960795 + 567392 * 2 ^ 59
def prefixEnd_567392 : Nat := 4983230072969 + 3 ^ 40 * 567392 * 2
def baseEnd_567392 : Nat := 258973169347510497680549

theorem tailTrace_567392 : CollatzResearch.WordTrace tailWord_567392 prefixEnd_567392 258973169347510497680549 := by
  unfold tailWord_567392
  simp only [CollatzResearch.WordTrace]
  refine ⟨10347243180221580841940215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13796324240295441122586953 10347243180221580841940215)
  ·
    refine ⟨15520864770332371262910323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10347243180221580841940215 15520864770332371262910323)
    ·
      refine ⟨23281297155498556894365485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15520864770332371262910323 23281297155498556894365485)
      ·
        refine ⟨8730486433311958835387057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23281297155498556894365485 8730486433311958835387057)
        ·
          refine ⟨6547864824983969126540293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8730486433311958835387057 6547864824983969126540293)
          ·
            refine ⟨1227724654684494211226305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6547864824983969126540293 1227724654684494211226305)
            ·
              refine ⟨920793491013370658419729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1227724654684494211226305 920793491013370658419729)
              ·
                refine ⟨690595118260027993814797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 920793491013370658419729 690595118260027993814797)
                ·
                  refine ⟨258973169347510497680549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 690595118260027993814797 258973169347510497680549)
                  ·
                    rfl

theorem cell20_567392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_567392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567392 prefixEnd_567392 := by exact prefixLift 567392
  have htrace : WordTrace (prefixWord ++ tailWord_567392) baseStart_567392 baseEnd_567392 := by
    simpa [prefixWord, tailWord_567392, baseEnd_567392] using wordTrace_append hprefix tailTrace_567392
  have hstable : (prefixWord ++ tailWord_567392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567392).length < 2 ^ (prefixWord ++ tailWord_567392).sum := by decide
  have hdescent : baseEnd_567392 < baseStart_567392 := by decide
  rcases family_descends (prefixWord ++ tailWord_567392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567402 : List Nat := [3, 1, 3, 2, 4, 1, 1, 5]
def baseStart_567402 : Nat := 118140960795 + 567402 * 2 ^ 59
def prefixEnd_567402 : Nat := 4983230072969 + 3 ^ 40 * 567402 * 2
def baseEnd_567402 : Nat := 86325911206664969115725

theorem tailTrace_567402 : CollatzResearch.WordTrace tailWord_567402 prefixEnd_567402 86325911206664969115725 := by
  unfold tailWord_567402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5173712772601733347936115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13796567393604622261162973 5173712772601733347936115)
  ·
    refine ⟨7760569158902600021904173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5173712772601733347936115 7760569158902600021904173)
    ·
      refine ⟨2910213434588475008214065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7760569158902600021904173 2910213434588475008214065)
      ·
        refine ⟨2182660075941356256160549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2910213434588475008214065 2182660075941356256160549)
        ·
          refine ⟨409248764239004298030103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2182660075941356256160549 409248764239004298030103)
          ·
            refine ⟨613873146358506447045155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409248764239004298030103 613873146358506447045155)
            ·
              refine ⟨920809719537759670567733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613873146358506447045155 920809719537759670567733)
              ·
                refine ⟨86325911206664969115725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 920809719537759670567733 86325911206664969115725)
                ·
                  rfl

theorem cell20_567402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_567402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567402 prefixEnd_567402 := by exact prefixLift 567402
  have htrace : WordTrace (prefixWord ++ tailWord_567402) baseStart_567402 baseEnd_567402 := by
    simpa [prefixWord, tailWord_567402, baseEnd_567402] using wordTrace_append hprefix tailTrace_567402
  have hstable : (prefixWord ++ tailWord_567402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567402).length < 2 ^ (prefixWord ++ tailWord_567402).sum := by decide
  have hdescent : baseEnd_567402 < baseStart_567402 := by decide
  rcases family_descends (prefixWord ++ tailWord_567402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567420 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 6]
def baseStart_567420 : Nat := 118140960795 + 567420 * 2 ^ 59
def prefixEnd_567420 : Nat := 4983230072969 + 3 ^ 40 * 567420 * 2
def baseEnd_567420 : Nat := 258985949310466844747101

theorem tailTrace_567420 : CollatzResearch.WordTrace tailWord_567420 prefixEnd_567420 258985949310466844747101 := by
  unfold tailWord_567420
  simp only [CollatzResearch.WordTrace]
  refine ⟨10347753802170861232949857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13797005069561148310599809 10347753802170861232949857)
  ·
    refine ⟨7760815351628145924712393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10347753802170861232949857 7760815351628145924712393)
    ·
      refine ⟨5820611513721109443534295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7760815351628145924712393 5820611513721109443534295)
      ·
        refine ⟨8730917270581664165301443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5820611513721109443534295 8730917270581664165301443)
        ·
          refine ⟨13096375905872496247952165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8730917270581664165301443 13096375905872496247952165)
          ·
            refine ⟨2455570482351093046491031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13096375905872496247952165 2455570482351093046491031)
            ·
              refine ⟨3683355723526639569736547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455570482351093046491031 3683355723526639569736547)
              ·
                refine ⟨5525033585289959354604821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3683355723526639569736547 5525033585289959354604821)
                ·
                  refine ⟨258985949310466844747101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5525033585289959354604821 258985949310466844747101)
                  ·
                    rfl

theorem cell20_567420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_567420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567420 prefixEnd_567420 := by exact prefixLift 567420
  have htrace : WordTrace (prefixWord ++ tailWord_567420) baseStart_567420 baseEnd_567420 := by
    simpa [prefixWord, tailWord_567420, baseEnd_567420] using wordTrace_append hprefix tailTrace_567420
  have hstable : (prefixWord ++ tailWord_567420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567420).length < 2 ^ (prefixWord ++ tailWord_567420).sum := by decide
  have hdescent : baseEnd_567420 < baseStart_567420 := by decide
  rcases family_descends (prefixWord ++ tailWord_567420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567447 : List Nat := [1, 1, 3, 3, 4, 2, 1, 2, 3]
def baseStart_567447 : Nat := 118140960795 + 567447 * 2 ^ 59
def prefixEnd_567447 : Nat := 4983230072969 + 3 ^ 40 * 567447 * 2
def baseEnd_567447 : Nat := 258998272846174750846991

theorem tailTrace_567447 : CollatzResearch.WordTrace tailWord_567447 prefixEnd_567447 258998272846174750846991 := by
  unfold tailWord_567447
  simp only [CollatzResearch.WordTrace]
  refine ⟨20696492375243906077132595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13797661583495937384755063 20696492375243906077132595)
  ·
    refine ⟨31044738562865859115698893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20696492375243906077132595 31044738562865859115698893)
    ·
      refine ⟨11641776961074697168387085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31044738562865859115698893 11641776961074697168387085)
      ·
        refine ⟨4365666360403011438145157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11641776961074697168387085 4365666360403011438145157)
        ·
          refine ⟨818562442575564644652217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4365666360403011438145157 818562442575564644652217)
          ·
            refine ⟨613921831931673483489163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 818562442575564644652217 613921831931673483489163)
            ·
              refine ⟨920882747897510225233745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613921831931673483489163 920882747897510225233745)
              ·
                refine ⟨690662060923132668925309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 920882747897510225233745 690662060923132668925309)
                ·
                  refine ⟨258998272846174750846991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 690662060923132668925309 258998272846174750846991)
                  ·
                    rfl

theorem cell20_567447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 3].length) (baseStart_567447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567447 prefixEnd_567447 := by exact prefixLift 567447
  have htrace : WordTrace (prefixWord ++ tailWord_567447) baseStart_567447 baseEnd_567447 := by
    simpa [prefixWord, tailWord_567447, baseEnd_567447] using wordTrace_append hprefix tailTrace_567447
  have hstable : (prefixWord ++ tailWord_567447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567447).length < 2 ^ (prefixWord ++ tailWord_567447).sum := by decide
  have hdescent : baseEnd_567447 < baseStart_567447 := by decide
  rcases family_descends (prefixWord ++ tailWord_567447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567472 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 9]
def baseStart_567472 : Nat := 118140960795 + 567472 * 2 ^ 59
def prefixEnd_567472 : Nat := 4983230072969 + 3 ^ 40 * 567472 * 2
def baseEnd_567472 : Nat := 259009683527385775013555

theorem tailTrace_567472 : CollatzResearch.WordTrace tailWord_567472 prefixEnd_567472 259009683527385775013555 := by
  unfold tailWord_567472
  simp only [CollatzResearch.WordTrace]
  refine ⟨10348702100076667673396335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13798269466768890231195113 10348702100076667673396335)
  ·
    refine ⟨15523053150115001510094503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10348702100076667673396335 15523053150115001510094503)
    ·
      refine ⟨23284579725172502265141755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15523053150115001510094503 23284579725172502265141755)
      ·
        refine ⟨34926869587758753397712633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23284579725172502265141755 34926869587758753397712633)
        ·
          refine ⟨26195152190819065048284475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34926869587758753397712633 26195152190819065048284475)
          ·
            refine ⟨39292728286228597572426713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26195152190819065048284475 39292728286228597572426713)
            ·
              refine ⟨29469546214671448179320035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39292728286228597572426713 29469546214671448179320035)
              ·
                refine ⟨44204319322007172268980053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29469546214671448179320035 44204319322007172268980053)
                ·
                  refine ⟨259009683527385775013555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44204319322007172268980053 259009683527385775013555)
                  ·
                    rfl

theorem cell20_567472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_567472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567472 prefixEnd_567472 := by exact prefixLift 567472
  have htrace : WordTrace (prefixWord ++ tailWord_567472) baseStart_567472 baseEnd_567472 := by
    simpa [prefixWord, tailWord_567472, baseEnd_567472] using wordTrace_append hprefix tailTrace_567472
  have hstable : (prefixWord ++ tailWord_567472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567472).length < 2 ^ (prefixWord ++ tailWord_567472).sum := by decide
  have hdescent : baseEnd_567472 < baseStart_567472 := by decide
  rcases family_descends (prefixWord ++ tailWord_567472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567482 : List Nat := [3, 1, 1, 1, 2, 2, 6, 4]
def baseStart_567482 : Nat := 118140960795 + 567482 * 2 ^ 59
def prefixEnd_567482 : Nat := 4983230072969 + 3 ^ 40 * 567482 * 2
def baseEnd_567482 : Nat := 86338082599956728226727

theorem tailTrace_567482 : CollatzResearch.WordTrace tailWord_567482 prefixEnd_567482 86338082599956728226727 := by
  unfold tailWord_567482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5174442232529276763664175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13798512620078071369771133 5174442232529276763664175)
  ·
    refine ⟨7761663348793915145496263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5174442232529276763664175 7761663348793915145496263)
    ·
      refine ⟨11642495023190872718244395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7761663348793915145496263 11642495023190872718244395)
      ·
        refine ⟨17463742534786309077366593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11642495023190872718244395 17463742534786309077366593)
        ·
          refine ⟨13097806901089731808024945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17463742534786309077366593 13097806901089731808024945)
          ·
            refine ⟨9823355175817298856018709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13097806901089731808024945 9823355175817298856018709)
            ·
              refine ⟨460469773866435883875877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9823355175817298856018709 460469773866435883875877)
              ·
                refine ⟨86338082599956728226727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 460469773866435883875877 86338082599956728226727)
                ·
                  rfl

theorem cell20_567482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_567482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567482 prefixEnd_567482 := by exact prefixLift 567482
  have htrace : WordTrace (prefixWord ++ tailWord_567482) baseStart_567482 baseEnd_567482 := by
    simpa [prefixWord, tailWord_567482, baseEnd_567482] using wordTrace_append hprefix tailTrace_567482
  have hstable : (prefixWord ++ tailWord_567482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567482).length < 2 ^ (prefixWord ++ tailWord_567482).sum := by decide
  have hdescent : baseEnd_567482 < baseStart_567482 := by decide
  rcases family_descends (prefixWord ++ tailWord_567482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567509 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 4]
def baseStart_567509 : Nat := 118140960795 + 567509 * 2 ^ 59
def prefixEnd_567509 : Nat := 4983230072969 + 3 ^ 40 * 567509 * 2
def baseEnd_567509 : Nat := 259026571335578090780071

theorem tailTrace_567509 : CollatzResearch.WordTrace tailWord_567509 prefixEnd_567509 259026571335578090780071 := by
  unfold tailWord_567509
  simp only [CollatzResearch.WordTrace]
  refine ⟨20698753701019290665889581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13799169134012860443926387 20698753701019290665889581)
  ·
    refine ⟨7762032637882233999708593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20698753701019290665889581 7762032637882233999708593)
    ·
      refine ⟨5821524478411675499781445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7762032637882233999708593 5821524478411675499781445)
      ·
        refine ⟨1091535839702189156209021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5821524478411675499781445 1091535839702189156209021)
        ·
          refine ⟨409325939888320933578383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1091535839702189156209021 409325939888320933578383)
          ·
            refine ⟨613988909832481400367575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409325939888320933578383 613988909832481400367575)
            ·
              refine ⟨920983364748722100551363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613988909832481400367575 920983364748722100551363)
              ·
                refine ⟨1381475047123083150827045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 920983364748722100551363 1381475047123083150827045)
                ·
                  refine ⟨259026571335578090780071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1381475047123083150827045 259026571335578090780071)
                  ·
                    rfl

theorem cell20_567509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_567509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567509 prefixEnd_567509 := by exact prefixLift 567509
  have htrace : WordTrace (prefixWord ++ tailWord_567509) baseStart_567509 baseEnd_567509 := by
    simpa [prefixWord, tailWord_567509, baseEnd_567509] using wordTrace_append hprefix tailTrace_567509
  have hstable : (prefixWord ++ tailWord_567509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567509).length < 2 ^ (prefixWord ++ tailWord_567509).sum := by decide
  have hdescent : baseEnd_567509 < baseStart_567509 := by decide
  rcases family_descends (prefixWord ++ tailWord_567509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567513 : List Nat := [1, 2, 1, 2, 3, 1, 2, 6, 2]
def baseStart_567513 : Nat := 118140960795 + 567513 * 2 ^ 59
def prefixEnd_567513 : Nat := 4983230072969 + 3 ^ 40 * 567513 * 2
def baseEnd_567513 : Nat := 259028397044571854646721

theorem tailTrace_567513 : CollatzResearch.WordTrace tailWord_567513 prefixEnd_567513 259028397044571854646721 := by
  unfold tailWord_567513
  simp only [CollatzResearch.WordTrace]
  refine ⟨20698899593004799349035193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13799266395336532899356795 20698899593004799349035193)
  ·
    refine ⟨15524174694753599511776395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20698899593004799349035193 15524174694753599511776395)
    ·
      refine ⟨23286262042130399267664593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15524174694753599511776395 23286262042130399267664593)
      ·
        refine ⟨17464696531597799450748445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23286262042130399267664593 17464696531597799450748445)
        ·
          refine ⟨6549261199349174794030667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17464696531597799450748445 6549261199349174794030667)
          ·
            refine ⟨9823891799023762191046001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6549261199349174794030667 9823891799023762191046001)
            ·
              refine ⟨7367918849267821643284501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9823891799023762191046001 7367918849267821643284501)
              ·
                refine ⟨345371196059429139528961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7367918849267821643284501 345371196059429139528961)
                ·
                  refine ⟨259028397044571854646721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345371196059429139528961 259028397044571854646721)
                  ·
                    rfl

theorem cell20_567513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 2].length) (baseStart_567513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567513 prefixEnd_567513 := by exact prefixLift 567513
  have htrace : WordTrace (prefixWord ++ tailWord_567513) baseStart_567513 baseEnd_567513 := by
    simpa [prefixWord, tailWord_567513, baseEnd_567513] using wordTrace_append hprefix tailTrace_567513
  have hstable : (prefixWord ++ tailWord_567513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567513).length < 2 ^ (prefixWord ++ tailWord_567513).sum := by decide
  have hdescent : baseEnd_567513 < baseStart_567513 := by decide
  rcases family_descends (prefixWord ++ tailWord_567513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567516 : List Nat := [2, 2, 5, 2, 1, 1, 2, 5]
def baseStart_567516 : Nat := 118140960795 + 567516 * 2 ^ 59
def prefixEnd_567516 : Nat := 4983230072969 + 3 ^ 40 * 567516 * 2
def baseEnd_567516 : Nat := 86343255442105725848903

theorem tailTrace_567516 : CollatzResearch.WordTrace tailWord_567516 prefixEnd_567516 86343255442105725848903 := by
  unfold tailWord_567516
  simp only [CollatzResearch.WordTrace]
  refine ⟨10349504505996965430697201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13799339341329287240929601 10349504505996965430697201)
  ·
    refine ⟨7762128379497724073022901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10349504505996965430697201 7762128379497724073022901)
    ·
      refine ⟨727699535577911631845897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7762128379497724073022901 727699535577911631845897)
      ·
        refine ⟨545774651683433723884423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 727699535577911631845897 545774651683433723884423)
        ·
          refine ⟨818661977525150585826635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545774651683433723884423 818661977525150585826635)
          ·
            refine ⟨1227992966287725878739953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818661977525150585826635 1227992966287725878739953)
            ·
              refine ⟨920994724715794409054965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1227992966287725878739953 920994724715794409054965)
              ·
                refine ⟨86343255442105725848903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 920994724715794409054965 86343255442105725848903)
                ·
                  rfl

theorem cell20_567516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_567516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567516 prefixEnd_567516 := by exact prefixLift 567516
  have htrace : WordTrace (prefixWord ++ tailWord_567516) baseStart_567516 baseEnd_567516 := by
    simpa [prefixWord, tailWord_567516, baseEnd_567516] using wordTrace_append hprefix tailTrace_567516
  have hstable : (prefixWord ++ tailWord_567516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567516).length < 2 ^ (prefixWord ++ tailWord_567516).sum := by decide
  have hdescent : baseEnd_567516 < baseStart_567516 := by decide
  rcases family_descends (prefixWord ++ tailWord_567516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567523 : List Nat := [1, 1, 1, 8, 1, 1, 1, 3, 3]
def baseStart_567523 : Nat := 118140960795 + 567523 * 2 ^ 59
def prefixEnd_567523 : Nat := 4983230072969 + 3 ^ 40 * 567523 * 2
def baseEnd_567523 : Nat := 259032961317056264313347

theorem tailTrace_567523 : CollatzResearch.WordTrace tailWord_567523 prefixEnd_567523 259032961317056264313347 := by
  unfold tailWord_567523
  simp only [CollatzResearch.WordTrace]
  refine ⟨20699264322968571056899223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13799509548645714037932815 20699264322968571056899223)
  ·
    refine ⟨31048896484452856585348835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20699264322968571056899223 31048896484452856585348835)
    ·
      refine ⟨46573344726679284878023253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31048896484452856585348835 46573344726679284878023253)
      ·
        refine ⟨545781383515772869664335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 46573344726679284878023253 545781383515772869664335)
        ·
          refine ⟨818672075273659304496503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545781383515772869664335 818672075273659304496503)
          ·
            refine ⟨1228008112910488956744755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818672075273659304496503 1228008112910488956744755)
            ·
              refine ⟨1842012169365733435117133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228008112910488956744755 1842012169365733435117133)
              ·
                refine ⟨690754563512150038168925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1842012169365733435117133 690754563512150038168925)
                ·
                  refine ⟨259032961317056264313347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 690754563512150038168925 259032961317056264313347)
                  ·
                    rfl

theorem cell20_567523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 3].length) (baseStart_567523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567523 prefixEnd_567523 := by exact prefixLift 567523
  have htrace : WordTrace (prefixWord ++ tailWord_567523) baseStart_567523 baseEnd_567523 := by
    simpa [prefixWord, tailWord_567523, baseEnd_567523] using wordTrace_append hprefix tailTrace_567523
  have hstable : (prefixWord ++ tailWord_567523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567523).length < 2 ^ (prefixWord ++ tailWord_567523).sum := by decide
  have hdescent : baseEnd_567523 < baseStart_567523 := by decide
  rcases family_descends (prefixWord ++ tailWord_567523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567534 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_567534 : Nat := 118140960795 + 567534 * 2 ^ 59
def prefixEnd_567534 : Nat := 4983230072969 + 3 ^ 40 * 567534 * 2
def baseEnd_567534 : Nat := 259037982016789114946635

theorem tailTrace_567534 : CollatzResearch.WordTrace tailWord_567534 prefixEnd_567534 259037982016789114946635 := by
  unfold tailWord_567534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2587458190741089991943707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13799777017285813290366437 2587458190741089991943707)
  ·
    refine ⟨3881187286111634987915561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2587458190741089991943707 3881187286111634987915561)
    ·
      refine ⟨2910890464583726240936671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3881187286111634987915561 2910890464583726240936671)
      ·
        refine ⟨4366335696875589361405007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2910890464583726240936671 4366335696875589361405007)
        ·
          refine ⟨6549503545313384042107511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4366335696875589361405007 6549503545313384042107511)
          ·
            refine ⟨9824255317970076063161267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6549503545313384042107511 9824255317970076063161267)
            ·
              refine ⟨14736382976955114094741901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9824255317970076063161267 14736382976955114094741901)
              ·
                refine ⟨5526143616358167785528213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14736382976955114094741901 5526143616358167785528213)
                ·
                  refine ⟨259037982016789114946635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5526143616358167785528213 259037982016789114946635)
                  ·
                    rfl

theorem cell20_567534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_567534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567534 prefixEnd_567534 := by exact prefixLift 567534
  have htrace : WordTrace (prefixWord ++ tailWord_567534) baseStart_567534 baseEnd_567534 := by
    simpa [prefixWord, tailWord_567534, baseEnd_567534] using wordTrace_append hprefix tailTrace_567534
  have hstable : (prefixWord ++ tailWord_567534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567534).length < 2 ^ (prefixWord ++ tailWord_567534).sum := by decide
  have hdescent : baseEnd_567534 < baseStart_567534 := by decide
  rcases family_descends (prefixWord ++ tailWord_567534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567551 : List Nat := [1, 1, 2, 2, 1, 4, 2, 5, 2]
def baseStart_567551 : Nat := 118140960795 + 567551 * 2 ^ 59
def prefixEnd_567551 : Nat := 4983230072969 + 3 ^ 40 * 567551 * 2
def baseEnd_567551 : Nat := 259045741280012611379899

theorem tailTrace_567551 : CollatzResearch.WordTrace tailWord_567551 prefixEnd_567551 259045741280012611379899 := by
  unfold tailWord_567551
  simp only [CollatzResearch.WordTrace]
  refine ⟨20700285566867131838918507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13800190377911421225945671 20700285566867131838918507)
  ·
    refine ⟨31050428350300697758377761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20700285566867131838918507 31050428350300697758377761)
    ·
      refine ⟨23287821262725523318783321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31050428350300697758377761 23287821262725523318783321)
      ·
        refine ⟨17465865947044142489087491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23287821262725523318783321 17465865947044142489087491)
        ·
          refine ⟨26198798920566213733631237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17465865947044142489087491 26198798920566213733631237)
          ·
            refine ⟨4912274797606165075055857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26198798920566213733631237 4912274797606165075055857)
            ·
              refine ⟨3684206098204623806291893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4912274797606165075055857 3684206098204623806291893)
              ·
                refine ⟨345394321706683481839865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3684206098204623806291893 345394321706683481839865)
                ·
                  refine ⟨259045741280012611379899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345394321706683481839865 259045741280012611379899)
                  ·
                    rfl

theorem cell20_567551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 2].length) (baseStart_567551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567551 prefixEnd_567551 := by exact prefixLift 567551
  have htrace : WordTrace (prefixWord ++ tailWord_567551) baseStart_567551 baseEnd_567551 := by
    simpa [prefixWord, tailWord_567551, baseEnd_567551] using wordTrace_append hprefix tailTrace_567551
  have hstable : (prefixWord ++ tailWord_567551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567551).length < 2 ^ (prefixWord ++ tailWord_567551).sum := by decide
  have hdescent : baseEnd_567551 < baseStart_567551 := by decide
  rcases family_descends (prefixWord ++ tailWord_567551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567579 : List Nat := [1, 1, 1, 1, 1, 1, 9, 5]
def baseStart_567579 : Nat := 118140960795 + 567579 * 2 ^ 59
def prefixEnd_567579 : Nat := 4983230072969 + 3 ^ 40 * 567579 * 2
def baseEnd_567579 : Nat := 86352840414322986148817

theorem tailTrace_567579 : CollatzResearch.WordTrace tailWord_567579 prefixEnd_567579 86352840414322986148817 := by
  unfold tailWord_567579
  simp only [CollatzResearch.WordTrace]
  refine ⟨20701306810765692620937791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13800871207177128413958527 20701306810765692620937791)
  ·
    refine ⟨31051960216148538931406687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20701306810765692620937791 31051960216148538931406687)
    ·
      refine ⟨46577940324222808397110031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31051960216148538931406687 46577940324222808397110031)
      ·
        refine ⟨69866910486334212595665047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46577940324222808397110031 69866910486334212595665047)
        ·
          refine ⟨104800365729501318893497571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69866910486334212595665047 104800365729501318893497571)
          ·
            refine ⟨157200548594251978340246357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104800365729501318893497571 157200548594251978340246357)
            ·
              refine ⟨921096964419445185587381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 157200548594251978340246357 921096964419445185587381)
              ·
                refine ⟨86352840414322986148817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 921096964419445185587381 86352840414322986148817)
                ·
                  rfl

theorem cell20_567579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 5].length) (baseStart_567579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567579 prefixEnd_567579 := by exact prefixLift 567579
  have htrace : WordTrace (prefixWord ++ tailWord_567579) baseStart_567579 baseEnd_567579 := by
    simpa [prefixWord, tailWord_567579, baseEnd_567579] using wordTrace_append hprefix tailTrace_567579
  have hstable : (prefixWord ++ tailWord_567579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567579).length < 2 ^ (prefixWord ++ tailWord_567579).sum := by decide
  have hdescent : baseEnd_567579 < baseStart_567579 := by decide
  rcases family_descends (prefixWord ++ tailWord_567579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567589 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 4]
def baseStart_567589 : Nat := 118140960795 + 567589 * 2 ^ 59
def prefixEnd_567589 : Nat := 4983230072969 + 3 ^ 40 * 567589 * 2
def baseEnd_567589 : Nat := 259063085515453368113077

theorem tailTrace_567589 : CollatzResearch.WordTrace tailWord_567589 prefixEnd_567589 259063085515453368113077 := by
  unfold tailWord_567589
  simp only [CollatzResearch.WordTrace]
  refine ⟨20701671540729464328801821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13801114360486309552534547 20701671540729464328801821)
  ·
    refine ⟨7763126827773549123300683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20701671540729464328801821 7763126827773549123300683)
    ·
      refine ⟨11644690241660323684951025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7763126827773549123300683 11644690241660323684951025)
      ·
        refine ⟨8733517681245242763713269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11644690241660323684951025 8733517681245242763713269)
        ·
          refine ⟨818767282616741509098119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8733517681245242763713269 818767282616741509098119)
          ·
            refine ⟨1228150923925112263647179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818767282616741509098119 1228150923925112263647179)
            ·
              refine ⟨1842226385887668395470769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228150923925112263647179 1842226385887668395470769)
              ·
                refine ⟨1381669789415751296603077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1842226385887668395470769 1381669789415751296603077)
                ·
                  refine ⟨259063085515453368113077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1381669789415751296603077 259063085515453368113077)
                  ·
                    rfl

theorem cell20_567589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_567589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567589 prefixEnd_567589 := by exact prefixLift 567589
  have htrace : WordTrace (prefixWord ++ tailWord_567589) baseStart_567589 baseEnd_567589 := by
    simpa [prefixWord, tailWord_567589, baseEnd_567589] using wordTrace_append hprefix tailTrace_567589
  have hstable : (prefixWord ++ tailWord_567589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567589).length < 2 ^ (prefixWord ++ tailWord_567589).sum := by decide
  have hdescent : baseEnd_567589 < baseStart_567589 := by decide
  rcases family_descends (prefixWord ++ tailWord_567589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567637 : List Nat := [1, 3, 2, 2, 4, 1, 3, 1, 3]
def baseStart_567637 : Nat := 118140960795 + 567637 * 2 ^ 59
def prefixEnd_567637 : Nat := 4983230072969 + 3 ^ 40 * 567637 * 2
def baseEnd_567637 : Nat := 259084994023378534512881

theorem tailTrace_567637 : CollatzResearch.WordTrace tailWord_567637 prefixEnd_567637 259084994023378534512881 := by
  unfold tailWord_567637
  simp only [CollatzResearch.WordTrace]
  refine ⟨20703422244555568526549165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13802281496370379017699443 20703422244555568526549165)
  ·
    refine ⟨7763783341708338197455937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20703422244555568526549165 7763783341708338197455937)
    ·
      refine ⟨5822837506281253648091953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7763783341708338197455937 5822837506281253648091953)
      ·
        refine ⟨4367128129710940236068965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5822837506281253648091953 4367128129710940236068965)
        ·
          refine ⟨818836524320801294262931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4367128129710940236068965 818836524320801294262931)
          ·
            refine ⟨1228254786481201941394397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818836524320801294262931 1228254786481201941394397)
            ·
              refine ⟨460595544930450728022899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1228254786481201941394397 460595544930450728022899)
              ·
                refine ⟨690893317395676092034349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460595544930450728022899 690893317395676092034349)
                ·
                  refine ⟨259084994023378534512881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 690893317395676092034349 259084994023378534512881)
                  ·
                    rfl

theorem cell20_567637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_567637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567637 prefixEnd_567637 := by exact prefixLift 567637
  have htrace : WordTrace (prefixWord ++ tailWord_567637) baseStart_567637 baseEnd_567637 := by
    simpa [prefixWord, tailWord_567637, baseEnd_567637] using wordTrace_append hprefix tailTrace_567637
  have hstable : (prefixWord ++ tailWord_567637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567637).length < 2 ^ (prefixWord ++ tailWord_567637).sum := by decide
  have hdescent : baseEnd_567637 < baseStart_567637 := by decide
  rcases family_descends (prefixWord ++ tailWord_567637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567737 : List Nat := [1, 2, 1, 4, 3, 3, 2, 2, 2]
def baseStart_567737 : Nat := 118140960795 + 567737 * 2 ^ 59
def prefixEnd_567737 : Nat := 4983230072969 + 3 ^ 40 * 567737 * 2
def baseEnd_567737 : Nat := 259130636748222631179139

theorem tailTrace_567737 : CollatzResearch.WordTrace tailWord_567737 prefixEnd_567737 259130636748222631179139 := by
  unfold tailWord_567737
  simp only [CollatzResearch.WordTrace]
  refine ⟨20707069544193285605189465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13804713029462190403459643 20707069544193285605189465)
  ·
    refine ⟨15530302158144964203892099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20707069544193285605189465 15530302158144964203892099)
    ·
      refine ⟨23295453237217446305838149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15530302158144964203892099 23295453237217446305838149)
      ·
        refine ⟨4367897481978271182344653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23295453237217446305838149 4367897481978271182344653)
        ·
          refine ⟨1637961555741851693379245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4367897481978271182344653 1637961555741851693379245)
          ·
            refine ⟨614235583403194385017217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1637961555741851693379245 614235583403194385017217)
            ·
              refine ⟨460676687552395788762913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 614235583403194385017217 460676687552395788762913)
              ·
                refine ⟨345507515664296841572185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 460676687552395788762913 345507515664296841572185)
                ·
                  refine ⟨259130636748222631179139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345507515664296841572185 259130636748222631179139)
                  ·
                    rfl

theorem cell20_567737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 2].length) (baseStart_567737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567737 prefixEnd_567737 := by exact prefixLift 567737
  have htrace : WordTrace (prefixWord ++ tailWord_567737) baseStart_567737 baseEnd_567737 := by
    simpa [prefixWord, tailWord_567737, baseEnd_567737] using wordTrace_append hprefix tailTrace_567737
  have hstable : (prefixWord ++ tailWord_567737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567737).length < 2 ^ (prefixWord ++ tailWord_567737).sum := by decide
  have hdescent : baseEnd_567737 < baseStart_567737 := by decide
  rcases family_descends (prefixWord ++ tailWord_567737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567738 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_567738 : Nat := 118140960795 + 567738 * 2 ^ 59
def prefixEnd_567738 : Nat := 4983230072969 + 3 ^ 40 * 567738 * 2
def baseEnd_567738 : Nat := 259131093175471072145801

theorem tailTrace_567738 : CollatzResearch.WordTrace tailWord_567738 prefixEnd_567738 259131093175471072145801 := by
  unfold tailWord_567738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5176776504297415693993967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13804737344793108517317245 5176776504297415693993967)
  ·
    refine ⟨7765164756446123540990951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5176776504297415693993967 7765164756446123540990951)
    ·
      refine ⟨11647747134669185311486427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7765164756446123540990951 11647747134669185311486427)
      ·
        refine ⟨17471620702003777967229641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11647747134669185311486427 17471620702003777967229641)
        ·
          refine ⟨13103715526502833475422231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17471620702003777967229641 13103715526502833475422231)
          ·
            refine ⟨19655573289754250213133347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13103715526502833475422231 19655573289754250213133347)
            ·
              refine ⟨29483359934631375319700021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19655573289754250213133347 29483359934631375319700021)
              ·
                refine ⟨2764064993871691436221877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29483359934631375319700021 2764064993871691436221877)
                ·
                  refine ⟨259131093175471072145801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2764064993871691436221877 259131093175471072145801)
                  ·
                    rfl

theorem cell20_567738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_567738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567738 prefixEnd_567738 := by exact prefixLift 567738
  have htrace : WordTrace (prefixWord ++ tailWord_567738) baseStart_567738 baseEnd_567738 := by
    simpa [prefixWord, tailWord_567738, baseEnd_567738] using wordTrace_append hprefix tailTrace_567738
  have hstable : (prefixWord ++ tailWord_567738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567738).length < 2 ^ (prefixWord ++ tailWord_567738).sum := by decide
  have hdescent : baseEnd_567738 < baseStart_567738 := by decide
  rcases family_descends (prefixWord ++ tailWord_567738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567776 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 5]
def baseStart_567776 : Nat := 118140960795 + 567776 * 2 ^ 59
def prefixEnd_567776 : Nat := 4983230072969 + 3 ^ 40 * 567776 * 2
def baseEnd_567776 : Nat := 259148437410911828878979

theorem tailTrace_567776 : CollatzResearch.WordTrace tailWord_567776 prefixEnd_567776 259148437410911828878979 := by
  unfold tailWord_567776
  simp only [CollatzResearch.WordTrace]
  refine ⟨10354245995525997632929591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13805661327367996843906121 10354245995525997632929591)
  ·
    refine ⟨15531368993288996449394387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10354245995525997632929591 15531368993288996449394387)
    ·
      refine ⟨23297053489933494674091581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15531368993288996449394387 23297053489933494674091581)
      ·
        refine ⟨8736395058725060502784343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23297053489933494674091581 8736395058725060502784343)
        ·
          refine ⟨13104592588087590754176515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8736395058725060502784343 13104592588087590754176515)
          ·
            refine ⟨19656888882131386131264773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13104592588087590754176515 19656888882131386131264773)
            ·
              refine ⟨3685666665399634899612145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19656888882131386131264773 3685666665399634899612145)
              ·
                refine ⟨2764249999049726174709109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3685666665399634899612145 2764249999049726174709109)
                ·
                  refine ⟨259148437410911828878979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2764249999049726174709109 259148437410911828878979)
                  ·
                    rfl

theorem cell20_567776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_567776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567776 prefixEnd_567776 := by exact prefixLift 567776
  have htrace : WordTrace (prefixWord ++ tailWord_567776) baseStart_567776 baseEnd_567776 := by
    simpa [prefixWord, tailWord_567776, baseEnd_567776] using wordTrace_append hprefix tailTrace_567776
  have hstable : (prefixWord ++ tailWord_567776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567776).length < 2 ^ (prefixWord ++ tailWord_567776).sum := by decide
  have hdescent : baseEnd_567776 < baseStart_567776 := by decide
  rcases family_descends (prefixWord ++ tailWord_567776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567789 : List Nat := [1, 5, 1, 3, 1, 3, 1, 2, 3]
def baseStart_567789 : Nat := 118140960795 + 567789 * 2 ^ 59
def prefixEnd_567789 : Nat := 4983230072969 + 3 ^ 40 * 567789 * 2
def baseEnd_567789 : Nat := 259154370965141561445593

theorem tailTrace_567789 : CollatzResearch.WordTrace tailWord_567789 prefixEnd_567789 259154370965141561445593 := by
  unfold tailWord_567789
  simp only [CollatzResearch.WordTrace]
  refine ⟨20708966140004898486082421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13805977426669932324054947 20708966140004898486082421)
  ·
    refine ⟨1941465575625459233070227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20708966140004898486082421 1941465575625459233070227)
    ·
      refine ⟨2912198363438188849605341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1941465575625459233070227 2912198363438188849605341)
      ·
        refine ⟨1092074386289320818602003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2912198363438188849605341 1092074386289320818602003)
        ·
          refine ⟨1638111579433981227903005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1092074386289320818602003 1638111579433981227903005)
          ·
            refine ⟨614291842287742960463627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1638111579433981227903005 614291842287742960463627)
            ·
              refine ⟨921437763431614440695441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 614291842287742960463627 921437763431614440695441)
              ·
                refine ⟨691078322573710830521581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 921437763431614440695441 691078322573710830521581)
                ·
                  refine ⟨259154370965141561445593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691078322573710830521581 259154370965141561445593)
                  ·
                    rfl

theorem cell20_567789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_567789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567789 prefixEnd_567789 := by exact prefixLift 567789
  have htrace : WordTrace (prefixWord ++ tailWord_567789) baseStart_567789 baseEnd_567789 := by
    simpa [prefixWord, tailWord_567789, baseEnd_567789] using wordTrace_append hprefix tailTrace_567789
  have hstable : (prefixWord ++ tailWord_567789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567789).length < 2 ^ (prefixWord ++ tailWord_567789).sum := by decide
  have hdescent : baseEnd_567789 < baseStart_567789 := by decide
  rcases family_descends (prefixWord ++ tailWord_567789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567800 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 4]
def baseStart_567800 : Nat := 118140960795 + 567800 * 2 ^ 59
def prefixEnd_567800 : Nat := 4983230072969 + 3 ^ 40 * 567800 * 2
def baseEnd_567800 : Nat := 259159391664874412078881

theorem tailTrace_567800 : CollatzResearch.WordTrace tailWord_567800 prefixEnd_567800 259159391664874412078881 := by
  unfold tailWord_567800
  simp only [CollatzResearch.WordTrace]
  refine ⟨10354683671482523682366427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13806244895310031576488569 10354683671482523682366427)
  ·
    refine ⟨15532025507223785523549641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10354683671482523682366427 15532025507223785523549641)
    ·
      refine ⟨11649019130417839142662231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15532025507223785523549641 11649019130417839142662231)
      ·
        refine ⟨17473528695626758713993347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11649019130417839142662231 17473528695626758713993347)
        ·
          refine ⟨26210293043440138070990021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17473528695626758713993347 26210293043440138070990021)
          ·
            refine ⟨4914429945645025888310629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26210293043440138070990021 4914429945645025888310629)
            ·
              refine ⟨921455614808442354058243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4914429945645025888310629 921455614808442354058243)
              ·
                refine ⟨1382183422212663531087365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921455614808442354058243 1382183422212663531087365)
                ·
                  refine ⟨259159391664874412078881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1382183422212663531087365 259159391664874412078881)
                  ·
                    rfl

theorem cell20_567800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_567800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567800 prefixEnd_567800 := by exact prefixLift 567800
  have htrace : WordTrace (prefixWord ++ tailWord_567800) baseStart_567800 baseEnd_567800 := by
    simpa [prefixWord, tailWord_567800, baseEnd_567800] using wordTrace_append hprefix tailTrace_567800
  have hstable : (prefixWord ++ tailWord_567800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567800).length < 2 ^ (prefixWord ++ tailWord_567800).sum := by decide
  have hdescent : baseEnd_567800 < baseStart_567800 := by decide
  rcases family_descends (prefixWord ++ tailWord_567800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567862 : List Nat := [5, 1, 2, 1, 2, 1, 1, 7]
def baseStart_567862 : Nat := 118140960795 + 567862 * 2 ^ 59
def prefixEnd_567862 : Nat := 4983230072969 + 3 ^ 40 * 567862 * 2
def baseEnd_567862 : Nat := 86395896718092584003987

theorem tailTrace_567862 : CollatzResearch.WordTrace tailWord_567862 prefixEnd_567862 86395896718092584003987 := by
  unfold tailWord_567862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1294476791796276997093115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13807752445826954635659893 1294476791796276997093115)
  ·
    refine ⟨1941715187694415495639673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1294476791796276997093115 1941715187694415495639673)
    ·
      refine ⟨1456286390770811621729755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1941715187694415495639673 1456286390770811621729755)
      ·
        refine ⟨2184429586156217432594633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1456286390770811621729755 2184429586156217432594633)
        ·
          refine ⟨1638322189617163074445975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2184429586156217432594633 1638322189617163074445975)
          ·
            refine ⟨2457483284425744611668963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638322189617163074445975 2457483284425744611668963)
            ·
              refine ⟨3686224926638616917503445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2457483284425744611668963 3686224926638616917503445)
              ·
                refine ⟨86395896718092584003987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3686224926638616917503445 86395896718092584003987)
                ·
                  rfl

theorem cell20_567862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_567862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567862 prefixEnd_567862 := by exact prefixLift 567862
  have htrace : WordTrace (prefixWord ++ tailWord_567862) baseStart_567862 baseEnd_567862 := by
    simpa [prefixWord, tailWord_567862, baseEnd_567862] using wordTrace_append hprefix tailTrace_567862
  have hstable : (prefixWord ++ tailWord_567862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567862).length < 2 ^ (prefixWord ++ tailWord_567862).sum := by decide
  have hdescent : baseEnd_567862 < baseStart_567862 := by decide
  rcases family_descends (prefixWord ++ tailWord_567862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567900 : List Nat := [2, 2, 4, 1, 4, 7]
def baseStart_567900 : Nat := 118140960795 + 567900 * 2 ^ 59
def prefixEnd_567900 : Nat := 4983230072969 + 3 ^ 40 * 567900 * 2
def baseEnd_567900 : Nat := 9600186458878463286857

theorem tailTrace_567900 : CollatzResearch.WordTrace tailWord_567900 prefixEnd_567900 9600186458878463286857 := by
  unfold tailWord_567900
  simp only [CollatzResearch.WordTrace]
  refine ⟨10356507321301382221686577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13808676428401842962248769 10356507321301382221686577)
  ·
    refine ⟨7767380490976036666264933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10356507321301382221686577 7767380490976036666264933)
    ·
      refine ⟨1456383842058006874924675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7767380490976036666264933 1456383842058006874924675)
      ·
        refine ⟨2184575763087010312387013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1456383842058006874924675 2184575763087010312387013)
        ·
          refine ⟨409607955578814433572565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2184575763087010312387013 409607955578814433572565)
          ·
            refine ⟨9600186458878463286857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 409607955578814433572565 9600186458878463286857)
            ·
              rfl

theorem cell20_567900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 7].length) (baseStart_567900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567900 prefixEnd_567900 := by exact prefixLift 567900
  have htrace : WordTrace (prefixWord ++ tailWord_567900) baseStart_567900 baseEnd_567900 := by
    simpa [prefixWord, tailWord_567900, baseEnd_567900] using wordTrace_append hprefix tailTrace_567900
  have hstable : (prefixWord ++ tailWord_567900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567900).length < 2 ^ (prefixWord ++ tailWord_567900).sum := by decide
  have hdescent : baseEnd_567900 < baseStart_567900 := by decide
  rcases family_descends (prefixWord ++ tailWord_567900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567902 : List Nat := [4, 4, 1, 2, 1, 2, 2, 2, 2]
def baseStart_567902 : Nat := 118140960795 + 567902 * 2 ^ 59
def prefixEnd_567902 : Nat := 4983230072969 + 3 ^ 40 * 567902 * 2
def baseEnd_567902 : Nat := 259205947244215390678465

theorem tailTrace_567902 : CollatzResearch.WordTrace tailWord_567902 prefixEnd_567902 259205947244215390678465 := by
  unfold tailWord_567902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2589135948574439848118245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13808725059063679189963973 2589135948574439848118245)
  ·
    refine ⟨485462990357707471522171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2589135948574439848118245 485462990357707471522171)
    ·
      refine ⟨728194485536561207283257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 485462990357707471522171 728194485536561207283257)
      ·
        refine ⟨546145864152420905462443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 728194485536561207283257 546145864152420905462443)
        ·
          refine ⟨819218796228631358193665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546145864152420905462443 819218796228631358193665)
          ·
            refine ⟨614414097171473518645249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 819218796228631358193665 614414097171473518645249)
            ·
              refine ⟨460810572878605138983937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 614414097171473518645249 460810572878605138983937)
              ·
                refine ⟨345607929658953854237953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 460810572878605138983937 345607929658953854237953)
                ·
                  refine ⟨259205947244215390678465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345607929658953854237953 259205947244215390678465)
                  ·
                    rfl

theorem cell20_567902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_567902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567902 prefixEnd_567902 := by exact prefixLift 567902
  have htrace : WordTrace (prefixWord ++ tailWord_567902) baseStart_567902 baseEnd_567902 := by
    simpa [prefixWord, tailWord_567902, baseEnd_567902] using wordTrace_append hprefix tailTrace_567902
  have hstable : (prefixWord ++ tailWord_567902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567902).length < 2 ^ (prefixWord ++ tailWord_567902).sum := by decide
  have hdescent : baseEnd_567902 < baseStart_567902 := by decide
  rcases family_descends (prefixWord ++ tailWord_567902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567907 : List Nat := [1, 1, 1, 5, 1, 2, 4, 2, 3]
def baseStart_567907 : Nat := 118140960795 + 567907 * 2 ^ 59
def prefixEnd_567907 : Nat := 4983230072969 + 3 ^ 40 * 567907 * 2
def baseEnd_567907 : Nat := 259208229380457595511777

theorem tailTrace_567907 : CollatzResearch.WordTrace tailWord_567907 prefixEnd_567907 259208229380457595511777 := by
  unfold tailWord_567907
  simp only [CollatzResearch.WordTrace]
  refine ⟨20713269953577404638877975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13808846635718269759251983 20713269953577404638877975)
  ·
    refine ⟨31069904930366106958316963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20713269953577404638877975 31069904930366106958316963)
    ·
      refine ⟨46604857395549160437475445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31069904930366106958316963 46604857395549160437475445)
      ·
        refine ⟨4369205380832733791013323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46604857395549160437475445 4369205380832733791013323)
        ·
          refine ⟨6553808071249100686519985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4369205380832733791013323 6553808071249100686519985)
          ·
            refine ⟨4915356053436825514889989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6553808071249100686519985 4915356053436825514889989)
            ·
              refine ⟨921629260019404784041873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4915356053436825514889989 921629260019404784041873)
              ·
                refine ⟨691221945014553588031405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 921629260019404784041873 691221945014553588031405)
                ·
                  refine ⟨259208229380457595511777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691221945014553588031405 259208229380457595511777)
                  ·
                    rfl

theorem cell20_567907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 3].length) (baseStart_567907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567907 prefixEnd_567907 := by exact prefixLift 567907
  have htrace : WordTrace (prefixWord ++ tailWord_567907) baseStart_567907 baseEnd_567907 := by
    simpa [prefixWord, tailWord_567907, baseEnd_567907] using wordTrace_append hprefix tailTrace_567907
  have hstable : (prefixWord ++ tailWord_567907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567907).length < 2 ^ (prefixWord ++ tailWord_567907).sum := by decide
  have hdescent : baseEnd_567907 < baseStart_567907 := by decide
  rcases family_descends (prefixWord ++ tailWord_567907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567914 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_567914 : Nat := 118140960795 + 567914 * 2 ^ 59
def prefixEnd_567914 : Nat := 4983230072969 + 3 ^ 40 * 567914 * 2
def baseEnd_567914 : Nat := 259211424371196682278415

theorem tailTrace_567914 : CollatzResearch.WordTrace tailWord_567914 prefixEnd_567914 259211424371196682278415 := by
  unfold tailWord_567914
  simp only [CollatzResearch.WordTrace]
  refine ⟨5178381316138011208595699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13809016843034696556255197 5178381316138011208595699)
  ·
    refine ⟨7767571974207016812893549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5178381316138011208595699 7767571974207016812893549)
    ·
      refine ⟨2912839490327631304835081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7767571974207016812893549 2912839490327631304835081)
      ·
        refine ⟨2184629617745723478626311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2912839490327631304835081 2184629617745723478626311)
        ·
          refine ⟨3276944426618585217939467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2184629617745723478626311 3276944426618585217939467)
          ·
            refine ⟨4915416639927877826909201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276944426618585217939467 4915416639927877826909201)
            ·
              refine ⟨3686562479945908370181901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4915416639927877826909201 3686562479945908370181901)
              ·
                refine ⟨1382460929979715638818213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3686562479945908370181901 1382460929979715638818213)
                ·
                  refine ⟨259211424371196682278415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1382460929979715638818213 259211424371196682278415)
                  ·
                    rfl

theorem cell20_567914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_567914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567914 prefixEnd_567914 := by exact prefixLift 567914
  have htrace : WordTrace (prefixWord ++ tailWord_567914) baseStart_567914 baseEnd_567914 := by
    simpa [prefixWord, tailWord_567914, baseEnd_567914] using wordTrace_append hprefix tailTrace_567914
  have hstable : (prefixWord ++ tailWord_567914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567914).length < 2 ^ (prefixWord ++ tailWord_567914).sum := by decide
  have hdescent : baseEnd_567914 < baseStart_567914 := by decide
  rcases family_descends (prefixWord ++ tailWord_567914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567962 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 5]
def baseStart_567962 : Nat := 118140960795 + 567962 * 2 ^ 59
def prefixEnd_567962 : Nat := 4983230072969 + 3 ^ 40 * 567962 * 2
def baseEnd_567962 : Nat := 259233332879121848678219

theorem tailTrace_567962 : CollatzResearch.WordTrace tailWord_567962 prefixEnd_567962 259233332879121848678219 := by
  unfold tailWord_567962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5178818992094537258032535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13810183978918766021420093 5178818992094537258032535)
  ·
    refine ⟨7768228488141805887048803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5178818992094537258032535 7768228488141805887048803)
    ·
      refine ⟨11652342732212708830573205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7768228488141805887048803 11652342732212708830573205)
      ·
        refine ⟨546203565572470726433119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11652342732212708830573205 546203565572470726433119)
        ·
          refine ⟨819305348358706089649679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546203565572470726433119 819305348358706089649679)
          ·
            refine ⟨1228958022538059134474519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819305348358706089649679 1228958022538059134474519)
            ·
              refine ⟨1843437033807088701711779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228958022538059134474519 1843437033807088701711779)
              ·
                refine ⟨2765155550710633052567669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843437033807088701711779 2765155550710633052567669)
                ·
                  refine ⟨259233332879121848678219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2765155550710633052567669 259233332879121848678219)
                  ·
                    rfl

theorem cell20_567962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_567962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567962 prefixEnd_567962 := by exact prefixLift 567962
  have htrace : WordTrace (prefixWord ++ tailWord_567962) baseStart_567962 baseEnd_567962 := by
    simpa [prefixWord, tailWord_567962, baseEnd_567962] using wordTrace_append hprefix tailTrace_567962
  have hstable : (prefixWord ++ tailWord_567962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567962).length < 2 ^ (prefixWord ++ tailWord_567962).sum := by decide
  have hdescent : baseEnd_567962 < baseStart_567962 := by decide
  rcases family_descends (prefixWord ++ tailWord_567962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567969 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 4]
def baseStart_567969 : Nat := 118140960795 + 567969 * 2 ^ 59
def prefixEnd_567969 : Nat := 4983230072969 + 3 ^ 40 * 567969 * 2
def baseEnd_567969 : Nat := 259236527869860935444857

theorem tailTrace_567969 : CollatzResearch.WordTrace tailWord_567969 prefixEnd_567969 259236527869860935444857 := by
  unfold tailWord_567969
  simp only [CollatzResearch.WordTrace]
  refine ⟨20715531279352789227634961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13810354186235192818423307 20715531279352789227634961)
  ·
    refine ⟨15536648459514591920726221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20715531279352789227634961 15536648459514591920726221)
    ·
      refine ⟨5826243172317971970272333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15536648459514591920726221 5826243172317971970272333)
      ·
        refine ⟨2184841189619239488852125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5826243172317971970272333 2184841189619239488852125)
        ·
          refine ⟨819315446107214808319547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2184841189619239488852125 819315446107214808319547)
          ·
            refine ⟨1228973169160822212479321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819315446107214808319547 1228973169160822212479321)
            ·
              refine ⟨921729876870616659359491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1228973169160822212479321 921729876870616659359491)
              ·
                refine ⟨1382594815305924989039237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921729876870616659359491 1382594815305924989039237)
                ·
                  refine ⟨259236527869860935444857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1382594815305924989039237 259236527869860935444857)
                  ·
                    rfl

theorem cell20_567969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_567969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567969 prefixEnd_567969 := by exact prefixLift 567969
  have htrace : WordTrace (prefixWord ++ tailWord_567969) baseStart_567969 baseEnd_567969 := by
    simpa [prefixWord, tailWord_567969, baseEnd_567969] using wordTrace_append hprefix tailTrace_567969
  have hstable : (prefixWord ++ tailWord_567969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567969).length < 2 ^ (prefixWord ++ tailWord_567969).sum := by decide
  have hdescent : baseEnd_567969 < baseStart_567969 := by decide
  rcases family_descends (prefixWord ++ tailWord_567969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567997 : List Nat := [1, 4, 1, 2, 1, 4, 1, 6]
def baseStart_567997 : Nat := 118140960795 + 567997 * 2 ^ 59
def prefixEnd_567997 : Nat := 4983230072969 + 3 ^ 40 * 567997 * 2
def baseEnd_567997 : Nat := 86416435944272427503803

theorem tailTrace_567997 : CollatzResearch.WordTrace tailWord_567997 prefixEnd_567997 86416435944272427503803 := by
  unfold tailWord_567997
  simp only [CollatzResearch.WordTrace]
  refine ⟨20716552523251350009654245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13811035015500900006436163 20716552523251350009654245)
  ·
    refine ⟨3884353598109628126810171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20716552523251350009654245 3884353598109628126810171)
    ·
      refine ⟨5826530397164442190215257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3884353598109628126810171 5826530397164442190215257)
      ·
        refine ⟨4369897797873331642661443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5826530397164442190215257 4369897797873331642661443)
        ·
          refine ⟨6554846696809997463992165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4369897797873331642661443 6554846696809997463992165)
          ·
            refine ⟨1229033755651874524498531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6554846696809997463992165 1229033755651874524498531)
            ·
              refine ⟨1843550633477811786747797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229033755651874524498531 1843550633477811786747797)
              ·
                refine ⟨86416435944272427503803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1843550633477811786747797 86416435944272427503803)
                ·
                  rfl

theorem cell20_567997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 6].length) (baseStart_567997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_567997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_567997 prefixEnd_567997 := by exact prefixLift 567997
  have htrace : WordTrace (prefixWord ++ tailWord_567997) baseStart_567997 baseEnd_567997 := by
    simpa [prefixWord, tailWord_567997, baseEnd_567997] using wordTrace_append hprefix tailTrace_567997
  have hstable : (prefixWord ++ tailWord_567997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567997).length < 2 ^ (prefixWord ++ tailWord_567997).sum := by decide
  have hdescent : baseEnd_567997 < baseStart_567997 := by decide
  rcases family_descends (prefixWord ++ tailWord_567997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568024 : List Nat := [2, 1, 2, 2, 3, 3, 3, 2, 2]
def baseStart_568024 : Nat := 118140960795 + 568024 * 2 ^ 59
def prefixEnd_568024 : Nat := 4983230072969 + 3 ^ 40 * 568024 * 2
def baseEnd_568024 : Nat := 259261631368525188611299

theorem tailTrace_568024 : CollatzResearch.WordTrace tailWord_568024 prefixEnd_568024 259261631368525188611299 := by
  unfold tailWord_568024
  simp only [CollatzResearch.WordTrace]
  refine ⟨10358768647076766810443563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13811691529435689080591417 10358768647076766810443563)
  ·
    refine ⟨15538152970615150215665345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10358768647076766810443563 15538152970615150215665345)
    ·
      refine ⟨11653614727961362661749009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15538152970615150215665345 11653614727961362661749009)
      ·
        refine ⟨8740211045971021996311757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11653614727961362661749009 8740211045971021996311757)
        ·
          refine ⟨3277579142239133248616909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8740211045971021996311757 3277579142239133248616909)
          ·
            refine ⟨1229092178339674968231341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3277579142239133248616909 1229092178339674968231341)
            ·
              refine ⟨460909566877378113086753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1229092178339674968231341 460909566877378113086753)
              ·
                refine ⟨345682175158033584815065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 460909566877378113086753 345682175158033584815065)
                ·
                  refine ⟨259261631368525188611299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345682175158033584815065 259261631368525188611299)
                  ·
                    rfl

theorem cell20_568024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 2].length) (baseStart_568024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568024 prefixEnd_568024 := by exact prefixLift 568024
  have htrace : WordTrace (prefixWord ++ tailWord_568024) baseStart_568024 baseEnd_568024 := by
    simpa [prefixWord, tailWord_568024, baseEnd_568024] using wordTrace_append hprefix tailTrace_568024
  have hstable : (prefixWord ++ tailWord_568024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568024).length < 2 ^ (prefixWord ++ tailWord_568024).sum := by decide
  have hdescent : baseEnd_568024 < baseStart_568024 := by decide
  rcases family_descends (prefixWord ++ tailWord_568024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568035 : List Nat := [1, 1, 1, 7, 1, 1, 1, 7]
def baseStart_568035 : Nat := 118140960795 + 568035 * 2 ^ 59
def prefixEnd_568035 : Nat := 4983230072969 + 3 ^ 40 * 568035 * 2
def baseEnd_568035 : Nat := 86422217356086013081529

theorem tailTrace_568035 : CollatzResearch.WordTrace tailWord_568035 prefixEnd_568035 86422217356086013081529 := by
  unfold tailWord_568035
  simp only [CollatzResearch.WordTrace]
  refine ⟨20717938497113682499537559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13811958998075788333025039 20717938497113682499537559)
  ·
    refine ⟨31076907745670523749306339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20717938497113682499537559 31076907745670523749306339)
    ·
      refine ⟨46615361618505785623959509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31076907745670523749306339 46615361618505785623959509)
      ·
        refine ⟨1092547537933729350561551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 46615361618505785623959509 1092547537933729350561551)
        ·
          refine ⟨1638821306900594025842327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1092547537933729350561551 1638821306900594025842327)
          ·
            refine ⟨2458231960350891038763491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638821306900594025842327 2458231960350891038763491)
            ·
              refine ⟨3687347940526336558145237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2458231960350891038763491 3687347940526336558145237)
              ·
                refine ⟨86422217356086013081529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3687347940526336558145237 86422217356086013081529)
                ·
                  rfl

theorem cell20_568035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 7].length) (baseStart_568035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568035 prefixEnd_568035 := by exact prefixLift 568035
  have htrace : WordTrace (prefixWord ++ tailWord_568035) baseStart_568035 baseEnd_568035 := by
    simpa [prefixWord, tailWord_568035, baseEnd_568035] using wordTrace_append hprefix tailTrace_568035
  have hstable : (prefixWord ++ tailWord_568035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568035).length < 2 ^ (prefixWord ++ tailWord_568035).sum := by decide
  have hdescent : baseEnd_568035 < baseStart_568035 := by decide
  rcases family_descends (prefixWord ++ tailWord_568035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568049 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 6]
def baseStart_568049 : Nat := 118140960795 + 568049 * 2 ^ 59
def prefixEnd_568049 : Nat := 4983230072969 + 3 ^ 40 * 568049 * 2
def baseEnd_568049 : Nat := 259273042049736212777863

theorem tailTrace_568049 : CollatzResearch.WordTrace tailWord_568049 prefixEnd_568049 259273042049736212777863 := by
  unfold tailWord_568049
  simp only [CollatzResearch.WordTrace]
  refine ⟨20718449119062962890547201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13812299412708641927031467 20718449119062962890547201)
  ·
    refine ⟨15538836839297222167910401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20718449119062962890547201 15538836839297222167910401)
    ·
      refine ⟨11654127629472916625932801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15538836839297222167910401 11654127629472916625932801)
      ·
        refine ⟨8740595722104687469449601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11654127629472916625932801 8740595722104687469449601)
        ·
          refine ⟨6555446791578515602087201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8740595722104687469449601 6555446791578515602087201)
          ·
            refine ⟨4916585093683886701565401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6555446791578515602087201 4916585093683886701565401)
            ·
              refine ⟨3687438820262915026174051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4916585093683886701565401 3687438820262915026174051)
              ·
                refine ⟨5531158230394372539261077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3687438820262915026174051 5531158230394372539261077)
                ·
                  refine ⟨259273042049736212777863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5531158230394372539261077 259273042049736212777863)
                  ·
                    rfl

theorem cell20_568049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_568049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568049 prefixEnd_568049 := by exact prefixLift 568049
  have htrace : WordTrace (prefixWord ++ tailWord_568049) baseStart_568049 baseEnd_568049 := by
    simpa [prefixWord, tailWord_568049, baseEnd_568049] using wordTrace_append hprefix tailTrace_568049
  have hstable : (prefixWord ++ tailWord_568049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568049).length < 2 ^ (prefixWord ++ tailWord_568049).sum := by decide
  have hdescent : baseEnd_568049 < baseStart_568049 := by decide
  rcases family_descends (prefixWord ++ tailWord_568049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568056 : List Nat := [2, 1, 2, 1, 1, 2, 3, 8]
def baseStart_568056 : Nat := 118140960795 + 568056 * 2 ^ 59
def prefixEnd_568056 : Nat := 4983230072969 + 3 ^ 40 * 568056 * 2
def baseEnd_568056 : Nat := 86425412346825099848167

theorem tailTrace_568056 : CollatzResearch.WordTrace tailWord_568056 prefixEnd_568056 86425412346825099848167 := by
  unfold tailWord_568056
  simp only [CollatzResearch.WordTrace]
  refine ⟨10359352215018801543026011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13812469620025068724034681 10359352215018801543026011)
  ·
    refine ⟨15539028322528202314539017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10359352215018801543026011 15539028322528202314539017)
    ·
      refine ⟨11654271241896151735904263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15539028322528202314539017 11654271241896151735904263)
      ·
        refine ⟨17481406862844227603856395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11654271241896151735904263 17481406862844227603856395)
        ·
          refine ⟨26222110294266341405784593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17481406862844227603856395 26222110294266341405784593)
          ·
            refine ⟨19666582720699756054338445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26222110294266341405784593 19666582720699756054338445)
            ·
              refine ⟨7374968520262408520376917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19666582720699756054338445 7374968520262408520376917)
              ·
                refine ⟨86425412346825099848167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7374968520262408520376917 86425412346825099848167)
                ·
                  rfl

theorem cell20_568056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_568056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568056 prefixEnd_568056 := by exact prefixLift 568056
  have htrace : WordTrace (prefixWord ++ tailWord_568056) baseStart_568056 baseEnd_568056 := by
    simpa [prefixWord, tailWord_568056, baseEnd_568056] using wordTrace_append hprefix tailTrace_568056
  have hstable : (prefixWord ++ tailWord_568056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568056).length < 2 ^ (prefixWord ++ tailWord_568056).sum := by decide
  have hdescent : baseEnd_568056 < baseStart_568056 := by decide
  rcases family_descends (prefixWord ++ tailWord_568056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568104 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 4]
def baseStart_568104 : Nat := 118140960795 + 568104 * 2 ^ 59
def prefixEnd_568104 : Nat := 4983230072969 + 3 ^ 40 * 568104 * 2
def baseEnd_568104 : Nat := 259298145548400465944305

theorem tailTrace_568104 : CollatzResearch.WordTrace tailWord_568104 prefixEnd_568104 259298145548400465944305 := by
  unfold tailWord_568104
  simp only [CollatzResearch.WordTrace]
  refine ⟨10360227566931853641899683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13813636755909138189199577 10360227566931853641899683)
  ·
    refine ⟨15540341350397780462849525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10360227566931853641899683 15540341350397780462849525)
    ·
      refine ⟨1456907001599791918392143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15540341350397780462849525 1456907001599791918392143)
      ·
        refine ⟨2185360502399687877588215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1456907001599791918392143 2185360502399687877588215)
        ·
          refine ⟨3278040753599531816382323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2185360502399687877588215 3278040753599531816382323)
          ·
            refine ⟨4917061130399297724573485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3278040753599531816382323 4917061130399297724573485)
            ·
              refine ⟨1843897923899736646715057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4917061130399297724573485 1843897923899736646715057)
              ·
                refine ⟨1382923442924802485036293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1843897923899736646715057 1382923442924802485036293)
                ·
                  refine ⟨259298145548400465944305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1382923442924802485036293 259298145548400465944305)
                  ·
                    rfl

theorem cell20_568104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_568104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568104 prefixEnd_568104 := by exact prefixLift 568104
  have htrace : WordTrace (prefixWord ++ tailWord_568104) baseStart_568104 baseEnd_568104 := by
    simpa [prefixWord, tailWord_568104, baseEnd_568104] using wordTrace_append hprefix tailTrace_568104
  have hstable : (prefixWord ++ tailWord_568104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568104).length < 2 ^ (prefixWord ++ tailWord_568104).sum := by decide
  have hdescent : baseEnd_568104 < baseStart_568104 := by decide
  rcases family_descends (prefixWord ++ tailWord_568104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568162 : List Nat := [3, 3, 2, 1, 4, 1, 2, 4]
def baseStart_568162 : Nat := 118140960795 + 568162 * 2 ^ 59
def prefixEnd_568162 : Nat := 4983230072969 + 3 ^ 40 * 568162 * 2
def baseEnd_568162 : Nat := 86441539442936680670245

theorem tailTrace_568162 : CollatzResearch.WordTrace tailWord_568162 prefixEnd_568162 86441539442936680670245 := by
  unfold tailWord_568162
  simp only [CollatzResearch.WordTrace]
  refine ⟨5180642641913395797352685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13815047045102388792940493 5180642641913395797352685)
  ·
    refine ⟨1942740990717523424007257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5180642641913395797352685 1942740990717523424007257)
    ·
      refine ⟨1457055743038142568005443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1942740990717523424007257 1457055743038142568005443)
      ·
        refine ⟨2185583614557213852008165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1457055743038142568005443 2185583614557213852008165)
        ·
          refine ⟨409796927729477597251531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2185583614557213852008165 409796927729477597251531)
          ·
            refine ⟨614695391594216395877297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409796927729477597251531 614695391594216395877297)
            ·
              refine ⟨461021543695662296907973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 614695391594216395877297 461021543695662296907973)
              ·
                refine ⟨86441539442936680670245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 461021543695662296907973 86441539442936680670245)
                ·
                  rfl

theorem cell20_568162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_568162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568162 prefixEnd_568162 := by exact prefixLift 568162
  have htrace : WordTrace (prefixWord ++ tailWord_568162) baseStart_568162 baseEnd_568162 := by
    simpa [prefixWord, tailWord_568162, baseEnd_568162] using wordTrace_append hprefix tailTrace_568162
  have hstable : (prefixWord ++ tailWord_568162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568162).length < 2 ^ (prefixWord ++ tailWord_568162).sum := by decide
  have hdescent : baseEnd_568162 < baseStart_568162 := by decide
  rcases family_descends (prefixWord ++ tailWord_568162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568225 : List Nat := [1, 2, 3, 4, 1, 1, 2, 6]
def baseStart_568225 : Nat := 118140960795 + 568225 * 2 ^ 59
def prefixEnd_568225 : Nat := 4983230072969 + 3 ^ 40 * 568225 * 2
def baseEnd_568225 : Nat := 86451124415153940970159

theorem tailTrace_568225 : CollatzResearch.WordTrace tailWord_568225 prefixEnd_568225 86451124415153940970159 := by
  unfold tailWord_568225
  simp only [CollatzResearch.WordTrace]
  refine ⟨20724868366425344948954129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13816578910950229965969419 20724868366425344948954129)
  ·
    refine ⟨15543651274819008711715597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20724868366425344948954129 15543651274819008711715597)
    ·
      refine ⟨5828869228057128266893349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15543651274819008711715597 5828869228057128266893349)
      ·
        refine ⟨1092912980260711550042503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5828869228057128266893349 1092912980260711550042503)
        ·
          refine ⟨1639369470391067325063755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1092912980260711550042503 1639369470391067325063755)
          ·
            refine ⟨2459054205586600987595633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1639369470391067325063755 2459054205586600987595633)
            ·
              refine ⟨1844290654189950740696725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2459054205586600987595633 1844290654189950740696725)
              ·
                refine ⟨86451124415153940970159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1844290654189950740696725 86451124415153940970159)
                ·
                  rfl

theorem cell20_568225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 6].length) (baseStart_568225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568225 prefixEnd_568225 := by exact prefixLift 568225
  have htrace : WordTrace (prefixWord ++ tailWord_568225) baseStart_568225 baseEnd_568225 := by
    simpa [prefixWord, tailWord_568225, baseEnd_568225] using wordTrace_append hprefix tailTrace_568225
  have hstable : (prefixWord ++ tailWord_568225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568225).length < 2 ^ (prefixWord ++ tailWord_568225).sum := by decide
  have hdescent : baseEnd_568225 < baseStart_568225 := by decide
  rcases family_descends (prefixWord ++ tailWord_568225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568249 : List Nat := [1, 2, 1, 4, 2, 3, 2, 2, 3]
def baseStart_568249 : Nat := 118140960795 + 568249 * 2 ^ 59
def prefixEnd_568249 : Nat := 4983230072969 + 3 ^ 40 * 568249 * 2
def baseEnd_568249 : Nat := 259364327499424406110379

theorem tailTrace_568249 : CollatzResearch.WordTrace tailWord_568249 prefixEnd_568249 259364327499424406110379 := by
  unfold tailWord_568249
  simp only [CollatzResearch.WordTrace]
  refine ⟨20725743718338397047827801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13817162478892264698551867 20725743718338397047827801)
  ·
    refine ⟨15544307788753797785870851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20725743718338397047827801 15544307788753797785870851)
    ·
      refine ⟨23316461683130696678806277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15544307788753797785870851 23316461683130696678806277)
      ·
        refine ⟨4371836565587005627276177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23316461683130696678806277 4371836565587005627276177)
        ·
          refine ⟨3278877424190254220457133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4371836565587005627276177 3278877424190254220457133)
          ·
            refine ⟨1229579034071345332671425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3278877424190254220457133 1229579034071345332671425)
            ·
              refine ⟨922184275553508999503569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1229579034071345332671425 922184275553508999503569)
              ·
                refine ⟨691638206665131749627677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 922184275553508999503569 691638206665131749627677)
                ·
                  refine ⟨259364327499424406110379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691638206665131749627677 259364327499424406110379)
                  ·
                    rfl

theorem cell20_568249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_568249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568249 prefixEnd_568249 := by exact prefixLift 568249
  have htrace : WordTrace (prefixWord ++ tailWord_568249) baseStart_568249 baseEnd_568249 := by
    simpa [prefixWord, tailWord_568249, baseEnd_568249] using wordTrace_append hprefix tailTrace_568249
  have hstable : (prefixWord ++ tailWord_568249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568249).length < 2 ^ (prefixWord ++ tailWord_568249).sum := by decide
  have hdescent : baseEnd_568249 < baseStart_568249 := by decide
  rcases family_descends (prefixWord ++ tailWord_568249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568269 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 4]
def baseStart_568269 : Nat := 118140960795 + 568269 * 2 ^ 59
def prefixEnd_568269 : Nat := 4983230072969 + 3 ^ 40 * 568269 * 2
def baseEnd_568269 : Nat := 259373456044393225443631

theorem tailTrace_568269 : CollatzResearch.WordTrace tailWord_568269 prefixEnd_568269 259373456044393225443631 := by
  unfold tailWord_568269
  simp only [CollatzResearch.WordTrace]
  refine ⟨20726473178265940463555861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13817648785510626975703907 20726473178265940463555861)
  ·
    refine ⟨971553430231215959229181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20726473178265940463555861 971553430231215959229181)
    ·
      refine ⟨364332536336705984710943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 971553430231215959229181 364332536336705984710943)
      ·
        refine ⟨546498804505058977066415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364332536336705984710943 546498804505058977066415)
        ·
          refine ⟨819748206757588465599623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546498804505058977066415 819748206757588465599623)
          ·
            refine ⟨1229622310136382698399435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819748206757588465599623 1229622310136382698399435)
            ·
              refine ⟨1844433465204574047599153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229622310136382698399435 1844433465204574047599153)
              ·
                refine ⟨1383325098903430535699365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1844433465204574047599153 1383325098903430535699365)
                ·
                  refine ⟨259373456044393225443631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1383325098903430535699365 259373456044393225443631)
                  ·
                    rfl

theorem cell20_568269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_568269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568269 prefixEnd_568269 := by exact prefixLift 568269
  have htrace : WordTrace (prefixWord ++ tailWord_568269) baseStart_568269 baseEnd_568269 := by
    simpa [prefixWord, tailWord_568269, baseEnd_568269] using wordTrace_append hprefix tailTrace_568269
  have hstable : (prefixWord ++ tailWord_568269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568269).length < 2 ^ (prefixWord ++ tailWord_568269).sum := by decide
  have hdescent : baseEnd_568269 < baseStart_568269 := by decide
  rcases family_descends (prefixWord ++ tailWord_568269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568290 : List Nat := [3, 3, 3, 1, 1, 1, 1, 5, 2]
def baseStart_568290 : Nat := 118140960795 + 568290 * 2 ^ 59
def prefixEnd_568290 : Nat := 4983230072969 + 3 ^ 40 * 568290 * 2
def baseEnd_568290 : Nat := 259383041016610485743545

theorem tailTrace_568290 : CollatzResearch.WordTrace tailWord_568290 prefixEnd_568290 259383041016610485743545 := by
  unfold tailWord_568290
  simp only [CollatzResearch.WordTrace]
  refine ⟨5181809777797465262517581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13818159407459907366713549 5181809777797465262517581)
  ·
    refine ⟨1943178666674049473444093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5181809777797465262517581 1943178666674049473444093)
    ·
      refine ⟨728692000002768552541535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1943178666674049473444093 728692000002768552541535)
      ·
        refine ⟨1093038000004152828812303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 728692000002768552541535 1093038000004152828812303)
        ·
          refine ⟨1639557000006229243218455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1093038000004152828812303 1639557000006229243218455)
          ·
            refine ⟨2459335500009343864827683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1639557000006229243218455 2459335500009343864827683)
            ·
              refine ⟨3689003250014015797241525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2459335500009343864827683 3689003250014015797241525)
              ·
                refine ⟨345844054688813980991393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3689003250014015797241525 345844054688813980991393)
                ·
                  refine ⟨259383041016610485743545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345844054688813980991393 259383041016610485743545)
                  ·
                    rfl

theorem cell20_568290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_568290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568290 prefixEnd_568290 := by exact prefixLift 568290
  have htrace : WordTrace (prefixWord ++ tailWord_568290) baseStart_568290 baseEnd_568290 := by
    simpa [prefixWord, tailWord_568290, baseEnd_568290] using wordTrace_append hprefix tailTrace_568290
  have hstable : (prefixWord ++ tailWord_568290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568290).length < 2 ^ (prefixWord ++ tailWord_568290).sum := by decide
  have hdescent : baseEnd_568290 < baseStart_568290 := by decide
  rcases family_descends (prefixWord ++ tailWord_568290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568325 : List Nat := [1, 3, 1, 1, 2, 3, 5, 1, 3]
def baseStart_568325 : Nat := 118140960795 + 568325 * 2 ^ 59
def prefixEnd_568325 : Nat := 4983230072969 + 3 ^ 40 * 568325 * 2
def baseEnd_568325 : Nat := 259399015970305919576735

theorem tailTrace_568325 : CollatzResearch.WordTrace tailWord_568325 prefixEnd_568325 259399015970305919576735 := by
  unfold tailWord_568325
  simp only [CollatzResearch.WordTrace]
  refine ⟨20728515666063062027594429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13819010444042041351729619 20728515666063062027594429)
  ·
    refine ⟨7773193374773648260347911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20728515666063062027594429 7773193374773648260347911)
    ·
      refine ⟨11659790062160472390521867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7773193374773648260347911 11659790062160472390521867)
      ·
        refine ⟨17489685093240708585782801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11659790062160472390521867 17489685093240708585782801)
        ·
          refine ⟨13117263819930531439337101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17489685093240708585782801 13117263819930531439337101)
          ·
            refine ⟨4918973932473949289751413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13117263819930531439337101 4918973932473949289751413)
            ·
              refine ⟨461153806169432745914195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4918973932473949289751413 461153806169432745914195)
              ·
                refine ⟨691730709254149118871293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461153806169432745914195 691730709254149118871293)
                ·
                  refine ⟨259399015970305919576735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691730709254149118871293 259399015970305919576735)
                  ·
                    rfl

theorem cell20_568325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_568325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568325 prefixEnd_568325 := by exact prefixLift 568325
  have htrace : WordTrace (prefixWord ++ tailWord_568325) baseStart_568325 baseEnd_568325 := by
    simpa [prefixWord, tailWord_568325, baseEnd_568325] using wordTrace_append hprefix tailTrace_568325
  have hstable : (prefixWord ++ tailWord_568325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568325).length < 2 ^ (prefixWord ++ tailWord_568325).sum := by decide
  have hdescent : baseEnd_568325 < baseStart_568325 := by decide
  rcases family_descends (prefixWord ++ tailWord_568325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568366 : List Nat := [4, 1, 3, 1, 1, 1, 5, 2, 2]
def baseStart_568366 : Nat := 118140960795 + 568366 * 2 ^ 59
def prefixEnd_568366 : Nat := 4983230072969 + 3 ^ 40 * 568366 * 2
def baseEnd_568366 : Nat := 259417729487491999209901

theorem tailTrace_568366 : CollatzResearch.WordTrace tailWord_568366 prefixEnd_568366 259417729487491999209901 := by
  unfold tailWord_568366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2591251382364315753729619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13820007372609684019891301 2591251382364315753729619)
  ·
    refine ⟨3886877073546473630594429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2591251382364315753729619 3886877073546473630594429)
    ·
      refine ⟨1457578902579927611472911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3886877073546473630594429 1457578902579927611472911)
      ·
        refine ⟨2186368353869891417209367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1457578902579927611472911 2186368353869891417209367)
        ·
          refine ⟨3279552530804837125814051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2186368353869891417209367 3279552530804837125814051)
          ·
            refine ⟨4919328796207255688721077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3279552530804837125814051 4919328796207255688721077)
            ·
              refine ⟨461187074644430220817601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4919328796207255688721077 461187074644430220817601)
              ·
                refine ⟨345890305983322665613201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 461187074644430220817601 345890305983322665613201)
                ·
                  refine ⟨259417729487491999209901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345890305983322665613201 259417729487491999209901)
                  ·
                    rfl

theorem cell20_568366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_568366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568366 prefixEnd_568366 := by exact prefixLift 568366
  have htrace : WordTrace (prefixWord ++ tailWord_568366) baseStart_568366 baseEnd_568366 := by
    simpa [prefixWord, tailWord_568366, baseEnd_568366] using wordTrace_append hprefix tailTrace_568366
  have hstable : (prefixWord ++ tailWord_568366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568366).length < 2 ^ (prefixWord ++ tailWord_568366).sum := by decide
  have hdescent : baseEnd_568366 < baseStart_568366 := by decide
  rcases family_descends (prefixWord ++ tailWord_568366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568377 : List Nat := [1, 2, 1, 5, 2, 2, 2, 5]
def baseStart_568377 : Nat := 118140960795 + 568377 * 2 ^ 59
def prefixEnd_568377 : Nat := 4983230072969 + 3 ^ 40 * 568377 * 2
def baseEnd_568377 : Nat := 86474250062408283281063

theorem tailTrace_568377 : CollatzResearch.WordTrace tailWord_568377 prefixEnd_568377 86474250062408283281063 := by
  unfold tailWord_568377
  simp only [CollatzResearch.WordTrace]
  refine ⟨20730412261874674908487385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13820274841249783272324923 20730412261874674908487385)
  ·
    refine ⟨15547809196406006181365539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20730412261874674908487385 15547809196406006181365539)
    ·
      refine ⟨23321713794609009272048309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15547809196406006181365539 23321713794609009272048309)
      ·
        refine ⟨2186410668244594619254529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23321713794609009272048309 2186410668244594619254529)
        ·
          refine ⟨1639808001183445964440897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2186410668244594619254529 1639808001183445964440897)
          ·
            refine ⟨1229856000887584473330673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1639808001183445964440897 1229856000887584473330673)
            ·
              refine ⟨922392000665688354998005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1229856000887584473330673 922392000665688354998005)
              ·
                refine ⟨86474250062408283281063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 922392000665688354998005 86474250062408283281063)
                ·
                  rfl

theorem cell20_568377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 5].length) (baseStart_568377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568377 prefixEnd_568377 := by exact prefixLift 568377
  have htrace : WordTrace (prefixWord ++ tailWord_568377) baseStart_568377 baseEnd_568377 := by
    simpa [prefixWord, tailWord_568377, baseEnd_568377] using wordTrace_append hprefix tailTrace_568377
  have hstable : (prefixWord ++ tailWord_568377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568377).length < 2 ^ (prefixWord ++ tailWord_568377).sum := by decide
  have hdescent : baseEnd_568377 < baseStart_568377 := by decide
  rcases family_descends (prefixWord ++ tailWord_568377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568380 : List Nat := [2, 2, 2, 2, 2, 4, 2, 1, 3]
def baseStart_568380 : Nat := 118140960795 + 568380 * 2 ^ 59
def prefixEnd_568380 : Nat := 4983230072969 + 3 ^ 40 * 568380 * 2
def baseEnd_568380 : Nat := 259424119468970172743177

theorem tailTrace_568380 : CollatzResearch.WordTrace tailWord_568380 prefixEnd_568380 259424119468970172743177 := by
  unfold tailWord_568380
  simp only [CollatzResearch.WordTrace]
  refine ⟨10365260840431903210423297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13820347787242537613897729 10365260840431903210423297)
  ·
    refine ⟨7773945630323927407817473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10365260840431903210423297 7773945630323927407817473)
    ·
      refine ⟨5830459222742945555863105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7773945630323927407817473 5830459222742945555863105)
      ·
        refine ⟨4372844417057209166897329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5830459222742945555863105 4372844417057209166897329)
        ·
          refine ⟨3279633312792906875172997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4372844417057209166897329 3279633312792906875172997)
          ·
            refine ⟨614931246148670039094937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3279633312792906875172997 614931246148670039094937)
            ·
              refine ⟨461198434611502529321203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 614931246148670039094937 461198434611502529321203)
              ·
                refine ⟨691797651917253793981805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461198434611502529321203 691797651917253793981805)
                ·
                  refine ⟨259424119468970172743177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691797651917253793981805 259424119468970172743177)
                  ·
                    rfl

theorem cell20_568380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_568380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568380 prefixEnd_568380 := by exact prefixLift 568380
  have htrace : WordTrace (prefixWord ++ tailWord_568380) baseStart_568380 baseEnd_568380 := by
    simpa [prefixWord, tailWord_568380, baseEnd_568380] using wordTrace_append hprefix tailTrace_568380
  have hstable : (prefixWord ++ tailWord_568380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568380).length < 2 ^ (prefixWord ++ tailWord_568380).sum := by decide
  have hdescent : baseEnd_568380 < baseStart_568380 := by decide
  rcases family_descends (prefixWord ++ tailWord_568380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568384 : List Nat := [2, 1, 1, 2, 2, 3, 3, 3, 3]
def baseStart_568384 : Nat := 118140960795 + 568384 * 2 ^ 59
def prefixEnd_568384 : Nat := 4983230072969 + 3 ^ 40 * 568384 * 2
def baseEnd_568384 : Nat := 259425945177963936609827

theorem tailTrace_568384 : CollatzResearch.WordTrace tailWord_568384 prefixEnd_568384 259425945177963936609827 := by
  unfold tailWord_568384
  simp only [CollatzResearch.WordTrace]
  refine ⟨10365333786424657551996103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13820445048566210069328137 10365333786424657551996103)
  ·
    refine ⟨15548000679636986327994155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10365333786424657551996103 15548000679636986327994155)
    ·
      refine ⟨23322001019455479491991233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15548000679636986327994155 23322001019455479491991233)
      ·
        refine ⟨17491500764591609618993425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23322001019455479491991233 17491500764591609618993425)
        ·
          refine ⟨13118625573443707214245069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17491500764591609618993425 13118625573443707214245069)
          ·
            refine ⟨4919484590041390205341901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13118625573443707214245069 4919484590041390205341901)
            ·
              refine ⟨1844806721265521327003213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4919484590041390205341901 1844806721265521327003213)
              ·
                refine ⟨691802520474570497626205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1844806721265521327003213 691802520474570497626205)
                ·
                  refine ⟨259425945177963936609827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691802520474570497626205 259425945177963936609827)
                  ·
                    rfl

theorem cell20_568384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_568384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568384 prefixEnd_568384 := by exact prefixLift 568384
  have htrace : WordTrace (prefixWord ++ tailWord_568384) baseStart_568384 baseEnd_568384 := by
    simpa [prefixWord, tailWord_568384, baseEnd_568384] using wordTrace_append hprefix tailTrace_568384
  have hstable : (prefixWord ++ tailWord_568384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568384).length < 2 ^ (prefixWord ++ tailWord_568384).sum := by decide
  have hdescent : baseEnd_568384 < baseStart_568384 := by decide
  rcases family_descends (prefixWord ++ tailWord_568384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568398 : List Nat := [4, 1, 1, 1, 1, 3, 1, 8]
def baseStart_568398 : Nat := 118140960795 + 568398 * 2 ^ 59
def prefixEnd_568398 : Nat := 4983230072969 + 3 ^ 40 * 568398 * 2
def baseEnd_568398 : Nat := 86477445053147370047701

theorem tailTrace_568398 : CollatzResearch.WordTrace tailWord_568398 prefixEnd_568398 86477445053147370047701 := by
  unfold tailWord_568398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2591397274349824436875231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13820785463199063663334565 2591397274349824436875231)
  ·
    refine ⟨3887095911524736655312847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2591397274349824436875231 3887095911524736655312847)
    ·
      refine ⟨5830643867287104982969271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3887095911524736655312847 5830643867287104982969271)
      ·
        refine ⟨8745965800930657474453907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5830643867287104982969271 8745965800930657474453907)
        ·
          refine ⟨13118948701395986211680861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8745965800930657474453907 13118948701395986211680861)
          ·
            refine ⟨4919605763023494829380323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13118948701395986211680861 4919605763023494829380323)
            ·
              refine ⟨7379408644535242244070485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4919605763023494829380323 7379408644535242244070485)
              ·
                refine ⟨86477445053147370047701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7379408644535242244070485 86477445053147370047701)
                ·
                  rfl

theorem cell20_568398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_568398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568398 prefixEnd_568398 := by exact prefixLift 568398
  have htrace : WordTrace (prefixWord ++ tailWord_568398) baseStart_568398 baseEnd_568398 := by
    simpa [prefixWord, tailWord_568398, baseEnd_568398] using wordTrace_append hprefix tailTrace_568398
  have hstable : (prefixWord ++ tailWord_568398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568398).length < 2 ^ (prefixWord ++ tailWord_568398).sum := by decide
  have hdescent : baseEnd_568398 < baseStart_568398 := by decide
  rcases family_descends (prefixWord ++ tailWord_568398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568408 : List Nat := [2, 1, 2, 2, 1, 3, 2, 5, 2]
def baseStart_568408 : Nat := 118140960795 + 568408 * 2 ^ 59
def prefixEnd_568408 : Nat := 4983230072969 + 3 ^ 40 * 568408 * 2
def baseEnd_568408 : Nat := 259436899431926519809729

theorem tailTrace_568408 : CollatzResearch.WordTrace tailWord_568408 prefixEnd_568408 259436899431926519809729 := by
  unfold tailWord_568408
  simp only [CollatzResearch.WordTrace]
  refine ⟨10365771462381183601432939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13821028616508244801910585 10365771462381183601432939)
  ·
    refine ⟨15548657193571775402149409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10365771462381183601432939 15548657193571775402149409)
    ·
      refine ⟨11661492895178831551612057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15548657193571775402149409 11661492895178831551612057)
      ·
        refine ⟨8746119671384123663709043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11661492895178831551612057 8746119671384123663709043)
        ·
          refine ⟨13119179507076185495563565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8746119671384123663709043 13119179507076185495563565)
          ·
            refine ⟨4919692315153569560836337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13119179507076185495563565 4919692315153569560836337)
            ·
              refine ⟨3689769236365177170627253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4919692315153569560836337 3689769236365177170627253)
              ·
                refine ⟨345915865909235359746305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3689769236365177170627253 345915865909235359746305)
                ·
                  refine ⟨259436899431926519809729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345915865909235359746305 259436899431926519809729)
                  ·
                    rfl

theorem cell20_568408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 2].length) (baseStart_568408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568408 prefixEnd_568408 := by exact prefixLift 568408
  have htrace : WordTrace (prefixWord ++ tailWord_568408) baseStart_568408 baseEnd_568408 := by
    simpa [prefixWord, tailWord_568408, baseEnd_568408] using wordTrace_append hprefix tailTrace_568408
  have hstable : (prefixWord ++ tailWord_568408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568408).length < 2 ^ (prefixWord ++ tailWord_568408).sum := by decide
  have hdescent : baseEnd_568408 < baseStart_568408 := by decide
  rcases family_descends (prefixWord ++ tailWord_568408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568418 : List Nat := [3, 3, 2, 2, 1, 2, 2, 2, 3]
def baseStart_568418 : Nat := 118140960795 + 568418 * 2 ^ 59
def prefixEnd_568418 : Nat := 4983230072969 + 3 ^ 40 * 568418 * 2
def baseEnd_568418 : Nat := 259441463704410929476355

theorem tailTrace_568418 : CollatzResearch.WordTrace tailWord_568418 prefixEnd_568418 259441463704410929476355 := by
  unfold tailWord_568418
  simp only [CollatzResearch.WordTrace]
  refine ⟨5182976913681534727682477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13821271769817425940486605 5182976913681534727682477)
  ·
    refine ⟨1943616342630575522880929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5182976913681534727682477 1943616342630575522880929)
    ·
      refine ⟨1457712256972931642160697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1943616342630575522880929 1457712256972931642160697)
      ·
        refine ⟨1093284192729698731620523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1457712256972931642160697 1093284192729698731620523)
        ·
          refine ⟨1639926289094548097430785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1093284192729698731620523 1639926289094548097430785)
          ·
            refine ⟨1229944716820911073073089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1639926289094548097430785 1229944716820911073073089)
            ·
              refine ⟨922458537615683304804817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1229944716820911073073089 922458537615683304804817)
              ·
                refine ⟨691843903211762478603613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 922458537615683304804817 691843903211762478603613)
                ·
                  refine ⟨259441463704410929476355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691843903211762478603613 259441463704410929476355)
                  ·
                    rfl

theorem cell20_568418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_568418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568418 prefixEnd_568418 := by exact prefixLift 568418
  have htrace : WordTrace (prefixWord ++ tailWord_568418) baseStart_568418 baseEnd_568418 := by
    simpa [prefixWord, tailWord_568418, baseEnd_568418] using wordTrace_append hprefix tailTrace_568418
  have hstable : (prefixWord ++ tailWord_568418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568418).length < 2 ^ (prefixWord ++ tailWord_568418).sum := by decide
  have hdescent : baseEnd_568418 < baseStart_568418 := by decide
  rcases family_descends (prefixWord ++ tailWord_568418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568425 : List Nat := [1, 2, 1, 1, 1, 6, 4, 2, 2]
def baseStart_568425 : Nat := 118140960795 + 568425 * 2 ^ 59
def prefixEnd_568425 : Nat := 4983230072969 + 3 ^ 40 * 568425 * 2
def baseEnd_568425 : Nat := 259444658695150016242993

theorem tailTrace_568425 : CollatzResearch.WordTrace tailWord_568425 prefixEnd_568425 259444658695150016242993 := by
  unfold tailWord_568425
  simp only [CollatzResearch.WordTrace]
  refine ⟨20732162965700779106234729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13821441977133852737489819 20732162965700779106234729)
  ·
    refine ⟨15549122224275584329676047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20732162965700779106234729 15549122224275584329676047)
    ·
      refine ⟨23323683336413376494514071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15549122224275584329676047 23323683336413376494514071)
      ·
        refine ⟨34985525004620064741771107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23323683336413376494514071 34985525004620064741771107)
        ·
          refine ⟨52478287506930097112656661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34985525004620064741771107 52478287506930097112656661)
          ·
            refine ⟨2459919726887348302155781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52478287506930097112656661 2459919726887348302155781)
            ·
              refine ⟨461234948791377806654209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2459919726887348302155781 461234948791377806654209)
              ·
                refine ⟨345926211593533354990657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 461234948791377806654209 345926211593533354990657)
                ·
                  refine ⟨259444658695150016242993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345926211593533354990657 259444658695150016242993)
                  ·
                    rfl

theorem cell20_568425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 2].length) (baseStart_568425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568425 prefixEnd_568425 := by exact prefixLift 568425
  have htrace : WordTrace (prefixWord ++ tailWord_568425) baseStart_568425 baseEnd_568425 := by
    simpa [prefixWord, tailWord_568425, baseEnd_568425] using wordTrace_append hprefix tailTrace_568425
  have hstable : (prefixWord ++ tailWord_568425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568425).length < 2 ^ (prefixWord ++ tailWord_568425).sum := by decide
  have hdescent : baseEnd_568425 < baseStart_568425 := by decide
  rcases family_descends (prefixWord ++ tailWord_568425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568484 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 4]
def baseStart_568484 : Nat := 118140960795 + 568484 * 2 ^ 59
def prefixEnd_568484 : Nat := 4983230072969 + 3 ^ 40 * 568484 * 2
def baseEnd_568484 : Nat := 259471587902808033276085

theorem tailTrace_568484 : CollatzResearch.WordTrace tailWord_568484 prefixEnd_568484 259471587902808033276085 := by
  unfold tailWord_568484
  simp only [CollatzResearch.WordTrace]
  refine ⟨10367157436243516091316253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13822876581658021455088337 10367157436243516091316253)
  ·
    refine ⟨3887684038591318534243595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10367157436243516091316253 3887684038591318534243595)
    ·
      refine ⟨5831526057886977801365393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3887684038591318534243595 5831526057886977801365393)
      ·
        refine ⟨4373644543415233351024045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5831526057886977801365393 4373644543415233351024045)
        ·
          refine ⟨1640116703780712506634017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4373644543415233351024045 1640116703780712506634017)
          ·
            refine ⟨1230087527835534379975513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1640116703780712506634017 1230087527835534379975513)
            ·
              refine ⟨922565645876650784981635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1230087527835534379975513 922565645876650784981635)
              ·
                refine ⟨1383848468814976177472453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922565645876650784981635 1383848468814976177472453)
                ·
                  refine ⟨259471587902808033276085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1383848468814976177472453 259471587902808033276085)
                  ·
                    rfl

theorem cell20_568484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_568484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568484 prefixEnd_568484 := by exact prefixLift 568484
  have htrace : WordTrace (prefixWord ++ tailWord_568484) baseStart_568484 baseEnd_568484 := by
    simpa [prefixWord, tailWord_568484, baseEnd_568484] using wordTrace_append hprefix tailTrace_568484
  have hstable : (prefixWord ++ tailWord_568484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568484).length < 2 ^ (prefixWord ++ tailWord_568484).sum := by decide
  have hdescent : baseEnd_568484 < baseStart_568484 := by decide
  rcases family_descends (prefixWord ++ tailWord_568484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568505 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 4]
def baseStart_568505 : Nat := 118140960795 + 568505 * 2 ^ 59
def prefixEnd_568505 : Nat := 4983230072969 + 3 ^ 40 * 568505 * 2
def baseEnd_568505 : Nat := 259481172875025293575999

theorem tailTrace_568505 : CollatzResearch.WordTrace tailWord_568505 prefixEnd_568505 259481172875025293575999 := by
  unfold tailWord_568505
  simp only [CollatzResearch.WordTrace]
  refine ⟨20735080805410952769146969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13823387203607301846097979 20735080805410952769146969)
  ·
    refine ⟨15551310604058214576860227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20735080805410952769146969 15551310604058214576860227)
    ·
      refine ⟨23326965906087321865290341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15551310604058214576860227 23326965906087321865290341)
      ·
        refine ⟨4373806107391372849741939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23326965906087321865290341 4373806107391372849741939)
        ·
          refine ⟨6560709161087059274612909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4373806107391372849741939 6560709161087059274612909)
          ·
            refine ⟨2460265935407647227979841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6560709161087059274612909 2460265935407647227979841)
            ·
              refine ⟨1845199451555735420984881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2460265935407647227979841 1845199451555735420984881)
              ·
                refine ⟨1383899588666801565738661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1845199451555735420984881 1383899588666801565738661)
                ·
                  refine ⟨259481172875025293575999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1383899588666801565738661 259481172875025293575999)
                  ·
                    rfl

theorem cell20_568505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_568505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568505 prefixEnd_568505 := by exact prefixLift 568505
  have htrace : WordTrace (prefixWord ++ tailWord_568505) baseStart_568505 baseEnd_568505 := by
    simpa [prefixWord, tailWord_568505, baseEnd_568505] using wordTrace_append hprefix tailTrace_568505
  have hstable : (prefixWord ++ tailWord_568505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568505).length < 2 ^ (prefixWord ++ tailWord_568505).sum := by decide
  have hdescent : baseEnd_568505 < baseStart_568505 := by decide
  rcases family_descends (prefixWord ++ tailWord_568505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568508 : List Nat := [2, 2, 2, 3, 2, 3, 2, 4]
def baseStart_568508 : Nat := 118140960795 + 568508 * 2 ^ 59
def prefixEnd_568508 : Nat := 4983230072969 + 3 ^ 40 * 568508 * 2
def baseEnd_568508 : Nat := 86494180718923538825329

theorem tailTrace_568508 : CollatzResearch.WordTrace tailWord_568508 prefixEnd_568508 86494180718923538825329 := by
  unfold tailWord_568508
  simp only [CollatzResearch.WordTrace]
  refine ⟨10367595112200042140753089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13823460149600056187670785 10367595112200042140753089)
  ·
    refine ⟨7775696334150031605564817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10367595112200042140753089 7775696334150031605564817)
    ·
      refine ⟨5831772250612523704173613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7775696334150031605564817 5831772250612523704173613)
      ·
        refine ⟨2186914593979696389065105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5831772250612523704173613 2186914593979696389065105)
        ·
          refine ⟨1640185945484772291798829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2186914593979696389065105 1640185945484772291798829)
          ·
            refine ⟨615069729556789609424561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1640185945484772291798829 615069729556789609424561)
            ·
              refine ⟨461302297167592207068421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615069729556789609424561 461302297167592207068421)
              ·
                refine ⟨86494180718923538825329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 461302297167592207068421 86494180718923538825329)
                ·
                  rfl

theorem cell20_568508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_568508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568508 prefixEnd_568508 := by exact prefixLift 568508
  have htrace : WordTrace (prefixWord ++ tailWord_568508) baseStart_568508 baseEnd_568508 := by
    simpa [prefixWord, tailWord_568508, baseEnd_568508] using wordTrace_append hprefix tailTrace_568508
  have hstable : (prefixWord ++ tailWord_568508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568508).length < 2 ^ (prefixWord ++ tailWord_568508).sum := by decide
  have hdescent : baseEnd_568508 < baseStart_568508 := by decide
  rcases family_descends (prefixWord ++ tailWord_568508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568514 : List Nat := [3, 5, 1, 1, 2, 2, 1, 3, 2]
def baseStart_568514 : Nat := 118140960795 + 568514 * 2 ^ 59
def prefixEnd_568514 : Nat := 4983230072969 + 3 ^ 40 * 568514 * 2
def baseEnd_568514 : Nat := 259485280720261262275963

theorem tailTrace_568514 : CollatzResearch.WordTrace tailWord_568514 prefixEnd_568514 259485280720261262275963 := by
  unfold tailWord_568514
  simp only [CollatzResearch.WordTrace]
  refine ⟨5183852265594586826556149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13823606041585564870816397 5183852265594586826556149)
  ·
    refine ⟨485986149899492514989639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5183852265594586826556149 485986149899492514989639)
    ·
      refine ⟨728979224849238772484459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 485986149899492514989639 728979224849238772484459)
      ·
        refine ⟨1093468837273858158726689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 728979224849238772484459 1093468837273858158726689)
        ·
          refine ⟨820101627955393619045017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1093468837273858158726689 820101627955393619045017)
          ·
            refine ⟨615076220966545214283763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 820101627955393619045017 615076220966545214283763)
            ·
              refine ⟨922614331449817821425645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615076220966545214283763 922614331449817821425645)
              ·
                refine ⟨345980374293681683034617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 922614331449817821425645 345980374293681683034617)
                ·
                  refine ⟨259485280720261262275963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345980374293681683034617 259485280720261262275963)
                  ·
                    rfl

theorem cell20_568514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_568514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568514 prefixEnd_568514 := by exact prefixLift 568514
  have htrace : WordTrace (prefixWord ++ tailWord_568514) baseStart_568514 baseEnd_568514 := by
    simpa [prefixWord, tailWord_568514, baseEnd_568514] using wordTrace_append hprefix tailTrace_568514
  have hstable : (prefixWord ++ tailWord_568514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568514).length < 2 ^ (prefixWord ++ tailWord_568514).sum := by decide
  have hdescent : baseEnd_568514 < baseStart_568514 := by decide
  rcases family_descends (prefixWord ++ tailWord_568514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568525 : List Nat := [1, 6, 2, 2, 1, 2, 6]
def baseStart_568525 : Nat := 118140960795 + 568525 * 2 ^ 59
def prefixEnd_568525 : Nat := 4983230072969 + 3 ^ 40 * 568525 * 2
def baseEnd_568525 : Nat := 28832255713332679212139

theorem tailTrace_568525 : CollatzResearch.WordTrace tailWord_568525 prefixEnd_568525 28832255713332679212139 := by
  unfold tailWord_568525
  simp only [CollatzResearch.WordTrace]
  refine ⟨20735810265338496184875029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13823873510225664123250019 20735810265338496184875029)
  ·
    refine ⟨971991106187742008666017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20735810265338496184875029 971991106187742008666017)
    ·
      refine ⟨728993329640806506499513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 971991106187742008666017 728993329640806506499513)
      ·
        refine ⟨546744997230604879874635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 728993329640806506499513 546744997230604879874635)
        ·
          refine ⟨820117495845907319811953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546744997230604879874635 820117495845907319811953)
          ·
            refine ⟨615088121884430489858965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 820117495845907319811953 615088121884430489858965)
            ·
              refine ⟨28832255713332679212139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 615088121884430489858965 28832255713332679212139)
              ·
                rfl

theorem cell20_568525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 6].length) (baseStart_568525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568525 prefixEnd_568525 := by exact prefixLift 568525
  have htrace : WordTrace (prefixWord ++ tailWord_568525) baseStart_568525 baseEnd_568525 := by
    simpa [prefixWord, tailWord_568525, baseEnd_568525] using wordTrace_append hprefix tailTrace_568525
  have hstable : (prefixWord ++ tailWord_568525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568525).length < 2 ^ (prefixWord ++ tailWord_568525).sum := by decide
  have hdescent : baseEnd_568525 < baseStart_568525 := by decide
  rcases family_descends (prefixWord ++ tailWord_568525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568543 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 4]
def baseStart_568543 : Nat := 118140960795 + 568543 * 2 ^ 59
def prefixEnd_568543 : Nat := 4983230072969 + 3 ^ 40 * 568543 * 2
def baseEnd_568543 : Nat := 259498517110466050309177

theorem tailTrace_568543 : CollatzResearch.WordTrace tailWord_568543 prefixEnd_568543 259498517110466050309177 := by
  unfold tailWord_568543
  simp only [CollatzResearch.WordTrace]
  refine ⟨20736466779273285259030283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13824311186182190172686855 20736466779273285259030283)
  ·
    refine ⟨31104700168909927888545425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20736466779273285259030283 31104700168909927888545425)
    ·
      refine ⟨23328525126682445916409069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31104700168909927888545425 23328525126682445916409069)
      ·
        refine ⟨8748196922505917218653401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23328525126682445916409069 8748196922505917218653401)
        ·
          refine ⟨6561147691879437913990051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8748196922505917218653401 6561147691879437913990051)
          ·
            refine ⟨9841721537819156870985077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6561147691879437913990051 9841721537819156870985077)
            ·
              refine ⟨922661394170545956654851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9841721537819156870985077 922661394170545956654851)
              ·
                refine ⟨1383992091255818934982277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922661394170545956654851 1383992091255818934982277)
                ·
                  refine ⟨259498517110466050309177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1383992091255818934982277 259498517110466050309177)
                  ·
                    rfl

theorem cell20_568543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 4].length) (baseStart_568543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568543 prefixEnd_568543 := by exact prefixLift 568543
  have htrace : WordTrace (prefixWord ++ tailWord_568543) baseStart_568543 baseEnd_568543 := by
    simpa [prefixWord, tailWord_568543, baseEnd_568543] using wordTrace_append hprefix tailTrace_568543
  have hstable : (prefixWord ++ tailWord_568543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568543).length < 2 ^ (prefixWord ++ tailWord_568543).sum := by decide
  have hdescent : baseEnd_568543 < baseStart_568543 := by decide
  rcases family_descends (prefixWord ++ tailWord_568543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568549 : List Nat := [1, 3, 1, 4, 4, 1, 2, 1, 3]
def baseStart_568549 : Nat := 118140960795 + 568549 * 2 ^ 59
def prefixEnd_568549 : Nat := 4983230072969 + 3 ^ 40 * 568549 * 2
def baseEnd_568549 : Nat := 259501255673956696109153

theorem tailTrace_568549 : CollatzResearch.WordTrace tailWord_568549 prefixEnd_568549 259501255673956696109153 := by
  unfold tailWord_568549
  simp only [CollatzResearch.WordTrace]
  refine ⟨20736685617251548283748701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13824457078167698855832467 20736685617251548283748701)
  ·
    refine ⟨7776257106469330606405763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20736685617251548283748701 7776257106469330606405763)
    ·
      refine ⟨11664385659703995909608645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7776257106469330606405763 11664385659703995909608645)
      ·
        refine ⟨2187072311194499233051621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11664385659703995909608645 2187072311194499233051621)
        ·
          refine ⟨410076058348968606197179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2187072311194499233051621 410076058348968606197179)
          ·
            refine ⟨615114087523452909295769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410076058348968606197179 615114087523452909295769)
            ·
              refine ⟨461335565642589681971827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615114087523452909295769 461335565642589681971827)
              ·
                refine ⟨692003348463884522957741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461335565642589681971827 692003348463884522957741)
                ·
                  refine ⟨259501255673956696109153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692003348463884522957741 259501255673956696109153)
                  ·
                    rfl

theorem cell20_568549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_568549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568549 prefixEnd_568549 := by exact prefixLift 568549
  have htrace : WordTrace (prefixWord ++ tailWord_568549) baseStart_568549 baseEnd_568549 := by
    simpa [prefixWord, tailWord_568549, baseEnd_568549] using wordTrace_append hprefix tailTrace_568549
  have hstable : (prefixWord ++ tailWord_568549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568549).length < 2 ^ (prefixWord ++ tailWord_568549).sum := by decide
  have hdescent : baseEnd_568549 < baseStart_568549 := by decide
  rcases family_descends (prefixWord ++ tailWord_568549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568605 : List Nat := [1, 4, 2, 3, 1, 1, 3, 5]
def baseStart_568605 : Nat := 118140960795 + 568605 * 2 ^ 59
def prefixEnd_568605 : Nat := 4983230072969 + 3 ^ 40 * 568605 * 2
def baseEnd_568605 : Nat := 86508938533289796747419

theorem tailTrace_568605 : CollatzResearch.WordTrace tailWord_568605 prefixEnd_568605 86508938533289796747419 := by
  unfold tailWord_568605
  simp only [CollatzResearch.WordTrace]
  refine ⟨20738728105048669847787269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13825818736699113231858179 20738728105048669847787269)
  ·
    refine ⟨3888511519696625596460113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20738728105048669847787269 3888511519696625596460113)
    ·
      refine ⟨2916383639772469197345085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3888511519696625596460113 2916383639772469197345085)
      ·
        refine ⟨1093643864914675949004407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2916383639772469197345085 1093643864914675949004407)
        ·
          refine ⟨1640465797372013923506611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1093643864914675949004407 1640465797372013923506611)
          ·
            refine ⟨2460698696058020885259917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1640465797372013923506611 2460698696058020885259917)
            ·
              refine ⟨922762011021757831972469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2460698696058020885259917 922762011021757831972469)
              ·
                refine ⟨86508938533289796747419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 922762011021757831972469 86508938533289796747419)
                ·
                  rfl

theorem cell20_568605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 5].length) (baseStart_568605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568605 prefixEnd_568605 := by exact prefixLift 568605
  have htrace : WordTrace (prefixWord ++ tailWord_568605) baseStart_568605 baseEnd_568605 := by
    simpa [prefixWord, tailWord_568605, baseEnd_568605] using wordTrace_append hprefix tailTrace_568605
  have hstable : (prefixWord ++ tailWord_568605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568605).length < 2 ^ (prefixWord ++ tailWord_568605).sum := by decide
  have hdescent : baseEnd_568605 < baseStart_568605 := by decide
  rcases family_descends (prefixWord ++ tailWord_568605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568612 : List Nat := [2, 3, 1, 3, 1, 1, 1, 5, 3]
def baseStart_568612 : Nat := 118140960795 + 568612 * 2 ^ 59
def prefixEnd_568612 : Nat := 4983230072969 + 3 ^ 40 * 568612 * 2
def baseEnd_568612 : Nat := 259530010590608477008895

theorem tailTrace_568612 : CollatzResearch.WordTrace tailWord_568612 prefixEnd_568612 259530010590608477008895 := by
  unfold tailWord_568612
  simp only [CollatzResearch.WordTrace]
  refine ⟨10369491708011655021646045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13825988944015540028861393 10369491708011655021646045)
  ·
    refine ⟨3888559390504370633117267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10369491708011655021646045 3888559390504370633117267)
    ·
      refine ⟨5832839085756555949675901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3888559390504370633117267 5832839085756555949675901)
      ·
        refine ⟨2187314657158708481128463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5832839085756555949675901 2187314657158708481128463)
        ·
          refine ⟨3280971985738062721692695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2187314657158708481128463 3280971985738062721692695)
          ·
            refine ⟨4921457978607094082539043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3280971985738062721692695 4921457978607094082539043)
            ·
              refine ⟨7382186967910641123808565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4921457978607094082539043 7382186967910641123808565)
              ·
                refine ⟨692080028241622605357053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7382186967910641123808565 692080028241622605357053)
                ·
                  refine ⟨259530010590608477008895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692080028241622605357053 259530010590608477008895)
                  ·
                    rfl

theorem cell20_568612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_568612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568612 prefixEnd_568612 := by exact prefixLift 568612
  have htrace : WordTrace (prefixWord ++ tailWord_568612) baseStart_568612 baseEnd_568612 := by
    simpa [prefixWord, tailWord_568612, baseEnd_568612] using wordTrace_append hprefix tailTrace_568612
  have hstable : (prefixWord ++ tailWord_568612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568612).length < 2 ^ (prefixWord ++ tailWord_568612).sum := by decide
  have hdescent : baseEnd_568612 < baseStart_568612 := by decide
  rcases family_descends (prefixWord ++ tailWord_568612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568636 : List Nat := [2, 2, 2, 2, 1, 3, 1, 5, 2]
def baseStart_568636 : Nat := 118140960795 + 568636 * 2 ^ 59
def prefixEnd_568636 : Nat := 4983230072969 + 3 ^ 40 * 568636 * 2
def baseEnd_568636 : Nat := 259540964844571060208797

theorem tailTrace_568636 : CollatzResearch.WordTrace tailWord_568636 prefixEnd_568636 259540964844571060208797 := by
  unfold tailWord_568636
  simp only [CollatzResearch.WordTrace]
  refine ⟨10369929383968181071082881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13826572511957574761443841 10369929383968181071082881)
  ·
    refine ⟨7777447037976135803312161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10369929383968181071082881 7777447037976135803312161)
    ·
      refine ⟨5833085278482101852484121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7777447037976135803312161 5833085278482101852484121)
      ·
        refine ⟨4374813958861576389363091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5833085278482101852484121 4374813958861576389363091)
        ·
          refine ⟨6562220938292364584044637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4374813958861576389363091 6562220938292364584044637)
          ·
            refine ⟨2460832851859636719016739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6562220938292364584044637 2460832851859636719016739)
            ·
              refine ⟨3691249277789455078525109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2460832851859636719016739 3691249277789455078525109)
              ·
                refine ⟨346054619792761413611729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3691249277789455078525109 346054619792761413611729)
                ·
                  refine ⟨259540964844571060208797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346054619792761413611729 259540964844571060208797)
                  ·
                    rfl

theorem cell20_568636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_568636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568636 prefixEnd_568636 := by exact prefixLift 568636
  have htrace : WordTrace (prefixWord ++ tailWord_568636) baseStart_568636 baseEnd_568636 := by
    simpa [prefixWord, tailWord_568636, baseEnd_568636] using wordTrace_append hprefix tailTrace_568636
  have hstable : (prefixWord ++ tailWord_568636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568636).length < 2 ^ (prefixWord ++ tailWord_568636).sum := by decide
  have hdescent : baseEnd_568636 < baseStart_568636 := by decide
  rcases family_descends (prefixWord ++ tailWord_568636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568640 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 6]
def baseStart_568640 : Nat := 118140960795 + 568640 * 2 ^ 59
def prefixEnd_568640 : Nat := 4983230072969 + 3 ^ 40 * 568640 * 2
def baseEnd_568640 : Nat := 259542790553564824075447

theorem tailTrace_568640 : CollatzResearch.WordTrace tailWord_568640 prefixEnd_568640 259542790553564824075447 := by
  unfold tailWord_568640
  simp only [CollatzResearch.WordTrace]
  refine ⟨10370002329960935412655687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13826669773281247216874249 10370002329960935412655687)
  ·
    refine ⟨15555003494941403118983531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10370002329960935412655687 15555003494941403118983531)
    ·
      refine ⟨23332505242412104678475297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15555003494941403118983531 23332505242412104678475297)
      ·
        refine ⟨17499378931809078508856473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23332505242412104678475297 17499378931809078508856473)
        ·
          refine ⟨13124534198856808881642355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17499378931809078508856473 13124534198856808881642355)
          ·
            refine ⟨19686801298285213322463533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13124534198856808881642355 19686801298285213322463533)
            ·
              refine ⟨7382550486856954995923825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19686801298285213322463533 7382550486856954995923825)
              ·
                refine ⟨5536912865142716246942869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7382550486856954995923825 5536912865142716246942869)
                ·
                  refine ⟨259542790553564824075447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5536912865142716246942869 259542790553564824075447)
                  ·
                    rfl

theorem cell20_568640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_568640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568640 prefixEnd_568640 := by exact prefixLift 568640
  have htrace : WordTrace (prefixWord ++ tailWord_568640) baseStart_568640 baseEnd_568640 := by
    simpa [prefixWord, tailWord_568640, baseEnd_568640] using wordTrace_append hprefix tailTrace_568640
  have hstable : (prefixWord ++ tailWord_568640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568640).length < 2 ^ (prefixWord ++ tailWord_568640).sum := by decide
  have hdescent : baseEnd_568640 < baseStart_568640 := by decide
  rcases family_descends (prefixWord ++ tailWord_568640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568657 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 4]
def baseStart_568657 : Nat := 118140960795 + 568657 * 2 ^ 59
def prefixEnd_568657 : Nat := 4983230072969 + 3 ^ 40 * 568657 * 2
def baseEnd_568657 : Nat := 259550549816788320508711

theorem tailTrace_568657 : CollatzResearch.WordTrace tailWord_568657 prefixEnd_568657 259550549816788320508711 := by
  unfold tailWord_568657
  simp only [CollatzResearch.WordTrace]
  refine ⟨20740624700860282728680225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13827083133906855152453483 20740624700860282728680225)
  ·
    refine ⟨15555468525645212046510169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20740624700860282728680225 15555468525645212046510169)
    ·
      refine ⟨11666601394233909034882627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15555468525645212046510169 11666601394233909034882627)
      ·
        refine ⟨17499902091350863552323941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11666601394233909034882627 17499902091350863552323941)
        ·
          refine ⟨3281231642128286916060739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17499902091350863552323941 3281231642128286916060739)
          ·
            refine ⟨4921847463192430374091109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281231642128286916060739 4921847463192430374091109)
            ·
              refine ⟨922846399348580695142083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4921847463192430374091109 922846399348580695142083)
              ·
                refine ⟨1384269599022871042713125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922846399348580695142083 1384269599022871042713125)
                ·
                  refine ⟨259550549816788320508711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1384269599022871042713125 259550549816788320508711)
                  ·
                    rfl

theorem cell20_568657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_568657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568657 prefixEnd_568657 := by exact prefixLift 568657
  have htrace : WordTrace (prefixWord ++ tailWord_568657) baseStart_568657 baseEnd_568657 := by
    simpa [prefixWord, tailWord_568657, baseEnd_568657] using wordTrace_append hprefix tailTrace_568657
  have hstable : (prefixWord ++ tailWord_568657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568657).length < 2 ^ (prefixWord ++ tailWord_568657).sum := by decide
  have hdescent : baseEnd_568657 < baseStart_568657 := by decide
  rcases family_descends (prefixWord ++ tailWord_568657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568709 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 5]
def baseStart_568709 : Nat := 118140960795 + 568709 * 2 ^ 59
def prefixEnd_568709 : Nat := 4983230072969 + 3 ^ 40 * 568709 * 2
def baseEnd_568709 : Nat := 259574284033707250775165

theorem tailTrace_568709 : CollatzResearch.WordTrace tailWord_568709 prefixEnd_568709 259574284033707250775165 := by
  unfold tailWord_568709
  simp only [CollatzResearch.WordTrace]
  refine ⟨20742521296671895609573181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13828347531114597073048787 20742521296671895609573181)
  ·
    refine ⟨7778445486251960853589943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20742521296671895609573181 7778445486251960853589943)
    ·
      refine ⟨11667668229377941280384915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7778445486251960853589943 11667668229377941280384915)
      ·
        refine ⟨17501502344066911920577373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11667668229377941280384915 17501502344066911920577373)
        ·
          refine ⟨6563063379025091970216515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17501502344066911920577373 6563063379025091970216515)
          ·
            refine ⟨9844595068537637955324773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6563063379025091970216515 9844595068537637955324773)
            ·
              refine ⟨1845861575350807116623395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9844595068537637955324773 1845861575350807116623395)
              ·
                refine ⟨2768792363026210674935093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845861575350807116623395 2768792363026210674935093)
                ·
                  refine ⟨259574284033707250775165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2768792363026210674935093 259574284033707250775165)
                  ·
                    rfl

theorem cell20_568709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_568709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568709 prefixEnd_568709 := by exact prefixLift 568709
  have htrace : WordTrace (prefixWord ++ tailWord_568709) baseStart_568709 baseEnd_568709 := by
    simpa [prefixWord, tailWord_568709, baseEnd_568709] using wordTrace_append hprefix tailTrace_568709
  have hstable : (prefixWord ++ tailWord_568709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568709).length < 2 ^ (prefixWord ++ tailWord_568709).sum := by decide
  have hdescent : baseEnd_568709 < baseStart_568709 := by decide
  rcases family_descends (prefixWord ++ tailWord_568709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568712 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 4]
def baseStart_568712 : Nat := 118140960795 + 568712 * 2 ^ 59
def prefixEnd_568712 : Nat := 4983230072969 + 3 ^ 40 * 568712 * 2
def baseEnd_568712 : Nat := 259575653315452573675153

theorem tailTrace_568712 : CollatzResearch.WordTrace tailWord_568712 prefixEnd_568712 259575653315452573675153 := by
  unfold tailWord_568712
  simp only [CollatzResearch.WordTrace]
  refine ⟨10371315357830513560966195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13828420477107351414621593 10371315357830513560966195)
  ·
    refine ⟨15556973036745770341449293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10371315357830513560966195 15556973036745770341449293)
    ·
      refine ⟨5833864888779663878043485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15556973036745770341449293 5833864888779663878043485)
      ·
        refine ⟨2187699333292373954266307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5833864888779663878043485 2187699333292373954266307)
        ·
          refine ⟨3281548999938560931399461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2187699333292373954266307 3281548999938560931399461)
          ·
            refine ⟨615290437488480174637399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3281548999938560931399461 615290437488480174637399)
            ·
              refine ⟨922935656232720261956099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615290437488480174637399 922935656232720261956099)
              ·
                refine ⟨1384403484349080392934149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922935656232720261956099 1384403484349080392934149)
                ·
                  refine ⟨259575653315452573675153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1384403484349080392934149 259575653315452573675153)
                  ·
                    rfl

theorem cell20_568712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_568712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568712 prefixEnd_568712 := by exact prefixLift 568712
  have htrace : WordTrace (prefixWord ++ tailWord_568712) baseStart_568712 baseEnd_568712 := by
    simpa [prefixWord, tailWord_568712, baseEnd_568712] using wordTrace_append hprefix tailTrace_568712
  have hstable : (prefixWord ++ tailWord_568712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568712).length < 2 ^ (prefixWord ++ tailWord_568712).sum := by decide
  have hdescent : baseEnd_568712 < baseStart_568712 := by decide
  rcases family_descends (prefixWord ++ tailWord_568712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568722 : List Nat := [3, 2, 3, 3, 1, 1, 1, 3, 3]
def baseStart_568722 : Nat := 118140960795 + 568722 * 2 ^ 59
def prefixEnd_568722 : Nat := 4983230072969 + 3 ^ 40 * 568722 * 2
def baseEnd_568722 : Nat := 259580217587936983341779

theorem tailTrace_568722 : CollatzResearch.WordTrace tailWord_568722 prefixEnd_568722 259580217587936983341779 := by
  unfold tailWord_568722
  simp only [CollatzResearch.WordTrace]
  refine ⟨5185748861406199707449105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13828663630416532553197613 5185748861406199707449105)
  ·
    refine ⟨3889311646054649780586829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5185748861406199707449105 3889311646054649780586829)
    ·
      refine ⟨1458491867270493667720061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3889311646054649780586829 1458491867270493667720061)
      ·
        refine ⟨546934450226435125395023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1458491867270493667720061 546934450226435125395023)
        ·
          refine ⟨820401675339652688092535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546934450226435125395023 820401675339652688092535)
          ·
            refine ⟨1230602513009479032138803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820401675339652688092535 1230602513009479032138803)
            ·
              refine ⟨1845903769514218548208205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1230602513009479032138803 1845903769514218548208205)
              ·
                refine ⟨692213913567831955578077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1845903769514218548208205 692213913567831955578077)
                ·
                  refine ⟨259580217587936983341779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692213913567831955578077 259580217587936983341779)
                  ·
                    rfl

theorem cell20_568722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_568722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568722 prefixEnd_568722 := by exact prefixLift 568722
  have htrace : WordTrace (prefixWord ++ tailWord_568722) baseStart_568722 baseEnd_568722 := by
    simpa [prefixWord, tailWord_568722, baseEnd_568722] using wordTrace_append hprefix tailTrace_568722
  have hstable : (prefixWord ++ tailWord_568722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568722).length < 2 ^ (prefixWord ++ tailWord_568722).sum := by decide
  have hdescent : baseEnd_568722 < baseStart_568722 := by decide
  rcases family_descends (prefixWord ++ tailWord_568722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568754 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_568754 : Nat := 118140960795 + 568754 * 2 ^ 59
def prefixEnd_568754 : Nat := 4983230072969 + 3 ^ 40 * 568754 * 2
def baseEnd_568754 : Nat := 259594823259887094274981

theorem tailTrace_568754 : CollatzResearch.WordTrace tailWord_568754 prefixEnd_568754 259594823259887094274981 := by
  unfold tailWord_568754
  simp only [CollatzResearch.WordTrace]
  refine ⟨5186040645377217073740329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13829441721005912196640877 5186040645377217073740329)
  ·
    refine ⟨3889530484032912805305247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5186040645377217073740329 3889530484032912805305247)
    ·
      refine ⟨5834295726049369207957871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3889530484032912805305247 5834295726049369207957871)
      ·
        refine ⟨8751443589074053811936807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5834295726049369207957871 8751443589074053811936807)
        ·
          refine ⟨13127165383611080717905211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8751443589074053811936807 13127165383611080717905211)
          ·
            refine ⟨19690748075416621076857817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13127165383611080717905211 19690748075416621076857817)
            ·
              refine ⟨14768061056562465807643363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19690748075416621076857817 14768061056562465807643363)
              ·
                refine ⟨22152091584843698711465045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14768061056562465807643363 22152091584843698711465045)
                ·
                  refine ⟨259594823259887094274981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22152091584843698711465045 259594823259887094274981)
                  ·
                    rfl

theorem cell20_568754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_568754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568754 prefixEnd_568754 := by exact prefixLift 568754
  have htrace : WordTrace (prefixWord ++ tailWord_568754) baseStart_568754 baseEnd_568754 := by
    simpa [prefixWord, tailWord_568754, baseEnd_568754] using wordTrace_append hprefix tailTrace_568754
  have hstable : (prefixWord ++ tailWord_568754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568754).length < 2 ^ (prefixWord ++ tailWord_568754).sum := by decide
  have hdescent : baseEnd_568754 < baseStart_568754 := by decide
  rcases family_descends (prefixWord ++ tailWord_568754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568761 : List Nat := [1, 2, 1, 4, 12]
def baseStart_568761 : Nat := 118140960795 + 568761 * 2 ^ 59
def prefixEnd_568761 : Nat := 4983230072969 + 3 ^ 40 * 568761 * 2
def baseEnd_568761 : Nat := 3204913805563286185699

theorem tailTrace_568761 : CollatzResearch.WordTrace tailWord_568761 prefixEnd_568761 3204913805563286185699 := by
  unfold tailWord_568761
  simp only [CollatzResearch.WordTrace]
  refine ⟨20744417892483508490466137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13829611928322338993644091 20744417892483508490466137)
  ·
    refine ⟨15558313419362631367849603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20744417892483508490466137 15558313419362631367849603)
    ·
      refine ⟨23337470129043947051774405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15558313419362631367849603 23337470129043947051774405)
      ·
        refine ⟨4375775649195740072207701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23337470129043947051774405 4375775649195740072207701)
        ·
          refine ⟨3204913805563286185699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4375775649195740072207701 3204913805563286185699)
          ·
            rfl

theorem cell20_568761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 12].length) (baseStart_568761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568761 prefixEnd_568761 := by exact prefixLift 568761
  have htrace : WordTrace (prefixWord ++ tailWord_568761) baseStart_568761 baseEnd_568761 := by
    simpa [prefixWord, tailWord_568761, baseEnd_568761] using wordTrace_append hprefix tailTrace_568761
  have hstable : (prefixWord ++ tailWord_568761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568761).length < 2 ^ (prefixWord ++ tailWord_568761).sum := by decide
  have hdescent : baseEnd_568761 < baseStart_568761 := by decide
  rcases family_descends (prefixWord ++ tailWord_568761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568778 : List Nat := [3, 1, 2, 1, 2, 3, 3, 5]
def baseStart_568778 : Nat := 118140960795 + 568778 * 2 ^ 59
def prefixEnd_568778 : Nat := 4983230072969 + 3 ^ 40 * 568778 * 2
def baseEnd_568778 : Nat := 86535259171283225824961

theorem tailTrace_568778 : CollatzResearch.WordTrace tailWord_568778 prefixEnd_568778 86535259171283225824961 := by
  unfold tailWord_568778
  simp only [CollatzResearch.WordTrace]
  refine ⟨5186259483355480098458747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13830025288947946929223325 5186259483355480098458747)
  ·
    refine ⟨7779389225033220147688121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5186259483355480098458747 7779389225033220147688121)
    ·
      refine ⟨5834541918774915110766091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7779389225033220147688121 5834541918774915110766091)
      ·
        refine ⟨8751812878162372666149137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5834541918774915110766091 8751812878162372666149137)
        ·
          refine ⟨6563859658621779499611853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8751812878162372666149137 6563859658621779499611853)
          ·
            refine ⟨2461447371983167312354445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6563859658621779499611853 2461447371983167312354445)
            ·
              refine ⟨923042764493687742132917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2461447371983167312354445 923042764493687742132917)
              ·
                refine ⟨86535259171283225824961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 923042764493687742132917 86535259171283225824961)
                ·
                  rfl

theorem cell20_568778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_568778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568778 prefixEnd_568778 := by exact prefixLift 568778
  have htrace : WordTrace (prefixWord ++ tailWord_568778) baseStart_568778 baseEnd_568778 := by
    simpa [prefixWord, tailWord_568778, baseEnd_568778] using wordTrace_append hprefix tailTrace_568778
  have hstable : (prefixWord ++ tailWord_568778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568778).length < 2 ^ (prefixWord ++ tailWord_568778).sum := by decide
  have hdescent : baseEnd_568778 < baseStart_568778 := by decide
  rcases family_descends (prefixWord ++ tailWord_568778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568788 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 4]
def baseStart_568788 : Nat := 118140960795 + 568788 * 2 ^ 59
def prefixEnd_568788 : Nat := 4983230072969 + 3 ^ 40 * 568788 * 2
def baseEnd_568788 : Nat := 259610341786334087141509

theorem tailTrace_568788 : CollatzResearch.WordTrace tailWord_568788 prefixEnd_568788 259610341786334087141509 := by
  unfold tailWord_568788
  simp only [CollatzResearch.WordTrace]
  refine ⟨10372701331692846050849509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13830268442257128067799345 10372701331692846050849509)
  ·
    refine ⟨1944881499692408634534283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10372701331692846050849509 1944881499692408634534283)
    ·
      refine ⟨2917322249538612951801425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1944881499692408634534283 2917322249538612951801425)
      ·
        refine ⟨2187991687153959713851069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2917322249538612951801425 2187991687153959713851069)
        ·
          refine ⟨820496882682734892694151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2187991687153959713851069 820496882682734892694151)
          ·
            refine ⟨1230745324024102339041227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820496882682734892694151 1230745324024102339041227)
            ·
              refine ⟨1846117986036153508561841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1230745324024102339041227 1846117986036153508561841)
              ·
                refine ⟨1384588489527115131421381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1846117986036153508561841 1384588489527115131421381)
                ·
                  refine ⟨259610341786334087141509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1384588489527115131421381 259610341786334087141509)
                  ·
                    rfl

theorem cell20_568788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_568788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568788 prefixEnd_568788 := by exact prefixLift 568788
  have htrace : WordTrace (prefixWord ++ tailWord_568788) baseStart_568788 baseEnd_568788 := by
    simpa [prefixWord, tailWord_568788, baseEnd_568788] using wordTrace_append hprefix tailTrace_568788
  have hstable : (prefixWord ++ tailWord_568788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568788).length < 2 ^ (prefixWord ++ tailWord_568788).sum := by decide
  have hdescent : baseEnd_568788 < baseStart_568788 := by decide
  rcases family_descends (prefixWord ++ tailWord_568788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568792 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 6]
def baseStart_568792 : Nat := 118140960795 + 568792 * 2 ^ 59
def prefixEnd_568792 : Nat := 4983230072969 + 3 ^ 40 * 568792 * 2
def baseEnd_568792 : Nat := 259612167495327851008159

theorem tailTrace_568792 : CollatzResearch.WordTrace tailWord_568792 prefixEnd_568792 259612167495327851008159 := by
  unfold tailWord_568792
  simp only [CollatzResearch.WordTrace]
  refine ⟨10372774277685600392422315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13830365703580800523229753 10372774277685600392422315)
  ·
    refine ⟨15559161416528400588633473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10372774277685600392422315 15559161416528400588633473)
    ·
      refine ⟨11669371062396300441475105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15559161416528400588633473 11669371062396300441475105)
      ·
        refine ⟨8752028296797225331106329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11669371062396300441475105 8752028296797225331106329)
        ·
          refine ⟨6564021222597918998329747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8752028296797225331106329 6564021222597918998329747)
          ·
            refine ⟨9846031833896878497494621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6564021222597918998329747 9846031833896878497494621)
            ·
              refine ⟨3692261937711329436560483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9846031833896878497494621 3692261937711329436560483)
              ·
                refine ⟨5538392906566994154840725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3692261937711329436560483 5538392906566994154840725)
                ·
                  refine ⟨259612167495327851008159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5538392906566994154840725 259612167495327851008159)
                  ·
                    rfl

theorem cell20_568792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_568792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568792 prefixEnd_568792 := by exact prefixLift 568792
  have htrace : WordTrace (prefixWord ++ tailWord_568792) baseStart_568792 baseEnd_568792 := by
    simpa [prefixWord, tailWord_568792, baseEnd_568792] using wordTrace_append hprefix tailTrace_568792
  have hstable : (prefixWord ++ tailWord_568792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568792).length < 2 ^ (prefixWord ++ tailWord_568792).sum := by decide
  have hdescent : baseEnd_568792 < baseStart_568792 := by decide
  rcases family_descends (prefixWord ++ tailWord_568792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568805 : List Nat := [1, 3, 1, 5, 1, 2, 2, 3, 2]
def baseStart_568805 : Nat := 118140960795 + 568805 * 2 ^ 59
def prefixEnd_568805 : Nat := 4983230072969 + 3 ^ 40 * 568805 * 2
def baseEnd_568805 : Nat := 259618101049557583574773

theorem tailTrace_568805 : CollatzResearch.WordTrace tailWord_568805 prefixEnd_568805 259618101049557583574773 := by
  unfold tailWord_568805
  simp only [CollatzResearch.WordTrace]
  refine ⟨20746022704324104005067869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13830681802882736003378579 20746022704324104005067869)
  ·
    refine ⟨7779758514121539001900451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20746022704324104005067869 7779758514121539001900451)
    ·
      refine ⟨11669637771182308502850677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7779758514121539001900451 11669637771182308502850677)
      ·
        refine ⟨1094028541048341422142251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11669637771182308502850677 1094028541048341422142251)
        ·
          refine ⟨1641042811572512133213377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1094028541048341422142251 1641042811572512133213377)
          ·
            refine ⟨1230782108679384099910033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1641042811572512133213377 1230782108679384099910033)
            ·
              refine ⟨923086581509538074932525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1230782108679384099910033 923086581509538074932525)
              ·
                refine ⟨346157468066076778099697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 923086581509538074932525 346157468066076778099697)
                ·
                  refine ⟨259618101049557583574773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346157468066076778099697 259618101049557583574773)
                  ·
                    rfl

theorem cell20_568805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_568805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568805 prefixEnd_568805 := by exact prefixLift 568805
  have htrace : WordTrace (prefixWord ++ tailWord_568805) baseStart_568805 baseEnd_568805 := by
    simpa [prefixWord, tailWord_568805, baseEnd_568805] using wordTrace_append hprefix tailTrace_568805
  have hstable : (prefixWord ++ tailWord_568805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568805).length < 2 ^ (prefixWord ++ tailWord_568805).sum := by decide
  have hdescent : baseEnd_568805 < baseStart_568805 := by decide
  rcases family_descends (prefixWord ++ tailWord_568805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568823 : List Nat := [1, 1, 3, 1, 1, 1, 1, 8, 3]
def baseStart_568823 : Nat := 118140960795 + 568823 * 2 ^ 59
def prefixEnd_568823 : Nat := 4983230072969 + 3 ^ 40 * 568823 * 2
def baseEnd_568823 : Nat := 259626316740029520974699

theorem tailTrace_568823 : CollatzResearch.WordTrace tailWord_568823 prefixEnd_568823 259626316740029520974699 := by
  unfold tailWord_568823
  simp only [CollatzResearch.WordTrace]
  refine ⟨20746679218258893079223123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13831119478839262052815415 20746679218258893079223123)
  ·
    refine ⟨31120018827388339618834685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20746679218258893079223123 31120018827388339618834685)
    ·
      refine ⟨11670007060270627357063007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31120018827388339618834685 11670007060270627357063007)
      ·
        refine ⟨17505010590405941035594511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11670007060270627357063007 17505010590405941035594511)
        ·
          refine ⟨26257515885608911553391767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17505010590405941035594511 26257515885608911553391767)
          ·
            refine ⟨39386273828413367330087651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26257515885608911553391767 39386273828413367330087651)
            ·
              refine ⟨59079410742620050995131477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39386273828413367330087651 59079410742620050995131477)
              ·
                refine ⟨692336844640078722599197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 59079410742620050995131477 692336844640078722599197)
                ·
                  refine ⟨259626316740029520974699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692336844640078722599197 259626316740029520974699)
                  ·
                    rfl

theorem cell20_568823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 3].length) (baseStart_568823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568823 prefixEnd_568823 := by exact prefixLift 568823
  have htrace : WordTrace (prefixWord ++ tailWord_568823) baseStart_568823 baseEnd_568823 := by
    simpa [prefixWord, tailWord_568823, baseEnd_568823] using wordTrace_append hprefix tailTrace_568823
  have hstable : (prefixWord ++ tailWord_568823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568823).length < 2 ^ (prefixWord ++ tailWord_568823).sum := by decide
  have hdescent : baseEnd_568823 < baseStart_568823 := by decide
  rcases family_descends (prefixWord ++ tailWord_568823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568836 : List Nat := [2, 3, 2, 3, 2, 1, 3, 1, 3]
def baseStart_568836 : Nat := 118140960795 + 568836 * 2 ^ 59
def prefixEnd_568836 : Nat := 4983230072969 + 3 ^ 40 * 568836 * 2
def baseEnd_568836 : Nat := 259632250294259253541313

theorem tailTrace_568836 : CollatzResearch.WordTrace tailWord_568836 prefixEnd_568836 259632250294259253541313 := by
  unfold tailWord_568836
  simp only [CollatzResearch.WordTrace]
  refine ⟨10373576683605898149723181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13831435578141197532964241 10373576683605898149723181)
  ·
    refine ⟨3890091256352211806146193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10373576683605898149723181 3890091256352211806146193)
    ·
      refine ⟨2917568442264158854609645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3890091256352211806146193 2917568442264158854609645)
      ·
        refine ⟨1094088165849059570478617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2917568442264158854609645 1094088165849059570478617)
        ·
          refine ⟨820566124386794677858963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1094088165849059570478617 820566124386794677858963)
          ·
            refine ⟨1230849186580192016788445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820566124386794677858963 1230849186580192016788445)
            ·
              refine ⟨461568444967572006295667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1230849186580192016788445 461568444967572006295667)
              ·
                refine ⟨692352667451358009443501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461568444967572006295667 692352667451358009443501)
                ·
                  refine ⟨259632250294259253541313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692352667451358009443501 259632250294259253541313)
                  ·
                    rfl

theorem cell20_568836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_568836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568836 prefixEnd_568836 := by exact prefixLift 568836
  have htrace : WordTrace (prefixWord ++ tailWord_568836) baseStart_568836 baseEnd_568836 := by
    simpa [prefixWord, tailWord_568836, baseEnd_568836] using wordTrace_append hprefix tailTrace_568836
  have hstable : (prefixWord ++ tailWord_568836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568836).length < 2 ^ (prefixWord ++ tailWord_568836).sum := by decide
  have hdescent : baseEnd_568836 < baseStart_568836 := by decide
  rcases family_descends (prefixWord ++ tailWord_568836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568837 : List Nat := [1, 3, 1, 1, 2, 2, 1, 9]
def baseStart_568837 : Nat := 118140960795 + 568837 * 2 ^ 59
def prefixEnd_568837 : Nat := 4983230072969 + 3 ^ 40 * 568837 * 2
def baseEnd_568837 : Nat := 86544235573835898169325

theorem tailTrace_568837 : CollatzResearch.WordTrace tailWord_568837 prefixEnd_568837 86544235573835898169325 := by
  unfold tailWord_568837
  simp only [CollatzResearch.WordTrace]
  refine ⟨20747189840208173470232765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13831459893472115646821843 20747189840208173470232765)
  ·
    refine ⟨7780196190078065051337287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20747189840208173470232765 7780196190078065051337287)
    ·
      refine ⟨11670294285117097577005931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7780196190078065051337287 11670294285117097577005931)
      ·
        refine ⟨17505441427675646365508897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11670294285117097577005931 17505441427675646365508897)
        ·
          refine ⟨13129081070756734774131673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17505441427675646365508897 13129081070756734774131673)
          ·
            refine ⟨9846810803067551080598755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13129081070756734774131673 9846810803067551080598755)
            ·
              refine ⟨14770216204601326620898133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9846810803067551080598755 14770216204601326620898133)
              ·
                refine ⟨86544235573835898169325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14770216204601326620898133 86544235573835898169325)
                ·
                  rfl

theorem cell20_568837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 9].length) (baseStart_568837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568837 prefixEnd_568837 := by exact prefixLift 568837
  have htrace : WordTrace (prefixWord ++ tailWord_568837) baseStart_568837 baseEnd_568837 := by
    simpa [prefixWord, tailWord_568837, baseEnd_568837] using wordTrace_append hprefix tailTrace_568837
  have hstable : (prefixWord ++ tailWord_568837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568837).length < 2 ^ (prefixWord ++ tailWord_568837).sum := by decide
  have hdescent : baseEnd_568837 < baseStart_568837 := by decide
  rcases family_descends (prefixWord ++ tailWord_568837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568861 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 7]
def baseStart_568861 : Nat := 118140960795 + 568861 * 2 ^ 59
def prefixEnd_568861 : Nat := 4983230072969 + 3 ^ 40 * 568861 * 2
def baseEnd_568861 : Nat := 259643660975470277707877

theorem tailTrace_568861 : CollatzResearch.WordTrace tailWord_568861 prefixEnd_568861 259643660975470277707877 := by
  unfold tailWord_568861
  simp only [CollatzResearch.WordTrace]
  refine ⟨20748065192121225569106437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13832043461414150379404291 20748065192121225569106437)
  ·
    refine ⟨3890262223522729794207457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20748065192121225569106437 3890262223522729794207457)
    ·
      refine ⟨2917696667642047345655593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3890262223522729794207457 2917696667642047345655593)
      ·
        refine ⟨2188272500731535509241695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2917696667642047345655593 2188272500731535509241695)
        ·
          refine ⟨3282408751097303263862543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188272500731535509241695 3282408751097303263862543)
          ·
            refine ⟨4923613126645954895793815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3282408751097303263862543 4923613126645954895793815)
            ·
              refine ⟨7385419689968932343690723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4923613126645954895793815 7385419689968932343690723)
              ·
                refine ⟨11078129534953398515536085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7385419689968932343690723 11078129534953398515536085)
                ·
                  refine ⟨259643660975470277707877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11078129534953398515536085 259643660975470277707877)
                  ·
                    rfl

theorem cell20_568861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_568861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568861 prefixEnd_568861 := by exact prefixLift 568861
  have htrace : WordTrace (prefixWord ++ tailWord_568861) baseStart_568861 baseEnd_568861 := by
    simpa [prefixWord, tailWord_568861, baseEnd_568861] using wordTrace_append hprefix tailTrace_568861
  have hstable : (prefixWord ++ tailWord_568861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568861).length < 2 ^ (prefixWord ++ tailWord_568861).sum := by decide
  have hdescent : baseEnd_568861 < baseStart_568861 := by decide
  rcases family_descends (prefixWord ++ tailWord_568861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568878 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_568878 : Nat := 118140960795 + 568878 * 2 ^ 59
def prefixEnd_568878 : Nat := 4983230072969 + 3 ^ 40 * 568878 * 2
def baseEnd_568878 : Nat := 259651420238693774141141

theorem tailTrace_568878 : CollatzResearch.WordTrace tailWord_568878 prefixEnd_568878 259651420238693774141141 := by
  unfold tailWord_568878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2593585654132454684059411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13832456822039758314983525 2593585654132454684059411)
  ·
    refine ⟨3890378481198682026089117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2593585654132454684059411 3890378481198682026089117)
    ·
      refine ⟨1458891930449505759783419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3890378481198682026089117 1458891930449505759783419)
      ·
        refine ⟨2188337895674258639675129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1458891930449505759783419 2188337895674258639675129)
        ·
          refine ⟨1641253421755693979756347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2188337895674258639675129 1641253421755693979756347)
          ·
            refine ⟨2461880132633540969634521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1641253421755693979756347 2461880132633540969634521)
            ·
              refine ⟨1846410099475155727225891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2461880132633540969634521 1846410099475155727225891)
              ·
                refine ⟨2769615149212733590838837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1846410099475155727225891 2769615149212733590838837)
                ·
                  refine ⟨259651420238693774141141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2769615149212733590838837 259651420238693774141141)
                  ·
                    rfl

theorem cell20_568878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_568878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568878 prefixEnd_568878 := by exact prefixLift 568878
  have htrace : WordTrace (prefixWord ++ tailWord_568878) baseStart_568878 baseEnd_568878 := by
    simpa [prefixWord, tailWord_568878, baseEnd_568878] using wordTrace_append hprefix tailTrace_568878
  have hstable : (prefixWord ++ tailWord_568878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568878).length < 2 ^ (prefixWord ++ tailWord_568878).sum := by decide
  have hdescent : baseEnd_568878 < baseStart_568878 := by decide
  rcases family_descends (prefixWord ++ tailWord_568878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568885 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 4]
def baseStart_568885 : Nat := 118140960795 + 568885 * 2 ^ 59
def prefixEnd_568885 : Nat := 4983230072969 + 3 ^ 40 * 568885 * 2
def baseEnd_568885 : Nat := 259654615229432860907779

theorem tailTrace_568885 : CollatzResearch.WordTrace tailWord_568885 prefixEnd_568885 259654615229432860907779 := by
  unfold tailWord_568885
  simp only [CollatzResearch.WordTrace]
  refine ⟨20748940544034277667980109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13832627029356185111986739 20748940544034277667980109)
  ·
    refine ⟨7780852704012854125492541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20748940544034277667980109 7780852704012854125492541)
    ·
      refine ⟨2917819764004820297059703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7780852704012854125492541 2917819764004820297059703)
      ·
        refine ⟨4376729646007230445589555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2917819764004820297059703 4376729646007230445589555)
        ·
          refine ⟨6565094469010845668384333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4376729646007230445589555 6565094469010845668384333)
          ·
            refine ⟨2461910425879067125644125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6565094469010845668384333 2461910425879067125644125)
            ·
              refine ⟨923216409704650172116547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2461910425879067125644125 923216409704650172116547)
              ·
                refine ⟨1384824614556975258174821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 923216409704650172116547 1384824614556975258174821)
                ·
                  refine ⟨259654615229432860907779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1384824614556975258174821 259654615229432860907779)
                  ·
                    rfl

theorem cell20_568885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_568885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568885 prefixEnd_568885 := by exact prefixLift 568885
  have htrace : WordTrace (prefixWord ++ tailWord_568885) baseStart_568885 baseEnd_568885 := by
    simpa [prefixWord, tailWord_568885, baseEnd_568885] using wordTrace_append hprefix tailTrace_568885
  have hstable : (prefixWord ++ tailWord_568885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568885).length < 2 ^ (prefixWord ++ tailWord_568885).sum := by decide
  have hdescent : baseEnd_568885 < baseStart_568885 := by decide
  rcases family_descends (prefixWord ++ tailWord_568885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568895 : List Nat := [1, 1, 2, 2, 3, 5, 2, 1, 3]
def baseStart_568895 : Nat := 118140960795 + 568895 * 2 ^ 59
def prefixEnd_568895 : Nat := 4983230072969 + 3 ^ 40 * 568895 * 2
def baseEnd_568895 : Nat := 259659179501917270574405

theorem tailTrace_568895 : CollatzResearch.WordTrace tailWord_568895 prefixEnd_568895 259659179501917270574405 := by
  unfold tailWord_568895
  simp only [CollatzResearch.WordTrace]
  refine ⟨20749305273998049375844139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13832870182665366250562759 20749305273998049375844139)
  ·
    refine ⟨31123957910997074063766209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20749305273998049375844139 31123957910997074063766209)
    ·
      refine ⟨23342968433247805547824657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31123957910997074063766209 23342968433247805547824657)
      ·
        refine ⟨17507226324935854160868493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23342968433247805547824657 17507226324935854160868493)
        ·
          refine ⟨6565209871850945310325685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17507226324935854160868493 6565209871850945310325685)
          ·
            refine ⟨615488425486026122843033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6565209871850945310325685 615488425486026122843033)
            ·
              refine ⟨461616319114519592132275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615488425486026122843033 461616319114519592132275)
              ·
                refine ⟨692424478671779388198413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461616319114519592132275 692424478671779388198413)
                ·
                  refine ⟨259659179501917270574405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692424478671779388198413 259659179501917270574405)
                  ·
                    rfl

theorem cell20_568895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 3].length) (baseStart_568895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568895 prefixEnd_568895 := by exact prefixLift 568895
  have htrace : WordTrace (prefixWord ++ tailWord_568895) baseStart_568895 baseEnd_568895 := by
    simpa [prefixWord, tailWord_568895, baseEnd_568895] using wordTrace_append hprefix tailTrace_568895
  have hstable : (prefixWord ++ tailWord_568895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568895).length < 2 ^ (prefixWord ++ tailWord_568895).sum := by decide
  have hdescent : baseEnd_568895 < baseStart_568895 := by decide
  rcases family_descends (prefixWord ++ tailWord_568895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568906 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_568906 : Nat := 118140960795 + 568906 * 2 ^ 59
def prefixEnd_568906 : Nat := 4983230072969 + 3 ^ 40 * 568906 * 2
def baseEnd_568906 : Nat := 259664200201650121207693

theorem tailTrace_568906 : CollatzResearch.WordTrace tailWord_568906 prefixEnd_568906 259664200201650121207693 := by
  unfold tailWord_568906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5187426619239549563623643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13833137651305465502996381 5187426619239549563623643)
  ·
    refine ⟨7781139928859324345435465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5187426619239549563623643 7781139928859324345435465)
    ·
      refine ⟨5835854946644493259076599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7781139928859324345435465 5835854946644493259076599)
      ·
        refine ⟨8753782419966739888614899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5835854946644493259076599 8753782419966739888614899)
        ·
          refine ⟨13130673629950109832922349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8753782419966739888614899 13130673629950109832922349)
          ·
            refine ⟨4924002611231291187345881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13130673629950109832922349 4924002611231291187345881)
            ·
              refine ⟨3693001958423468390509411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4924002611231291187345881 3693001958423468390509411)
              ·
                refine ⟨5539502937635202585764117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3693001958423468390509411 5539502937635202585764117)
                ·
                  refine ⟨259664200201650121207693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5539502937635202585764117 259664200201650121207693)
                  ·
                    rfl

theorem cell20_568906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_568906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568906 prefixEnd_568906 := by exact prefixLift 568906
  have htrace : WordTrace (prefixWord ++ tailWord_568906) baseStart_568906 baseEnd_568906 := by
    simpa [prefixWord, tailWord_568906, baseEnd_568906] using wordTrace_append hprefix tailTrace_568906
  have hstable : (prefixWord ++ tailWord_568906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568906).length < 2 ^ (prefixWord ++ tailWord_568906).sum := by decide
  have hdescent : baseEnd_568906 < baseStart_568906 := by decide
  rcases family_descends (prefixWord ++ tailWord_568906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568913 : List Nat := [1, 2, 2, 1, 3, 2, 1, 8]
def baseStart_568913 : Nat := 118140960795 + 568913 * 2 ^ 59
def prefixEnd_568913 : Nat := 4983230072969 + 3 ^ 40 * 568913 * 2
def baseEnd_568913 : Nat := 86555798397463069324777

theorem tailTrace_568913 : CollatzResearch.WordTrace tailWord_568913 prefixEnd_568913 86555798397463069324777 := by
  unfold tailWord_568913
  simp only [CollatzResearch.WordTrace]
  refine ⟨20749961787932838449999393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13833307858621892299999595 20749961787932838449999393)
  ·
    refine ⟨15562471340949628837499545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20749961787932838449999393 15562471340949628837499545)
    ·
      refine ⟨11671853505712221628124659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15562471340949628837499545 11671853505712221628124659)
      ·
        refine ⟨17507780258568332442186989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11671853505712221628124659 17507780258568332442186989)
        ·
          refine ⟨6565417596963124665820121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17507780258568332442186989 6565417596963124665820121)
          ·
            refine ⟨4924063197722343499365091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6565417596963124665820121 4924063197722343499365091)
            ·
              refine ⟨7386094796583515249047637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4924063197722343499365091 7386094796583515249047637)
              ·
                refine ⟨86555798397463069324777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7386094796583515249047637 86555798397463069324777)
                ·
                  rfl

theorem cell20_568913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 8].length) (baseStart_568913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568913 prefixEnd_568913 := by exact prefixLift 568913
  have htrace : WordTrace (prefixWord ++ tailWord_568913) baseStart_568913 baseEnd_568913 := by
    simpa [prefixWord, tailWord_568913, baseEnd_568913] using wordTrace_append hprefix tailTrace_568913
  have hstable : (prefixWord ++ tailWord_568913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568913).length < 2 ^ (prefixWord ++ tailWord_568913).sum := by decide
  have hdescent : baseEnd_568913 < baseStart_568913 := by decide
  rcases family_descends (prefixWord ++ tailWord_568913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568936 : List Nat := [2, 1, 4, 3, 1, 3, 2, 2, 2]
def baseStart_568936 : Nat := 118140960795 + 568936 * 2 ^ 59
def prefixEnd_568936 : Nat := 4983230072969 + 3 ^ 40 * 568936 * 2
def baseEnd_568936 : Nat := 259677893019103350207571

theorem tailTrace_568936 : CollatzResearch.WordTrace tailWord_568936 prefixEnd_568936 259677893019103350207571 := by
  unfold tailWord_568936
  simp only [CollatzResearch.WordTrace]
  refine ⟨10375400333424756689043331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13833867111233008918724441 10375400333424756689043331)
  ·
    refine ⟨15563100500137135033564997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10375400333424756689043331 15563100500137135033564997)
    ·
      refine ⟨2918081343775712818793437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15563100500137135033564997 2918081343775712818793437)
      ·
        refine ⟨1094280503915892307047539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2918081343775712818793437 1094280503915892307047539)
        ·
          refine ⟨1641420755873838460571309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1094280503915892307047539 1641420755873838460571309)
          ·
            refine ⟨615532783452689422714241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1641420755873838460571309 615532783452689422714241)
            ·
              refine ⟨461649587589517067035681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615532783452689422714241 461649587589517067035681)
              ·
                refine ⟨346237190692137800276761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 461649587589517067035681 346237190692137800276761)
                ·
                  refine ⟨259677893019103350207571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346237190692137800276761 259677893019103350207571)
                  ·
                    rfl

theorem cell20_568936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 2].length) (baseStart_568936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568936 prefixEnd_568936 := by exact prefixLift 568936
  have htrace : WordTrace (prefixWord ++ tailWord_568936) baseStart_568936 baseEnd_568936 := by
    simpa [prefixWord, tailWord_568936, baseEnd_568936] using wordTrace_append hprefix tailTrace_568936
  have hstable : (prefixWord ++ tailWord_568936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568936).length < 2 ^ (prefixWord ++ tailWord_568936).sum := by decide
  have hdescent : baseEnd_568936 < baseStart_568936 := by decide
  rcases family_descends (prefixWord ++ tailWord_568936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568937 : List Nat := [1, 2, 1, 1, 1, 4, 3, 4, 3]
def baseStart_568937 : Nat := 118140960795 + 568937 * 2 ^ 59
def prefixEnd_568937 : Nat := 4983230072969 + 3 ^ 40 * 568937 * 2
def baseEnd_568937 : Nat := 259678349446351791174233

theorem tailTrace_568937 : CollatzResearch.WordTrace tailWord_568937 prefixEnd_568937 259678349446351791174233 := by
  unfold tailWord_568937
  simp only [CollatzResearch.WordTrace]
  refine ⟨20750837139845890548873065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13833891426563927032582043 20750837139845890548873065)
  ·
    refine ⟨15563127854884417911654799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20750837139845890548873065 15563127854884417911654799)
    ·
      refine ⟨23344691782326626867482199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15563127854884417911654799 23344691782326626867482199)
      ·
        refine ⟨35017037673489940301223299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23344691782326626867482199 35017037673489940301223299)
        ·
          refine ⟨52525556510234910451834949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35017037673489940301223299 52525556510234910451834949)
          ·
            refine ⟨9848541845669045709719053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52525556510234910451834949 9848541845669045709719053)
            ·
              refine ⟨3693203192125892141144645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9848541845669045709719053 3693203192125892141144645)
              ·
                refine ⟨692475598523604776464621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3693203192125892141144645 692475598523604776464621)
                ·
                  refine ⟨259678349446351791174233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692475598523604776464621 259678349446351791174233)
                  ·
                    rfl

theorem cell20_568937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_568937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568937 prefixEnd_568937 := by exact prefixLift 568937
  have htrace : WordTrace (prefixWord ++ tailWord_568937) baseStart_568937 baseEnd_568937 := by
    simpa [prefixWord, tailWord_568937, baseEnd_568937] using wordTrace_append hprefix tailTrace_568937
  have hstable : (prefixWord ++ tailWord_568937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568937).length < 2 ^ (prefixWord ++ tailWord_568937).sum := by decide
  have hdescent : baseEnd_568937 < baseStart_568937 := by decide
  rcases family_descends (prefixWord ++ tailWord_568937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568961 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 4]
def baseStart_568961 : Nat := 118140960795 + 568961 * 2 ^ 59
def prefixEnd_568961 : Nat := 4983230072969 + 3 ^ 40 * 568961 * 2
def baseEnd_568961 : Nat := 259689303700314374374135

theorem tailTrace_568961 : CollatzResearch.WordTrace tailWord_568961 prefixEnd_568961 259689303700314374374135 := by
  unfold tailWord_568961
  simp only [CollatzResearch.WordTrace]
  refine ⟨20751712491758942647746737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13834474994505961765164491 20751712491758942647746737)
  ·
    refine ⟨15563784368819206985810053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20751712491758942647746737 15563784368819206985810053)
    ·
      refine ⟨2918209569153601309839385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15563784368819206985810053 2918209569153601309839385)
      ·
        refine ⟨2188657176865200982379539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2918209569153601309839385 2188657176865200982379539)
        ·
          refine ⟨3282985765297801473569309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188657176865200982379539 3282985765297801473569309)
          ·
            refine ⟨1231119661986675552588491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3282985765297801473569309 1231119661986675552588491)
            ·
              refine ⟨1846679492980013328882737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1231119661986675552588491 1846679492980013328882737)
              ·
                refine ⟨1385009619735009996662053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1846679492980013328882737 1385009619735009996662053)
                ·
                  refine ⟨259689303700314374374135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1385009619735009996662053 259689303700314374374135)
                  ·
                    rfl

theorem cell20_568961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_568961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568961 prefixEnd_568961 := by exact prefixLift 568961
  have htrace : WordTrace (prefixWord ++ tailWord_568961) baseStart_568961 baseEnd_568961 := by
    simpa [prefixWord, tailWord_568961, baseEnd_568961] using wordTrace_append hprefix tailTrace_568961
  have hstable : (prefixWord ++ tailWord_568961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568961).length < 2 ^ (prefixWord ++ tailWord_568961).sum := by decide
  have hdescent : baseEnd_568961 < baseStart_568961 := by decide
  rcases family_descends (prefixWord ++ tailWord_568961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568988 : List Nat := [2, 2, 3, 2, 4, 1, 1, 2, 3]
def baseStart_568988 : Nat := 118140960795 + 568988 * 2 ^ 59
def prefixEnd_568988 : Nat := 4983230072969 + 3 ^ 40 * 568988 * 2
def baseEnd_568988 : Nat := 259701627236022280474025

theorem tailTrace_568988 : CollatzResearch.WordTrace tailWord_568988 prefixEnd_568988 259701627236022280474025 := by
  unfold tailWord_568988
  simp only [CollatzResearch.WordTrace]
  refine ⟨10376348631330563129489809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13835131508440750839319745 10376348631330563129489809)
  ·
    refine ⟨7782261473497922347117357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10376348631330563129489809 7782261473497922347117357)
    ·
      refine ⟨2918348052561720880169009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7782261473497922347117357 2918348052561720880169009)
      ·
        refine ⟨2188761039421290660126757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2918348052561720880169009 2188761039421290660126757)
        ·
          refine ⟨410392694891491998773767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2188761039421290660126757 410392694891491998773767)
          ·
            refine ⟨615589042337237998160651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410392694891491998773767 615589042337237998160651)
            ·
              refine ⟨923383563505856997240977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615589042337237998160651 923383563505856997240977)
              ·
                refine ⟨692537672629392747930733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923383563505856997240977 692537672629392747930733)
                ·
                  refine ⟨259701627236022280474025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692537672629392747930733 259701627236022280474025)
                  ·
                    rfl

theorem cell20_568988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_568988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568988 prefixEnd_568988 := by exact prefixLift 568988
  have htrace : WordTrace (prefixWord ++ tailWord_568988) baseStart_568988 baseEnd_568988 := by
    simpa [prefixWord, tailWord_568988, baseEnd_568988] using wordTrace_append hprefix tailTrace_568988
  have hstable : (prefixWord ++ tailWord_568988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568988).length < 2 ^ (prefixWord ++ tailWord_568988).sum := by decide
  have hdescent : baseEnd_568988 < baseStart_568988 := by decide
  rcases family_descends (prefixWord ++ tailWord_568988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568992 : List Nat := [2, 1, 1, 4, 3, 1, 3, 2, 3]
def baseStart_568992 : Nat := 118140960795 + 568992 * 2 ^ 59
def prefixEnd_568992 : Nat := 4983230072969 + 3 ^ 40 * 568992 * 2
def baseEnd_568992 : Nat := 259703452945016044340675

theorem tailTrace_568992 : CollatzResearch.WordTrace tailWord_568992 prefixEnd_568992 259703452945016044340675 := by
  unfold tailWord_568992
  simp only [CollatzResearch.WordTrace]
  refine ⟨10376421577323317471062615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13835228769764423294750153 10376421577323317471062615)
  ·
    refine ⟨15564632365984976206593923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10376421577323317471062615 15564632365984976206593923)
    ·
      refine ⟨23346948548977464309890885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15564632365984976206593923 23346948548977464309890885)
      ·
        refine ⟨4377552852933274558104541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23346948548977464309890885 4377552852933274558104541)
        ·
          refine ⟨1641582319849977959289203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4377552852933274558104541 1641582319849977959289203)
          ·
            refine ⟨2462373479774966938933805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1641582319849977959289203 2462373479774966938933805)
            ·
              refine ⟨923390054915612602100177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2462373479774966938933805 923390054915612602100177)
              ·
                refine ⟨692542541186709451575133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923390054915612602100177 692542541186709451575133)
                ·
                  refine ⟨259703452945016044340675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692542541186709451575133 259703452945016044340675)
                  ·
                    rfl

theorem cell20_568992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_568992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_568992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_568992 prefixEnd_568992 := by exact prefixLift 568992
  have htrace : WordTrace (prefixWord ++ tailWord_568992) baseStart_568992 baseEnd_568992 := by
    simpa [prefixWord, tailWord_568992, baseEnd_568992] using wordTrace_append hprefix tailTrace_568992
  have hstable : (prefixWord ++ tailWord_568992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568992).length < 2 ^ (prefixWord ++ tailWord_568992).sum := by decide
  have hdescent : baseEnd_568992 < baseStart_568992 := by decide
  rcases family_descends (prefixWord ++ tailWord_568992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569044 : List Nat := [2, 4, 1, 3, 1, 1, 8]
def baseStart_569044 : Nat := 118140960795 + 569044 * 2 ^ 59
def prefixEnd_569044 : Nat := 4983230072969 + 3 ^ 40 * 569044 * 2
def baseEnd_569044 : Nat := 28858576351326108289681

theorem tailTrace_569044 : CollatzResearch.WordTrace tailWord_569044 prefixEnd_569044 28858576351326108289681 := by
  unfold tailWord_569044
  simp only [CollatzResearch.WordTrace]
  refine ⟨10377369875229123911509093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13836493166972165215345457 10377369875229123911509093)
  ·
    refine ⟨1945756851605460733407955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10377369875229123911509093 1945756851605460733407955)
    ·
      refine ⟨2918635277408191100111933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1945756851605460733407955 2918635277408191100111933)
      ·
        refine ⟨1094488229028071662541975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2918635277408191100111933 1094488229028071662541975)
        ·
          refine ⟨1641732343542107493812963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1094488229028071662541975 1641732343542107493812963)
          ·
            refine ⟨2462598515313161240719445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1641732343542107493812963 2462598515313161240719445)
            ·
              refine ⟨28858576351326108289681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2462598515313161240719445 28858576351326108289681)
              ·
                rfl

theorem cell20_569044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 8].length) (baseStart_569044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569044 prefixEnd_569044 := by exact prefixLift 569044
  have htrace : WordTrace (prefixWord ++ tailWord_569044) baseStart_569044 baseEnd_569044 := by
    simpa [prefixWord, tailWord_569044, baseEnd_569044] using wordTrace_append hprefix tailTrace_569044
  have hstable : (prefixWord ++ tailWord_569044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569044).length < 2 ^ (prefixWord ++ tailWord_569044).sum := by decide
  have hdescent : baseEnd_569044 < baseStart_569044 := by decide
  rcases family_descends (prefixWord ++ tailWord_569044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569068 : List Nat := [2, 2, 1, 1, 2, 2, 6, 1, 3]
def baseStart_569068 : Nat := 118140960795 + 569068 * 2 ^ 59
def prefixEnd_569068 : Nat := 4983230072969 + 3 ^ 40 * 569068 * 2
def baseEnd_569068 : Nat := 259738141415897557807031

theorem tailTrace_569068 : CollatzResearch.WordTrace tailWord_569068 prefixEnd_569068 259738141415897557807031 := by
  unfold tailWord_569068
  simp only [CollatzResearch.WordTrace]
  refine ⟨10377807551185649960945929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13837076734914199947927905 10377807551185649960945929)
  ·
    refine ⟨7783355663389237470709447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10377807551185649960945929 7783355663389237470709447)
    ·
      refine ⟨11675033495083856206064171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7783355663389237470709447 11675033495083856206064171)
      ·
        refine ⟨17512550242625784309096257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11675033495083856206064171 17512550242625784309096257)
        ·
          refine ⟨13134412681969338231822193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17512550242625784309096257 13134412681969338231822193)
          ·
            refine ⟨9850809511477003673866645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13134412681969338231822193 9850809511477003673866645)
            ·
              refine ⟨461756695850484547212499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9850809511477003673866645 461756695850484547212499)
              ·
                refine ⟨692635043775726820818749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461756695850484547212499 692635043775726820818749)
                ·
                  refine ⟨259738141415897557807031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692635043775726820818749 259738141415897557807031)
                  ·
                    rfl

theorem cell20_569068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_569068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569068 prefixEnd_569068 := by exact prefixLift 569068
  have htrace : WordTrace (prefixWord ++ tailWord_569068) baseStart_569068 baseEnd_569068 := by
    simpa [prefixWord, tailWord_569068, baseEnd_569068] using wordTrace_append hprefix tailTrace_569068
  have hstable : (prefixWord ++ tailWord_569068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569068).length < 2 ^ (prefixWord ++ tailWord_569068).sum := by decide
  have hdescent : baseEnd_569068 < baseStart_569068 := by decide
  rcases family_descends (prefixWord ++ tailWord_569068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569072 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 7]
def baseStart_569072 : Nat := 118140960795 + 569072 * 2 ^ 59
def prefixEnd_569072 : Nat := 4983230072969 + 3 ^ 40 * 569072 * 2
def baseEnd_569072 : Nat := 259739967124891321673681

theorem tailTrace_569072 : CollatzResearch.WordTrace tailWord_569072 prefixEnd_569072 259739967124891321673681 := by
  unfold tailWord_569072
  simp only [CollatzResearch.WordTrace]
  refine ⟨10377880497178404302518735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13837173996237872403358313 10377880497178404302518735)
  ·
    refine ⟨15566820745767606453778103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10377880497178404302518735 15566820745767606453778103)
    ·
      refine ⟨23350231118651409680667155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15566820745767606453778103 23350231118651409680667155)
      ·
        refine ⟨35025346677977114521000733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23350231118651409680667155 35025346677977114521000733)
        ·
          refine ⟨13134505004241417945375275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35025346677977114521000733 13134505004241417945375275)
          ·
            refine ⟨19701757506362126918062913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13134505004241417945375275 19701757506362126918062913)
            ·
              refine ⟨14776318129771595188547185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19701757506362126918062913 14776318129771595188547185)
              ·
                refine ⟨11082238597328696391410389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14776318129771595188547185 11082238597328696391410389)
                ·
                  refine ⟨259739967124891321673681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11082238597328696391410389 259739967124891321673681)
                  ·
                    rfl

theorem cell20_569072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_569072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569072 prefixEnd_569072 := by exact prefixLift 569072
  have htrace : WordTrace (prefixWord ++ tailWord_569072) baseStart_569072 baseEnd_569072 := by
    simpa [prefixWord, tailWord_569072, baseEnd_569072] using wordTrace_append hprefix tailTrace_569072
  have hstable : (prefixWord ++ tailWord_569072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569072).length < 2 ^ (prefixWord ++ tailWord_569072).sum := by decide
  have hdescent : baseEnd_569072 < baseStart_569072 := by decide
  rcases family_descends (prefixWord ++ tailWord_569072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569101 : List Nat := [1, 7, 2, 1, 1, 2, 2, 2, 2]
def baseStart_569101 : Nat := 118140960795 + 569101 * 2 ^ 59
def prefixEnd_569101 : Nat := 4983230072969 + 3 ^ 40 * 569101 * 2
def baseEnd_569101 : Nat := 259753203515096109706897

theorem tailTrace_569101 : CollatzResearch.WordTrace tailWord_569101 prefixEnd_569101 259753203515096109706897 := by
  unfold tailWord_569101
  simp only [CollatzResearch.WordTrace]
  refine ⟨20756818711251746557843157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13837879140834497705228771 20756818711251746557843157)
  ·
    refine ⟨486487938544962809949449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 20756818711251746557843157 486487938544962809949449)
    ·
      refine ⟨364865953908722107462087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 486487938544962809949449 364865953908722107462087)
      ·
        refine ⟨547298930863083161193131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364865953908722107462087 547298930863083161193131)
        ·
          refine ⟨820948396294624741789697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547298930863083161193131 820948396294624741789697)
          ·
            refine ⟨615711297220968556342273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 820948396294624741789697 615711297220968556342273)
            ·
              refine ⟨461783472915726417256705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615711297220968556342273 461783472915726417256705)
              ·
                refine ⟨346337604686794812942529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 461783472915726417256705 346337604686794812942529)
                ·
                  refine ⟨259753203515096109706897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346337604686794812942529 259753203515096109706897)
                  ·
                    rfl

theorem cell20_569101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_569101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569101 prefixEnd_569101 := by exact prefixLift 569101
  have htrace : WordTrace (prefixWord ++ tailWord_569101) baseStart_569101 baseEnd_569101 := by
    simpa [prefixWord, tailWord_569101, baseEnd_569101] using wordTrace_append hprefix tailTrace_569101
  have hstable : (prefixWord ++ tailWord_569101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569101).length < 2 ^ (prefixWord ++ tailWord_569101).sum := by decide
  have hdescent : baseEnd_569101 < baseStart_569101 := by decide
  rcases family_descends (prefixWord ++ tailWord_569101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569109 : List Nat := [1, 3, 2, 1, 2, 5, 2, 2, 2]
def baseStart_569109 : Nat := 118140960795 + 569109 * 2 ^ 59
def prefixEnd_569109 : Nat := 4983230072969 + 3 ^ 40 * 569109 * 2
def baseEnd_569109 : Nat := 259756854933083637440197

theorem tailTrace_569109 : CollatzResearch.WordTrace tailWord_569109 prefixEnd_569109 259756854933083637440197 := by
  unfold tailWord_569109
  simp only [CollatzResearch.WordTrace]
  refine ⟨20757110495222763924134381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13838073663481842616089587 20757110495222763924134381)
  ·
    refine ⟨7783916435708536471550393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20757110495222763924134381 7783916435708536471550393)
    ·
      refine ⟨5837937326781402353662795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7783916435708536471550393 5837937326781402353662795)
      ·
        refine ⟨8756905990172103530494193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5837937326781402353662795 8756905990172103530494193)
        ·
          refine ⟨6567679492629077647870645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8756905990172103530494193 6567679492629077647870645)
          ·
            refine ⟨615719952433976029487873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6567679492629077647870645 615719952433976029487873)
            ·
              refine ⟨461789964325482022115905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615719952433976029487873 461789964325482022115905)
              ·
                refine ⟨346342473244111516586929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 461789964325482022115905 346342473244111516586929)
                ·
                  refine ⟨259756854933083637440197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346342473244111516586929 259756854933083637440197)
                  ·
                    rfl

theorem cell20_569109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_569109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569109 prefixEnd_569109 := by exact prefixLift 569109
  have htrace : WordTrace (prefixWord ++ tailWord_569109) baseStart_569109 baseEnd_569109 := by
    simpa [prefixWord, tailWord_569109, baseEnd_569109] using wordTrace_append hprefix tailTrace_569109
  have hstable : (prefixWord ++ tailWord_569109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569109).length < 2 ^ (prefixWord ++ tailWord_569109).sum := by decide
  have hdescent : baseEnd_569109 < baseStart_569109 := by decide
  rcases family_descends (prefixWord ++ tailWord_569109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569196 : List Nat := [2, 2, 1, 1, 4, 2, 4, 4]
def baseStart_569196 : Nat := 118140960795 + 569196 * 2 ^ 59
def prefixEnd_569196 : Nat := 4983230072969 + 3 ^ 40 * 569196 * 2
def baseEnd_569196 : Nat := 86598854701232667179947

theorem tailTrace_569196 : CollatzResearch.WordTrace tailWord_569196 prefixEnd_569196 86598854701232667179947 := by
  unfold tailWord_569196
  simp only [CollatzResearch.WordTrace]
  refine ⟨10380141822953788891275721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13840189097271718521700961 10380141822953788891275721)
  ·
    refine ⟨7785106367215341668456791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10380141822953788891275721 7785106367215341668456791)
    ·
      refine ⟨11677659550823012502685187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7785106367215341668456791 11677659550823012502685187)
      ·
        refine ⟨17516489326234518754027781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11677659550823012502685187 17516489326234518754027781)
        ·
          refine ⟨3284341748668972266380209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17516489326234518754027781 3284341748668972266380209)
          ·
            refine ⟨2463256311501729199785157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3284341748668972266380209 2463256311501729199785157)
            ·
              refine ⟨461860558406574224959717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2463256311501729199785157 461860558406574224959717)
              ·
                refine ⟨86598854701232667179947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 461860558406574224959717 86598854701232667179947)
                ·
                  rfl

theorem cell20_569196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_569196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569196 prefixEnd_569196 := by exact prefixLift 569196
  have htrace : WordTrace (prefixWord ++ tailWord_569196) baseStart_569196 baseEnd_569196 := by
    simpa [prefixWord, tailWord_569196, baseEnd_569196] using wordTrace_append hprefix tailTrace_569196
  have hstable : (prefixWord ++ tailWord_569196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569196).length < 2 ^ (prefixWord ++ tailWord_569196).sum := by decide
  have hdescent : baseEnd_569196 < baseStart_569196 := by decide
  rcases family_descends (prefixWord ++ tailWord_569196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569223 : List Nat := [1, 1, 4, 2, 4, 1, 3, 2, 2]
def baseStart_569223 : Nat := 118140960795 + 569223 * 2 ^ 59
def prefixEnd_569223 : Nat := 4983230072969 + 3 ^ 40 * 569223 * 2
def baseEnd_569223 : Nat := 259808887639405907639731

theorem tailTrace_569223 : CollatzResearch.WordTrace tailWord_569223 prefixEnd_569223 259808887639405907639731 := by
  unfold tailWord_569223
  simp only [CollatzResearch.WordTrace]
  refine ⟨20761268416809761393784323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13840845611206507595856215 20761268416809761393784323)
  ·
    refine ⟨31141902625214642090676485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20761268416809761393784323 31141902625214642090676485)
    ·
      refine ⟨5839106742227745392001841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31141902625214642090676485 5839106742227745392001841)
      ·
        refine ⟨4379330056670809044001381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5839106742227745392001841 4379330056670809044001381)
        ·
          refine ⟨821124385625776695750259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4379330056670809044001381 821124385625776695750259)
          ·
            refine ⟨1231686578438665043625389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821124385625776695750259 1231686578438665043625389)
            ·
              refine ⟨461882466914499391359521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1231686578438665043625389 461882466914499391359521)
              ·
                refine ⟨346411850185874543519641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 461882466914499391359521 346411850185874543519641)
                ·
                  refine ⟨259808887639405907639731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346411850185874543519641 259808887639405907639731)
                  ·
                    rfl

theorem cell20_569223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 2].length) (baseStart_569223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569223 prefixEnd_569223 := by exact prefixLift 569223
  have htrace : WordTrace (prefixWord ++ tailWord_569223) baseStart_569223 baseEnd_569223 := by
    simpa [prefixWord, tailWord_569223, baseEnd_569223] using wordTrace_append hprefix tailTrace_569223
  have hstable : (prefixWord ++ tailWord_569223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569223).length < 2 ^ (prefixWord ++ tailWord_569223).sum := by decide
  have hdescent : baseEnd_569223 < baseStart_569223 := by decide
  rcases family_descends (prefixWord ++ tailWord_569223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569234 : List Nat := [3, 2, 3, 2, 1, 1, 1, 7]
def baseStart_569234 : Nat := 118140960795 + 569234 * 2 ^ 59
def prefixEnd_569234 : Nat := 4983230072969 + 3 ^ 40 * 569234 * 2
def baseEnd_569234 : Nat := 86604636113046252757673

theorem tailTrace_569234 : CollatzResearch.WordTrace tailWord_569234 prefixEnd_569234 86604636113046252757673 := by
  unfold tailWord_569234
  simp only [CollatzResearch.WordTrace]
  refine ⟨5190417404942477568108689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13841113079846606848289837 5190417404942477568108689)
  ·
    refine ⟨3892813053706858176081517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5190417404942477568108689 3892813053706858176081517)
    ·
      refine ⟨1459804895140071816030569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3892813053706858176081517 1459804895140071816030569)
      ·
        refine ⟨1094853671355053862022927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1459804895140071816030569 1094853671355053862022927)
        ·
          refine ⟨1642280507032580793034391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1094853671355053862022927 1642280507032580793034391)
          ·
            refine ⟨2463420760548871189551587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1642280507032580793034391 2463420760548871189551587)
            ·
              refine ⟨3695131140823306784327381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463420760548871189551587 3695131140823306784327381)
              ·
                refine ⟨86604636113046252757673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3695131140823306784327381 86604636113046252757673)
                ·
                  rfl

theorem cell20_569234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_569234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569234 prefixEnd_569234 := by exact prefixLift 569234
  have htrace : WordTrace (prefixWord ++ tailWord_569234) baseStart_569234 baseEnd_569234 := by
    simpa [prefixWord, tailWord_569234, baseEnd_569234] using wordTrace_append hprefix tailTrace_569234
  have hstable : (prefixWord ++ tailWord_569234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569234).length < 2 ^ (prefixWord ++ tailWord_569234).sum := by decide
  have hdescent : baseEnd_569234 < baseStart_569234 := by decide
  rcases family_descends (prefixWord ++ tailWord_569234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569279 : List Nat := [1, 1, 2, 2, 2, 1, 6, 2, 3]
def baseStart_569279 : Nat := 118140960795 + 569279 * 2 ^ 59
def prefixEnd_569279 : Nat := 4983230072969 + 3 ^ 40 * 569279 * 2
def baseEnd_569279 : Nat := 259834447565318601772835

theorem tailTrace_569279 : CollatzResearch.WordTrace tailWord_569279 prefixEnd_569279 259834447565318601772835 := by
  unfold tailWord_569279
  simp only [CollatzResearch.WordTrace]
  refine ⟨20763310904606882957822891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13842207269737921971881927 20763310904606882957822891)
  ·
    refine ⟨31144966356910324436734337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20763310904606882957822891 31144966356910324436734337)
    ·
      refine ⟨23358724767682743327550753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31144966356910324436734337 23358724767682743327550753)
      ·
        refine ⟨17519043575762057495663065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23358724767682743327550753 17519043575762057495663065)
        ·
          refine ⟨13139282681821543121747299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17519043575762057495663065 13139282681821543121747299)
          ·
            refine ⟨19708924022732314682620949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13139282681821543121747299 19708924022732314682620949)
            ·
              refine ⟨923855813565577250747857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19708924022732314682620949 923855813565577250747857)
              ·
                refine ⟨692891860174182938060893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923855813565577250747857 692891860174182938060893)
                ·
                  refine ⟨259834447565318601772835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692891860174182938060893 259834447565318601772835)
                  ·
                    rfl

theorem cell20_569279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 3].length) (baseStart_569279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569279 prefixEnd_569279 := by exact prefixLift 569279
  have htrace : WordTrace (prefixWord ++ tailWord_569279) baseStart_569279 baseEnd_569279 := by
    simpa [prefixWord, tailWord_569279, baseEnd_569279] using wordTrace_append hprefix tailTrace_569279
  have hstable : (prefixWord ++ tailWord_569279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569279).length < 2 ^ (prefixWord ++ tailWord_569279).sum := by decide
  have hdescent : baseEnd_569279 < baseStart_569279 := by decide
  rcases family_descends (prefixWord ++ tailWord_569279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569334 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_569334 : Nat := 118140960795 + 569334 * 2 ^ 59
def prefixEnd_569334 : Nat := 4983230072969 + 3 ^ 40 * 569334 * 2
def baseEnd_569334 : Nat := 259859551063982854939277

theorem tailTrace_569334 : CollatzResearch.WordTrace tailWord_569334 prefixEnd_569334 259859551063982854939277 := by
  unfold tailWord_569334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1297832307462976709442191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13843544612938418234050037 1297832307462976709442191)
  ·
    refine ⟨1946748461194465064163287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1297832307462976709442191 1946748461194465064163287)
    ·
      refine ⟨2920122691791697596244931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1946748461194465064163287 2920122691791697596244931)
      ·
        refine ⟨4380184037687546394367397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2920122691791697596244931 4380184037687546394367397)
        ·
          refine ⟨821284507066414948943887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4380184037687546394367397 821284507066414948943887)
          ·
            refine ⟨1231926760599622423415831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821284507066414948943887 1231926760599622423415831)
            ·
              refine ⟨1847890140899433635123747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1231926760599622423415831 1847890140899433635123747)
              ·
                refine ⟨2771835211349150452685621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1847890140899433635123747 2771835211349150452685621)
                ·
                  refine ⟨259859551063982854939277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2771835211349150452685621 259859551063982854939277)
                  ·
                    rfl

theorem cell20_569334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_569334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569334 prefixEnd_569334 := by exact prefixLift 569334
  have htrace : WordTrace (prefixWord ++ tailWord_569334) baseStart_569334 baseEnd_569334 := by
    simpa [prefixWord, tailWord_569334, baseEnd_569334] using wordTrace_append hprefix tailTrace_569334
  have hstable : (prefixWord ++ tailWord_569334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569334).length < 2 ^ (prefixWord ++ tailWord_569334).sum := by decide
  have hdescent : baseEnd_569334 < baseStart_569334 := by decide
  rcases family_descends (prefixWord ++ tailWord_569334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569341 : List Nat := [1, 4, 1, 1, 1, 2, 4, 4, 2]
def baseStart_569341 : Nat := 118140960795 + 569341 * 2 ^ 59
def prefixEnd_569341 : Nat := 4983230072969 + 3 ^ 40 * 569341 * 2
def baseEnd_569341 : Nat := 259862746054721941705915

theorem tailTrace_569341 : CollatzResearch.WordTrace tailWord_569341 prefixEnd_569341 259862746054721941705915 := by
  unfold tailWord_569341
  simp only [CollatzResearch.WordTrace]
  refine ⟨20765572230382267546579877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13843714820254845031053251 20765572230382267546579877)
  ·
    refine ⟨3893544793196675164983727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20765572230382267546579877 3893544793196675164983727)
    ·
      refine ⟨5840317189795012747475591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3893544793196675164983727 5840317189795012747475591)
      ·
        refine ⟨8760475784692519121213387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5840317189795012747475591 8760475784692519121213387)
        ·
          refine ⟨13140713677038778681820081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8760475784692519121213387 13140713677038778681820081)
          ·
            refine ⟨9855535257779084011365061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13140713677038778681820081 9855535257779084011365061)
            ·
              refine ⟨1847912860833578252130949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9855535257779084011365061 1847912860833578252130949)
              ·
                refine ⟨346483661406295922274553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1847912860833578252130949 346483661406295922274553)
                ·
                  refine ⟨259862746054721941705915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346483661406295922274553 259862746054721941705915)
                  ·
                    rfl

theorem cell20_569341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_569341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569341 prefixEnd_569341 := by exact prefixLift 569341
  have htrace : WordTrace (prefixWord ++ tailWord_569341) baseStart_569341 baseEnd_569341 := by
    simpa [prefixWord, tailWord_569341, baseEnd_569341] using wordTrace_append hprefix tailTrace_569341
  have hstable : (prefixWord ++ tailWord_569341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569341).length < 2 ^ (prefixWord ++ tailWord_569341).sum := by decide
  have hdescent : baseEnd_569341 < baseStart_569341 := by decide
  rcases family_descends (prefixWord ++ tailWord_569341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569365 : List Nat := [1, 3, 2, 1, 5, 2, 2, 4]
def baseStart_569365 : Nat := 118140960795 + 569365 * 2 ^ 59
def prefixEnd_569365 : Nat := 4983230072969 + 3 ^ 40 * 569365 * 2
def baseEnd_569365 : Nat := 86624566769561508301939

theorem tailTrace_569365 : CollatzResearch.WordTrace tailWord_569365 prefixEnd_569365 86624566769561508301939 := by
  unfold tailWord_569365
  simp only [CollatzResearch.WordTrace]
  refine ⟨20766447582295319645453549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13844298388196879763635699 20766447582295319645453549)
  ·
    refine ⟨7787417843360744867045081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20766447582295319645453549 7787417843360744867045081)
    ·
      refine ⟨5840563382520558650283811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7787417843360744867045081 5840563382520558650283811)
      ·
        refine ⟨8760845073780837975425717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5840563382520558650283811 8760845073780837975425717)
        ·
          refine ⟨821329225666953560196161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8760845073780837975425717 821329225666953560196161)
          ·
            refine ⟨615996919250215170147121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 821329225666953560196161 615996919250215170147121)
            ·
              refine ⟨461997689437661377610341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615996919250215170147121 461997689437661377610341)
              ·
                refine ⟨86624566769561508301939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 461997689437661377610341 86624566769561508301939)
                ·
                  rfl

theorem cell20_569365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 4].length) (baseStart_569365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569365 prefixEnd_569365 := by exact prefixLift 569365
  have htrace : WordTrace (prefixWord ++ tailWord_569365) baseStart_569365 baseEnd_569365 := by
    simpa [prefixWord, tailWord_569365, baseEnd_569365] using wordTrace_append hprefix tailTrace_569365
  have hstable : (prefixWord ++ tailWord_569365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569365).length < 2 ^ (prefixWord ++ tailWord_569365).sum := by decide
  have hdescent : baseEnd_569365 < baseStart_569365 := by decide
  rcases family_descends (prefixWord ++ tailWord_569365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569386 : List Nat := [3, 1, 4, 1, 2, 3, 6]
def baseStart_569386 : Nat := 118140960795 + 569386 * 2 ^ 59
def prefixEnd_569386 : Nat := 4983230072969 + 3 ^ 40 * 569386 * 2
def baseEnd_569386 : Nat := 28875920586766865022859

theorem tailTrace_569386 : CollatzResearch.WordTrace tailWord_569386 prefixEnd_569386 28875920586766865022859 := by
  unfold tailWord_569386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5191803378804810057992003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13844809010146160154645341 5191803378804810057992003)
  ·
    refine ⟨7787705068207215086988005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5191803378804810057992003 7787705068207215086988005)
    ·
      refine ⟨1460194700288852828810251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7787705068207215086988005 1460194700288852828810251)
      ·
        refine ⟨2190292050433279243215377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1460194700288852828810251 2190292050433279243215377)
        ·
          refine ⟨1642719037824959432411533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2190292050433279243215377 1642719037824959432411533)
          ·
            refine ⟨616019639184359787154325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1642719037824959432411533 616019639184359787154325)
            ·
              refine ⟨28875920586766865022859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 616019639184359787154325 28875920586766865022859)
              ·
                rfl

theorem cell20_569386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 6].length) (baseStart_569386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569386 prefixEnd_569386 := by exact prefixLift 569386
  have htrace : WordTrace (prefixWord ++ tailWord_569386) baseStart_569386 baseEnd_569386 := by
    simpa [prefixWord, tailWord_569386, baseEnd_569386] using wordTrace_append hprefix tailTrace_569386
  have hstable : (prefixWord ++ tailWord_569386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569386).length < 2 ^ (prefixWord ++ tailWord_569386).sum := by decide
  have hdescent : baseEnd_569386 < baseStart_569386 := by decide
  rcases family_descends (prefixWord ++ tailWord_569386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569406 : List Nat := [4, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_569406 : Nat := 118140960795 + 569406 * 2 ^ 59
def prefixEnd_569406 : Nat := 4983230072969 + 3 ^ 40 * 569406 * 2
def baseEnd_569406 : Nat := 259892413825870604538983

theorem tailTrace_569406 : CollatzResearch.WordTrace tailWord_569406 prefixEnd_569406 259892413825870604538983 := by
  unfold tailWord_569406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2595992871893347955962009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13845295316764522431797381 2595992871893347955962009)
  ·
    refine ⟨1946994653920010966971507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2595992871893347955962009 1946994653920010966971507)
    ·
      refine ⟨2920491980880016450457261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1946994653920010966971507 2920491980880016450457261)
      ·
        refine ⟨1095184492830006168921473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2920491980880016450457261 1095184492830006168921473)
        ·
          refine ⟨821388369622504626691105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1095184492830006168921473 821388369622504626691105)
          ·
            refine ⟨616041277216878470018329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 821388369622504626691105 616041277216878470018329)
            ·
              refine ⟨462030957912658852513747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 616041277216878470018329 462030957912658852513747)
              ·
                refine ⟨693046436868988278770621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462030957912658852513747 693046436868988278770621)
                ·
                  refine ⟨259892413825870604538983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 693046436868988278770621 259892413825870604538983)
                  ·
                    rfl

theorem cell20_569406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_569406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569406 prefixEnd_569406 := by exact prefixLift 569406
  have htrace : WordTrace (prefixWord ++ tailWord_569406) baseStart_569406 baseEnd_569406 := by
    simpa [prefixWord, tailWord_569406, baseEnd_569406] using wordTrace_append hprefix tailTrace_569406
  have hstable : (prefixWord ++ tailWord_569406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569406).length < 2 ^ (prefixWord ++ tailWord_569406).sum := by decide
  have hdescent : baseEnd_569406 < baseStart_569406 := by decide
  rcases family_descends (prefixWord ++ tailWord_569406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569455 : List Nat := [1, 1, 2, 1, 3, 5, 1, 4, 2]
def baseStart_569455 : Nat := 118140960795 + 569455 * 2 ^ 59
def prefixEnd_569455 : Nat := 4983230072969 + 3 ^ 40 * 569455 * 2
def baseEnd_569455 : Nat := 259914778761044211905449

theorem tailTrace_569455 : CollatzResearch.WordTrace tailWord_569455 prefixEnd_569455 259914778761044211905449 := by
  unfold tailWord_569455
  simp only [CollatzResearch.WordTrace]
  refine ⟨20769730151969265016229819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13846486767979510010819879 20769730151969265016229819)
  ·
    refine ⟨31154595227953897524344729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20769730151969265016229819 31154595227953897524344729)
    ·
      refine ⟨23365946420965423143258547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31154595227953897524344729 23365946420965423143258547)
      ·
        refine ⟨35048919631448134714887821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23365946420965423143258547 35048919631448134714887821)
        ·
          refine ⟨13143344861793050518082933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35048919631448134714887821 13143344861793050518082933)
          ·
            refine ⟨1232188580793098486070275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13143344861793050518082933 1232188580793098486070275)
            ·
              refine ⟨1848282871189647729105413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1232188580793098486070275 1848282871189647729105413)
              ·
                refine ⟨346553038348058949207265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1848282871189647729105413 346553038348058949207265)
                ·
                  refine ⟨259914778761044211905449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346553038348058949207265 259914778761044211905449)
                  ·
                    rfl

theorem cell20_569455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 2].length) (baseStart_569455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569455 prefixEnd_569455 := by exact prefixLift 569455
  have htrace : WordTrace (prefixWord ++ tailWord_569455) baseStart_569455 baseEnd_569455 := by
    simpa [prefixWord, tailWord_569455, baseEnd_569455] using wordTrace_append hprefix tailTrace_569455
  have hstable : (prefixWord ++ tailWord_569455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569455).length < 2 ^ (prefixWord ++ tailWord_569455).sum := by decide
  have hdescent : baseEnd_569455 < baseStart_569455 := by decide
  rcases family_descends (prefixWord ++ tailWord_569455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569462 : List Nat := [5, 1, 1, 2, 1, 2, 3, 5]
def baseStart_569462 : Nat := 118140960795 + 569462 * 2 ^ 59
def prefixEnd_569462 : Nat := 4983230072969 + 3 ^ 40 * 569462 * 2
def baseEnd_569462 : Nat := 86639324583927766224029

theorem tailTrace_569462 : CollatzResearch.WordTrace tailWord_569462 prefixEnd_569462 86639324583927766224029 := by
  unfold tailWord_569462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1298124091433994075733415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13846656975295936807823093 1298124091433994075733415)
  ·
    refine ⟨1947186137150991113600123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1298124091433994075733415 1947186137150991113600123)
    ·
      refine ⟨2920779205726486670400185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1947186137150991113600123 2920779205726486670400185)
      ·
        refine ⟨2190584404294865002800139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2920779205726486670400185 2190584404294865002800139)
        ·
          refine ⟨3285876606442297504200209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190584404294865002800139 3285876606442297504200209)
          ·
            refine ⟨2464407454831723128150157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3285876606442297504200209 2464407454831723128150157)
            ·
              refine ⟨924152795561896173056309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2464407454831723128150157 924152795561896173056309)
              ·
                refine ⟨86639324583927766224029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 924152795561896173056309 86639324583927766224029)
                ·
                  rfl

theorem cell20_569462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_569462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569462 prefixEnd_569462 := by exact prefixLift 569462
  have htrace : WordTrace (prefixWord ++ tailWord_569462) baseStart_569462 baseEnd_569462 := by
    simpa [prefixWord, tailWord_569462, baseEnd_569462] using wordTrace_append hprefix tailTrace_569462
  have hstable : (prefixWord ++ tailWord_569462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569462).length < 2 ^ (prefixWord ++ tailWord_569462).sum := by decide
  have hdescent : baseEnd_569462 < baseStart_569462 := by decide
  rcases family_descends (prefixWord ++ tailWord_569462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569469 : List Nat := [1, 4, 1, 1, 3, 2, 2, 3, 3]
def baseStart_569469 : Nat := 118140960795 + 569469 * 2 ^ 59
def prefixEnd_569469 : Nat := 4983230072969 + 3 ^ 40 * 569469 * 2
def baseEnd_569469 : Nat := 259921168742522385438725

theorem tailTrace_569469 : CollatzResearch.WordTrace tailWord_569469 prefixEnd_569469 259921168742522385438725 := by
  unfold tailWord_569469
  simp only [CollatzResearch.WordTrace]
  refine ⟨20770240773918545407239461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13846827182612363604826307 20770240773918545407239461)
  ·
    refine ⟨3894420145109727263857399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20770240773918545407239461 3894420145109727263857399)
    ·
      refine ⟨5841630217664590895786099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3894420145109727263857399 5841630217664590895786099)
      ·
        refine ⟨8762445326496886343679149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5841630217664590895786099 8762445326496886343679149)
        ·
          refine ⟨3285916997436332378879681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8762445326496886343679149 3285916997436332378879681)
          ·
            refine ⟨2464437748077249284159761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3285916997436332378879681 2464437748077249284159761)
            ·
              refine ⟨1848328311057936963119821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2464437748077249284159761 1848328311057936963119821)
              ·
                refine ⟨693123116646726361169933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1848328311057936963119821 693123116646726361169933)
                ·
                  refine ⟨259921168742522385438725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 693123116646726361169933 259921168742522385438725)
                  ·
                    rfl

theorem cell20_569469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_569469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569469 prefixEnd_569469 := by exact prefixLift 569469
  have htrace : WordTrace (prefixWord ++ tailWord_569469) baseStart_569469 baseEnd_569469 := by
    simpa [prefixWord, tailWord_569469, baseEnd_569469] using wordTrace_append hprefix tailTrace_569469
  have hstable : (prefixWord ++ tailWord_569469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569469).length < 2 ^ (prefixWord ++ tailWord_569469).sum := by decide
  have hdescent : baseEnd_569469 < baseStart_569469 := by decide
  rcases family_descends (prefixWord ++ tailWord_569469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569476 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 4]
def baseStart_569476 : Nat := 118140960795 + 569476 * 2 ^ 59
def prefixEnd_569476 : Nat := 4983230072969 + 3 ^ 40 * 569476 * 2
def baseEnd_569476 : Nat := 259924363733261472205363

theorem tailTrace_569476 : CollatzResearch.WordTrace tailWord_569476 prefixEnd_569476 259924363733261472205363 := by
  unfold tailWord_569476
  simp only [CollatzResearch.WordTrace]
  refine ⟨10385248042446592801372141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13846997389928790401829521 10385248042446592801372141)
  ·
    refine ⟨3894468015917472300514553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10385248042446592801372141 3894468015917472300514553)
    ·
      refine ⟨2920851011938104225385915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3894468015917472300514553 2920851011938104225385915)
      ·
        refine ⟨4381276517907156338078873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2920851011938104225385915 4381276517907156338078873)
        ·
          refine ⟨3285957388430367253559155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4381276517907156338078873 3285957388430367253559155)
          ·
            refine ⟨4928936082645550880338733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3285957388430367253559155 4928936082645550880338733)
            ·
              refine ⟨1848351030992081580127025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4928936082645550880338733 1848351030992081580127025)
              ·
                refine ⟨1386263273244061185095269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1848351030992081580127025 1386263273244061185095269)
                ·
                  refine ⟨259924363733261472205363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1386263273244061185095269 259924363733261472205363)
                  ·
                    rfl

theorem cell20_569476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_569476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569476 prefixEnd_569476 := by exact prefixLift 569476
  have htrace : WordTrace (prefixWord ++ tailWord_569476) baseStart_569476 baseEnd_569476 := by
    simpa [prefixWord, tailWord_569476, baseEnd_569476] using wordTrace_append hprefix tailTrace_569476
  have hstable : (prefixWord ++ tailWord_569476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569476).length < 2 ^ (prefixWord ++ tailWord_569476).sum := by decide
  have hdescent : baseEnd_569476 < baseStart_569476 := by decide
  rcases family_descends (prefixWord ++ tailWord_569476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569493 : List Nat := [1, 3, 2, 1, 1, 1, 6, 3, 2]
def baseStart_569493 : Nat := 118140960795 + 569493 * 2 ^ 59
def prefixEnd_569493 : Nat := 4983230072969 + 3 ^ 40 * 569493 * 2
def baseEnd_569493 : Nat := 259932122996484968638627

theorem tailTrace_569493 : CollatzResearch.WordTrace tailWord_569493 prefixEnd_569493 259932122996484968638627 := by
  unfold tailWord_569493
  simp only [CollatzResearch.WordTrace]
  refine ⟨20771116125831597506113133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13847410750554398337408755 20771116125831597506113133)
  ·
    refine ⟨7789168547186849064792425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20771116125831597506113133 7789168547186849064792425)
    ·
      refine ⟨5841876410390136798594319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7789168547186849064792425 5841876410390136798594319)
      ·
        refine ⟨8762814615585205197891479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5841876410390136798594319 8762814615585205197891479)
        ·
          refine ⟨13144221923377807796837219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8762814615585205197891479 13144221923377807796837219)
          ·
            refine ⟨19716332885066711695255829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13144221923377807796837219 19716332885066711695255829)
            ·
              refine ⟨924203103987502110715117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19716332885066711695255829 924203103987502110715117)
              ·
                refine ⟨346576163995313291518169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 924203103987502110715117 346576163995313291518169)
                ·
                  refine ⟨259932122996484968638627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346576163995313291518169 259932122996484968638627)
                  ·
                    rfl

theorem cell20_569493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_569493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569493 prefixEnd_569493 := by exact prefixLift 569493
  have htrace : WordTrace (prefixWord ++ tailWord_569493) baseStart_569493 baseEnd_569493 := by
    simpa [prefixWord, tailWord_569493, baseEnd_569493] using wordTrace_append hprefix tailTrace_569493
  have hstable : (prefixWord ++ tailWord_569493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569493).length < 2 ^ (prefixWord ++ tailWord_569493).sum := by decide
  have hdescent : baseEnd_569493 < baseStart_569493 := by decide
  rcases family_descends (prefixWord ++ tailWord_569493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569534 : List Nat := [4, 2, 1, 1, 5, 1, 2, 4]
def baseStart_569534 : Nat := 118140960795 + 569534 * 2 ^ 59
def prefixEnd_569534 : Nat := 4983230072969 + 3 ^ 40 * 569534 * 2
def baseEnd_569534 : Nat := 86650278837890349423931

theorem tailTrace_569534 : CollatzResearch.WordTrace tailWord_569534 prefixEnd_569534 86650278837890349423931 := by
  unfold tailWord_569534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2596576439835382688544457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13848407679122041005570437 2596576439835382688544457)
  ·
    refine ⟨1947432329876537016408343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2596576439835382688544457 1947432329876537016408343)
    ·
      refine ⟨2921148494814805524612515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1947432329876537016408343 2921148494814805524612515)
      ·
        refine ⟨4381722742222208286918773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921148494814805524612515 4381722742222208286918773)
        ·
          refine ⟨410786507083332026898635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4381722742222208286918773 410786507083332026898635)
          ·
            refine ⟨616179760624998040347953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410786507083332026898635 616179760624998040347953)
            ·
              refine ⟨462134820468748530260965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 616179760624998040347953 462134820468748530260965)
              ·
                refine ⟨86650278837890349423931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 462134820468748530260965 86650278837890349423931)
                ·
                  rfl

theorem cell20_569534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_569534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569534 prefixEnd_569534 := by exact prefixLift 569534
  have htrace : WordTrace (prefixWord ++ tailWord_569534) baseStart_569534 baseEnd_569534 := by
    simpa [prefixWord, tailWord_569534, baseEnd_569534] using wordTrace_append hprefix tailTrace_569534
  have hstable : (prefixWord ++ tailWord_569534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569534).length < 2 ^ (prefixWord ++ tailWord_569534).sum := by decide
  have hdescent : baseEnd_569534 < baseStart_569534 := by decide
  rcases family_descends (prefixWord ++ tailWord_569534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569565 : List Nat := [1, 4, 3, 2, 1, 2, 3, 2, 2]
def baseStart_569565 : Nat := 118140960795 + 569565 * 2 ^ 59
def prefixEnd_569565 : Nat := 4983230072969 + 3 ^ 40 * 569565 * 2
def baseEnd_569565 : Nat := 259964985758372718238333

theorem tailTrace_569565 : CollatzResearch.WordTrace tailWord_569565 prefixEnd_569565 259964985758372718238333 := by
  unfold tailWord_569565
  simp only [CollatzResearch.WordTrace]
  refine ⟨20773742181570753802734149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13849161454380502535156099 20773742181570753802734149)
  ·
    refine ⟨3895076659044516338012653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20773742181570753802734149 3895076659044516338012653)
    ·
      refine ⟨1460653747141693626754745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3895076659044516338012653 1460653747141693626754745)
      ·
        refine ⟨1095490310356270220066059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1460653747141693626754745 1095490310356270220066059)
        ·
          refine ⟨1643235465534405330099089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1095490310356270220066059 1643235465534405330099089)
          ·
            refine ⟨1232426599150803997574317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1643235465534405330099089 1232426599150803997574317)
            ·
              refine ⟨462159974681551499090369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1232426599150803997574317 462159974681551499090369)
              ·
                refine ⟨346619981011163624317777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462159974681551499090369 346619981011163624317777)
                ·
                  refine ⟨259964985758372718238333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346619981011163624317777 259964985758372718238333)
                  ·
                    rfl

theorem cell20_569565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_569565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569565 prefixEnd_569565 := by exact prefixLift 569565
  have htrace : WordTrace (prefixWord ++ tailWord_569565) baseStart_569565 baseEnd_569565 := by
    simpa [prefixWord, tailWord_569565, baseEnd_569565] using wordTrace_append hprefix tailTrace_569565
  have hstable : (prefixWord ++ tailWord_569565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569565).length < 2 ^ (prefixWord ++ tailWord_569565).sum := by decide
  have hdescent : baseEnd_569565 < baseStart_569565 := by decide
  rcases family_descends (prefixWord ++ tailWord_569565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569583 : List Nat := [1, 1, 2, 1, 6, 2, 1, 3, 3]
def baseStart_569583 : Nat := 118140960795 + 569583 * 2 ^ 59
def prefixEnd_569583 : Nat := 4983230072969 + 3 ^ 40 * 569583 * 2
def baseEnd_569583 : Nat := 259973201448844655638259

theorem tailTrace_569583 : CollatzResearch.WordTrace tailWord_569583 prefixEnd_569583 259973201448844655638259 := by
  unfold tailWord_569583
  simp only [CollatzResearch.WordTrace]
  refine ⟨20774398695505542876889403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13849599130337028584592935 20774398695505542876889403)
  ·
    refine ⟨31161598043258314315334105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20774398695505542876889403 31161598043258314315334105)
    ·
      refine ⟨23371198532443735736500579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31161598043258314315334105 23371198532443735736500579)
      ·
        refine ⟨35056797798665603604750869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23371198532443735736500579 35056797798665603604750869)
        ·
          refine ⟨1643287396812450168972697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35056797798665603604750869 1643287396812450168972697)
          ·
            refine ⟨1232465547609337626729523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1643287396812450168972697 1232465547609337626729523)
            ·
              refine ⟨1848698321414006440094285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1232465547609337626729523 1848698321414006440094285)
              ·
                refine ⟨693261870530252415035357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1848698321414006440094285 693261870530252415035357)
                ·
                  refine ⟨259973201448844655638259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 693261870530252415035357 259973201448844655638259)
                  ·
                    rfl

theorem cell20_569583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 3].length) (baseStart_569583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569583 prefixEnd_569583 := by exact prefixLift 569583
  have htrace : WordTrace (prefixWord ++ tailWord_569583) baseStart_569583 baseEnd_569583 := by
    simpa [prefixWord, tailWord_569583, baseEnd_569583] using wordTrace_append hprefix tailTrace_569583
  have hstable : (prefixWord ++ tailWord_569583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569583).length < 2 ^ (prefixWord ++ tailWord_569583).sum := by decide
  have hdescent : baseEnd_569583 < baseStart_569583 := by decide
  rcases family_descends (prefixWord ++ tailWord_569583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569590 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_569590 : Nat := 118140960795 + 569590 * 2 ^ 59
def prefixEnd_569590 : Nat := 4983230072969 + 3 ^ 40 * 569590 * 2
def baseEnd_569590 : Nat := 259976396439583742404897

theorem tailTrace_569590 : CollatzResearch.WordTrace tailWord_569590 prefixEnd_569590 259976396439583742404897 := by
  unfold tailWord_569590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1298415875405011442024639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13849769337653455381596149 1298415875405011442024639)
  ·
    refine ⟨1947623813107517163036959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1298415875405011442024639 1947623813107517163036959)
    ·
      refine ⟨2921435719661275744555439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1947623813107517163036959 2921435719661275744555439)
      ·
        refine ⟨4382153579491913616833159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921435719661275744555439 4382153579491913616833159)
        ·
          refine ⟨6573230369237870425249739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4382153579491913616833159 6573230369237870425249739)
          ·
            refine ⟨9859845553856805637874609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6573230369237870425249739 9859845553856805637874609)
            ·
              refine ⟨7394884165392604228405957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9859845553856805637874609 7394884165392604228405957)
              ·
                refine ⟨1386540781011113292826117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7394884165392604228405957 1386540781011113292826117)
                ·
                  refine ⟨259976396439583742404897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1386540781011113292826117 259976396439583742404897)
                  ·
                    rfl

theorem cell20_569590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_569590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569590 prefixEnd_569590 := by exact prefixLift 569590
  have htrace : WordTrace (prefixWord ++ tailWord_569590) baseStart_569590 baseEnd_569590 := by
    simpa [prefixWord, tailWord_569590, baseEnd_569590] using wordTrace_append hprefix tailTrace_569590
  have hstable : (prefixWord ++ tailWord_569590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569590).length < 2 ^ (prefixWord ++ tailWord_569590).sum := by decide
  have hdescent : baseEnd_569590 < baseStart_569590 := by decide
  rcases family_descends (prefixWord ++ tailWord_569590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569656 : List Nat := [2, 1, 2, 1, 3, 1, 2, 8]
def baseStart_569656 : Nat := 118140960795 + 569656 * 2 ^ 59
def prefixEnd_569656 : Nat := 4983230072969 + 3 ^ 40 * 569656 * 2
def baseEnd_569656 : Nat := 86668840212660282068209

theorem tailTrace_569656 : CollatzResearch.WordTrace tailWord_569656 prefixEnd_569656 86668840212660282068209 := by
  unfold tailWord_569656
  simp only [CollatzResearch.WordTrace]
  refine ⟨10388530612120538172148411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13851374149494050896197881 10388530612120538172148411)
  ·
    refine ⟨15582795918180807258222617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10388530612120538172148411 15582795918180807258222617)
    ·
      refine ⟨11687096938635605443666963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15582795918180807258222617 11687096938635605443666963)
      ·
        refine ⟨17530645407953408165500445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11687096938635605443666963 17530645407953408165500445)
        ·
          refine ⟨6573992027982528062062667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17530645407953408165500445 6573992027982528062062667)
          ·
            refine ⟨9860988041973792093094001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6573992027982528062062667 9860988041973792093094001)
            ·
              refine ⟨7395741031480344069820501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9860988041973792093094001 7395741031480344069820501)
              ·
                refine ⟨86668840212660282068209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7395741031480344069820501 86668840212660282068209)
                ·
                  rfl

theorem cell20_569656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_569656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569656 prefixEnd_569656 := by exact prefixLift 569656
  have htrace : WordTrace (prefixWord ++ tailWord_569656) baseStart_569656 baseEnd_569656 := by
    simpa [prefixWord, tailWord_569656, baseEnd_569656] using wordTrace_append hprefix tailTrace_569656
  have hstable : (prefixWord ++ tailWord_569656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569656).length < 2 ^ (prefixWord ++ tailWord_569656).sum := by decide
  have hdescent : baseEnd_569656 < baseStart_569656 := by decide
  rcases family_descends (prefixWord ++ tailWord_569656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569662 : List Nat := [4, 2, 1, 2, 1, 3, 2, 3, 2]
def baseStart_569662 : Nat := 118140960795 + 569662 * 2 ^ 59
def prefixEnd_569662 : Nat := 4983230072969 + 3 ^ 40 * 569662 * 2
def baseEnd_569662 : Nat := 260009259201471492004603

theorem tailTrace_569662 : CollatzResearch.WordTrace tailWord_569662 prefixEnd_569662 260009259201471492004603 := by
  unfold tailWord_569662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2597160007777417421126905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13851520041479559579343493 2597160007777417421126905)
  ·
    refine ⟨1947870005833063065845179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2597160007777417421126905 1947870005833063065845179)
    ·
      refine ⟨2921805008749594598767769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1947870005833063065845179 2921805008749594598767769)
      ·
        refine ⟨2191353756562195949075827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2921805008749594598767769 2191353756562195949075827)
        ·
          refine ⟨3287030634843293923613741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2191353756562195949075827 3287030634843293923613741)
          ·
            refine ⟨1232636488066235221355153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3287030634843293923613741 1232636488066235221355153)
            ·
              refine ⟨924477366049676416016365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1232636488066235221355153 924477366049676416016365)
              ·
                refine ⟨346679012268628656006137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 924477366049676416016365 346679012268628656006137)
                ·
                  refine ⟨260009259201471492004603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346679012268628656006137 260009259201471492004603)
                  ·
                    rfl

theorem cell20_569662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_569662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569662 prefixEnd_569662 := by exact prefixLift 569662
  have htrace : WordTrace (prefixWord ++ tailWord_569662) baseStart_569662 baseEnd_569662 := by
    simpa [prefixWord, tailWord_569662, baseEnd_569662] using wordTrace_append hprefix tailTrace_569662
  have hstable : (prefixWord ++ tailWord_569662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569662).length < 2 ^ (prefixWord ++ tailWord_569662).sum := by decide
  have hdescent : baseEnd_569662 < baseStart_569662 := by decide
  rcases family_descends (prefixWord ++ tailWord_569662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569680 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 5]
def baseStart_569680 : Nat := 118140960795 + 569680 * 2 ^ 59
def prefixEnd_569680 : Nat := 4983230072969 + 3 ^ 40 * 569680 * 2
def baseEnd_569680 : Nat := 260017474891943429404529

theorem tailTrace_569680 : CollatzResearch.WordTrace tailWord_569680 prefixEnd_569680 260017474891943429404529 := by
  unfold tailWord_569680
  simp only [CollatzResearch.WordTrace]
  refine ⟨10388968288077064221585247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13851957717436085628780329 10388968288077064221585247)
  ·
    refine ⟨15583452432115596332377871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10388968288077064221585247 15583452432115596332377871)
    ·
      refine ⟨23375178648173394498566807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15583452432115596332377871 23375178648173394498566807)
      ·
        refine ⟨35062767972260091747850211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23375178648173394498566807 35062767972260091747850211)
        ·
          refine ⟨52594151958390137621775317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35062767972260091747850211 52594151958390137621775317)
          ·
            refine ⟨1232675436524768850510359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 52594151958390137621775317 1232675436524768850510359)
            ·
              refine ⟨1849013154787153275765539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1232675436524768850510359 1849013154787153275765539)
              ·
                refine ⟨2773519732180729913648309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1849013154787153275765539 2773519732180729913648309)
                ·
                  refine ⟨260017474891943429404529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2773519732180729913648309 260017474891943429404529)
                  ·
                    rfl

theorem cell20_569680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_569680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569680 prefixEnd_569680 := by exact prefixLift 569680
  have htrace : WordTrace (prefixWord ++ tailWord_569680) baseStart_569680 baseEnd_569680 := by
    simpa [prefixWord, tailWord_569680, baseEnd_569680] using wordTrace_append hprefix tailTrace_569680
  have hstable : (prefixWord ++ tailWord_569680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569680).length < 2 ^ (prefixWord ++ tailWord_569680).sum := by decide
  have hdescent : baseEnd_569680 < baseStart_569680 := by decide
  rcases family_descends (prefixWord ++ tailWord_569680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569704 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 4]
def baseStart_569704 : Nat := 118140960795 + 569704 * 2 ^ 59
def prefixEnd_569704 : Nat := 4983230072969 + 3 ^ 40 * 569704 * 2
def baseEnd_569704 : Nat := 260028429145906012604431

theorem tailTrace_569704 : CollatzResearch.WordTrace tailWord_569704 prefixEnd_569704 260028429145906012604431 := by
  unfold tailWord_569704
  simp only [CollatzResearch.WordTrace]
  refine ⟨10389405964033590271022083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13852541285378120361362777 10389405964033590271022083)
  ·
    refine ⟨15584108946050385406533125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10389405964033590271022083 15584108946050385406533125)
    ·
      refine ⟨2922020427384447263724961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15584108946050385406533125 2922020427384447263724961)
      ·
        refine ⟨2191515320538335447793721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2922020427384447263724961 2191515320538335447793721)
        ·
          refine ⟨1643636490403751585845291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2191515320538335447793721 1643636490403751585845291)
          ·
            refine ⟨2465454735605627378767937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1643636490403751585845291 2465454735605627378767937)
            ·
              refine ⟨1849091051704220534075953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2465454735605627378767937 1849091051704220534075953)
              ·
                refine ⟨1386818288778165400556965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1849091051704220534075953 1386818288778165400556965)
                ·
                  refine ⟨260028429145906012604431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1386818288778165400556965 260028429145906012604431)
                  ·
                    rfl

theorem cell20_569704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_569704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569704 prefixEnd_569704 := by exact prefixLift 569704
  have htrace : WordTrace (prefixWord ++ tailWord_569704) baseStart_569704 baseEnd_569704 := by
    simpa [prefixWord, tailWord_569704, baseEnd_569704] using wordTrace_append hprefix tailTrace_569704
  have hstable : (prefixWord ++ tailWord_569704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569704).length < 2 ^ (prefixWord ++ tailWord_569704).sum := by decide
  have hdescent : baseEnd_569704 < baseStart_569704 := by decide
  rcases family_descends (prefixWord ++ tailWord_569704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569738 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 4]
def baseStart_569738 : Nat := 118140960795 + 569738 * 2 ^ 59
def prefixEnd_569738 : Nat := 4983230072969 + 3 ^ 40 * 569738 * 2
def baseEnd_569738 : Nat := 260043947672353005470959

theorem tailTrace_569738 : CollatzResearch.WordTrace tailWord_569738 prefixEnd_569738 260043947672353005470959 := by
  unfold tailWord_569738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5195013002486001087195467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13853368006629336232521245 5195013002486001087195467)
  ·
    refine ⟨7792519503729001630793201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5195013002486001087195467 7792519503729001630793201)
    ·
      refine ⟨5844389627796751223094901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7792519503729001630793201 5844389627796751223094901)
      ·
        refine ⟨547911527605945427165147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5844389627796751223094901 547911527605945427165147)
        ·
          refine ⟨821867291408918140747721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547911527605945427165147 821867291408918140747721)
          ·
            refine ⟨616400468556688605560791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 821867291408918140747721 616400468556688605560791)
            ·
              refine ⟨924600702835032908341187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616400468556688605560791 924600702835032908341187)
              ·
                refine ⟨1386901054252549362511781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924600702835032908341187 1386901054252549362511781)
                ·
                  refine ⟨260043947672353005470959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1386901054252549362511781 260043947672353005470959)
                  ·
                    rfl

theorem cell20_569738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_569738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569738 prefixEnd_569738 := by exact prefixLift 569738
  have htrace : WordTrace (prefixWord ++ tailWord_569738) baseStart_569738 baseEnd_569738 := by
    simpa [prefixWord, tailWord_569738, baseEnd_569738] using wordTrace_append hprefix tailTrace_569738
  have hstable : (prefixWord ++ tailWord_569738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569738).length < 2 ^ (prefixWord ++ tailWord_569738).sum := by decide
  have hdescent : baseEnd_569738 < baseStart_569738 := by decide
  rcases family_descends (prefixWord ++ tailWord_569738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569748 : List Nat := [2, 4, 2, 1, 4, 1, 2, 1, 3]
def baseStart_569748 : Nat := 118140960795 + 569748 * 2 ^ 59
def prefixEnd_569748 : Nat := 4983230072969 + 3 ^ 40 * 569748 * 2
def baseEnd_569748 : Nat := 260048511944837415137585

theorem tailTrace_569748 : CollatzResearch.WordTrace tailWord_569748 prefixEnd_569748 260048511944837415137585 := by
  unfold tailWord_569748
  simp only [CollatzResearch.WordTrace]
  refine ⟨10390208369953888028322949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13853611159938517371097265 10390208369953888028322949)
  ·
    refine ⟨1948164069366354005310553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10390208369953888028322949 1948164069366354005310553)
    ·
      refine ⟨1461123052024765503982915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1948164069366354005310553 1461123052024765503982915)
      ·
        refine ⟨2191684578037148255974373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1461123052024765503982915 2191684578037148255974373)
        ·
          refine ⟨410940858381965297995195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2191684578037148255974373 410940858381965297995195)
          ·
            refine ⟨616411287572947946992793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410940858381965297995195 616411287572947946992793)
            ·
              refine ⟨462308465679710960244595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 616411287572947946992793 462308465679710960244595)
              ·
                refine ⟨693462698519566440366893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462308465679710960244595 693462698519566440366893)
                ·
                  refine ⟨260048511944837415137585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 693462698519566440366893 260048511944837415137585)
                  ·
                    rfl

theorem cell20_569748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_569748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569748 prefixEnd_569748 := by exact prefixLift 569748
  have htrace : WordTrace (prefixWord ++ tailWord_569748) baseStart_569748 baseEnd_569748 := by
    simpa [prefixWord, tailWord_569748, baseEnd_569748] using wordTrace_append hprefix tailTrace_569748
  have hstable : (prefixWord ++ tailWord_569748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569748).length < 2 ^ (prefixWord ++ tailWord_569748).sum := by decide
  have hdescent : baseEnd_569748 < baseStart_569748 := by decide
  rcases family_descends (prefixWord ++ tailWord_569748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569752 : List Nat := [2, 1, 2, 5, 1, 1, 4, 1, 3]
def baseStart_569752 : Nat := 118140960795 + 569752 * 2 ^ 59
def prefixEnd_569752 : Nat := 4983230072969 + 3 ^ 40 * 569752 * 2
def baseEnd_569752 : Nat := 260050337653831179004235

theorem tailTrace_569752 : CollatzResearch.WordTrace tailWord_569752 prefixEnd_569752 260050337653831179004235 := by
  unfold tailWord_569752
  simp only [CollatzResearch.WordTrace]
  refine ⟨10390281315946642369895755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13853708421262189826527673 10390281315946642369895755)
  ·
    refine ⟨15585421973919963554843633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10390281315946642369895755 15585421973919963554843633)
    ·
      refine ⟨11689066480439972666132725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15585421973919963554843633 11689066480439972666132725)
      ·
        refine ⟨1095849982541247437449943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11689066480439972666132725 1095849982541247437449943)
        ·
          refine ⟨1643774973811871156174915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1095849982541247437449943 1643774973811871156174915)
          ·
            refine ⟨2465662460717806734262373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1643774973811871156174915 2465662460717806734262373)
            ·
              refine ⟨462311711384588762674195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2465662460717806734262373 462311711384588762674195)
              ·
                refine ⟨693467567076883144011293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462311711384588762674195 693467567076883144011293)
                ·
                  refine ⟨260050337653831179004235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 693467567076883144011293 260050337653831179004235)
                  ·
                    rfl

theorem cell20_569752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_569752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569752 prefixEnd_569752 := by exact prefixLift 569752
  have htrace : WordTrace (prefixWord ++ tailWord_569752) baseStart_569752 baseEnd_569752 := by
    simpa [prefixWord, tailWord_569752, baseEnd_569752] using wordTrace_append hprefix tailTrace_569752
  have hstable : (prefixWord ++ tailWord_569752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569752).length < 2 ^ (prefixWord ++ tailWord_569752).sum := by decide
  have hdescent : baseEnd_569752 < baseStart_569752 := by decide
  rcases family_descends (prefixWord ++ tailWord_569752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569804 : List Nat := [2, 2, 1, 4, 3, 2, 1, 5]
def baseStart_569804 : Nat := 118140960795 + 569804 * 2 ^ 59
def prefixEnd_569804 : Nat := 4983230072969 + 3 ^ 40 * 569804 * 2
def baseEnd_569804 : Nat := 86691357290250036423563

theorem tailTrace_569804 : CollatzResearch.WordTrace tailWord_569804 prefixEnd_569804 86691357290250036423563 := by
  unfold tailWord_569804
  simp only [CollatzResearch.WordTrace]
  refine ⟨10391229613852448810342233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13854972818469931747122977 10391229613852448810342233)
  ·
    refine ⟨7793422210389336607756675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10391229613852448810342233 7793422210389336607756675)
    ·
      refine ⟨11690133315584004911635013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7793422210389336607756675 11690133315584004911635013)
      ·
        refine ⟨2191899996672000920931565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11690133315584004911635013 2191899996672000920931565)
        ·
          refine ⟨821962498752000345349337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2191899996672000920931565 821962498752000345349337)
          ·
            refine ⟨616471874064000259012003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 821962498752000345349337 616471874064000259012003)
            ·
              refine ⟨924707811096000388518005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616471874064000259012003 924707811096000388518005)
              ·
                refine ⟨86691357290250036423563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 924707811096000388518005 86691357290250036423563)
                ·
                  rfl

theorem cell20_569804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_569804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569804 prefixEnd_569804 := by exact prefixLift 569804
  have htrace : WordTrace (prefixWord ++ tailWord_569804) baseStart_569804 baseEnd_569804 := by
    simpa [prefixWord, tailWord_569804, baseEnd_569804] using wordTrace_append hprefix tailTrace_569804
  have hstable : (prefixWord ++ tailWord_569804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569804).length < 2 ^ (prefixWord ++ tailWord_569804).sum := by decide
  have hdescent : baseEnd_569804 < baseStart_569804 := by decide
  rcases family_descends (prefixWord ++ tailWord_569804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569815 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 9]
def baseStart_569815 : Nat := 118140960795 + 569815 * 2 ^ 59
def prefixEnd_569815 : Nat := 4983230072969 + 3 ^ 40 * 569815 * 2
def baseEnd_569815 : Nat := 260079092570482959903977

theorem tailTrace_569815 : CollatzResearch.WordTrace tailWord_569815 prefixEnd_569815 260079092570482959903977 := by
  unfold tailWord_569815
  simp only [CollatzResearch.WordTrace]
  refine ⟨20782860430665046499334899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13855240287110030999556599 20782860430665046499334899)
  ·
    refine ⟨31174290645997569749002349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20782860430665046499334899 31174290645997569749002349)
    ·
      refine ⟨11690358992249088655875881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31174290645997569749002349 11690358992249088655875881)
      ·
        refine ⟨8767769244186816491906911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11690358992249088655875881 8767769244186816491906911)
        ·
          refine ⟨13151653866280224737860367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8767769244186816491906911 13151653866280224737860367)
          ·
            refine ⟨19727480799420337106790551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13151653866280224737860367 19727480799420337106790551)
            ·
              refine ⟨29591221199130505660185827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19727480799420337106790551 29591221199130505660185827)
              ·
                refine ⟨44386831798695758490278741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29591221199130505660185827 44386831798695758490278741)
                ·
                  refine ⟨260079092570482959903977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44386831798695758490278741 260079092570482959903977)
                  ·
                    rfl

theorem cell20_569815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_569815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569815 prefixEnd_569815 := by exact prefixLift 569815
  have htrace : WordTrace (prefixWord ++ tailWord_569815) baseStart_569815 baseEnd_569815 := by
    simpa [prefixWord, tailWord_569815, baseEnd_569815] using wordTrace_append hprefix tailTrace_569815
  have hstable : (prefixWord ++ tailWord_569815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569815).length < 2 ^ (prefixWord ++ tailWord_569815).sum := by decide
  have hdescent : baseEnd_569815 < baseStart_569815 := by decide
  rcases family_descends (prefixWord ++ tailWord_569815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569825 : List Nat := [1, 2, 3, 1, 2, 2, 5, 4]
def baseStart_569825 : Nat := 118140960795 + 569825 * 2 ^ 59
def prefixEnd_569825 : Nat := 4983230072969 + 3 ^ 40 * 569825 * 2
def baseEnd_569825 : Nat := 86694552280989123190201

theorem tailTrace_569825 : CollatzResearch.WordTrace tailWord_569825 prefixEnd_569825 86694552280989123190201 := by
  unfold tailWord_569825
  simp only [CollatzResearch.WordTrace]
  refine ⟨20783225160628818207198929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13855483440419212138132619 20783225160628818207198929)
  ·
    refine ⟨15587418870471613655399197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20783225160628818207198929 15587418870471613655399197)
    ·
      refine ⟨5845282076426855120774699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15587418870471613655399197 5845282076426855120774699)
      ·
        refine ⟨8767923114640282681162049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5845282076426855120774699 8767923114640282681162049)
        ·
          refine ⟨6575942335980212010871537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8767923114640282681162049 6575942335980212010871537)
          ·
            refine ⟨4931956751985159008153653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6575942335980212010871537 4931956751985159008153653)
            ·
              refine ⟨462370945498608657014405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4931956751985159008153653 462370945498608657014405)
              ·
                refine ⟨86694552280989123190201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 462370945498608657014405 86694552280989123190201)
                ·
                  rfl

theorem cell20_569825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 4].length) (baseStart_569825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569825 prefixEnd_569825 := by exact prefixLift 569825
  have htrace : WordTrace (prefixWord ++ tailWord_569825) baseStart_569825 baseEnd_569825 := by
    simpa [prefixWord, tailWord_569825, baseEnd_569825] using wordTrace_append hprefix tailTrace_569825
  have hstable : (prefixWord ++ tailWord_569825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569825).length < 2 ^ (prefixWord ++ tailWord_569825).sum := by decide
  have hdescent : baseEnd_569825 < baseStart_569825 := by decide
  rcases family_descends (prefixWord ++ tailWord_569825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569845 : List Nat := [1, 3, 5, 1, 2, 2, 1, 2, 3]
def baseStart_569845 : Nat := 118140960795 + 569845 * 2 ^ 59
def prefixEnd_569845 : Nat := 4983230072969 + 3 ^ 40 * 569845 * 2
def baseEnd_569845 : Nat := 260092785387936188903855

theorem tailTrace_569845 : CollatzResearch.WordTrace tailWord_569845 prefixEnd_569845 260092785387936188903855 := by
  unfold tailWord_569845
  simp only [CollatzResearch.WordTrace]
  refine ⟨20783954620556361622926989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13855969747037574415284659 20783954620556361622926989)
  ·
    refine ⟨7793982982708635608597621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20783954620556361622926989 7793982982708635608597621)
    ·
      refine ⟨730685904628934588306027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7793982982708635608597621 730685904628934588306027)
      ·
        refine ⟨1096028856943401882459041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 730685904628934588306027 1096028856943401882459041)
        ·
          refine ⟨822021642707551411844281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1096028856943401882459041 822021642707551411844281)
          ·
            refine ⟨616516232030663558883211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 822021642707551411844281 616516232030663558883211)
            ·
              refine ⟨924774348045995338324817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616516232030663558883211 924774348045995338324817)
              ·
                refine ⟨693580761034496503743613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 924774348045995338324817 693580761034496503743613)
                ·
                  refine ⟨260092785387936188903855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 693580761034496503743613 260092785387936188903855)
                  ·
                    rfl

theorem cell20_569845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_569845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569845 prefixEnd_569845 := by exact prefixLift 569845
  have htrace : WordTrace (prefixWord ++ tailWord_569845) baseStart_569845 baseEnd_569845 := by
    simpa [prefixWord, tailWord_569845, baseEnd_569845] using wordTrace_append hprefix tailTrace_569845
  have hstable : (prefixWord ++ tailWord_569845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569845).length < 2 ^ (prefixWord ++ tailWord_569845).sum := by decide
  have hdescent : baseEnd_569845 < baseStart_569845 := by decide
  rcases family_descends (prefixWord ++ tailWord_569845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569877 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 4]
def baseStart_569877 : Nat := 118140960795 + 569877 * 2 ^ 59
def prefixEnd_569877 : Nat := 4983230072969 + 3 ^ 40 * 569877 * 2
def baseEnd_569877 : Nat := 260107391059886299837057

theorem tailTrace_569877 : CollatzResearch.WordTrace tailWord_569877 prefixEnd_569877 260107391059886299837057 := by
  unfold tailWord_569877
  simp only [CollatzResearch.WordTrace]
  refine ⟨20785121756440431088091885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13856747837626954058727923 20785121756440431088091885)
  ·
    refine ⟨7794420658665161658034457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20785121756440431088091885 7794420658665161658034457)
    ·
      refine ⟨5845815493998871243525843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7794420658665161658034457 5845815493998871243525843)
      ·
        refine ⟨8768723240998306865288765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5845815493998871243525843 8768723240998306865288765)
        ·
          refine ⟨3288271215374365074483287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8768723240998306865288765 3288271215374365074483287)
          ·
            refine ⟨4932406823061547611724931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3288271215374365074483287 4932406823061547611724931)
            ·
              refine ⟨7398610234592321417587397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4932406823061547611724931 7398610234592321417587397)
              ·
                refine ⟨1387239418986060265797637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7398610234592321417587397 1387239418986060265797637)
                ·
                  refine ⟨260107391059886299837057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1387239418986060265797637 260107391059886299837057)
                  ·
                    rfl

theorem cell20_569877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_569877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569877 prefixEnd_569877 := by exact prefixLift 569877
  have htrace : WordTrace (prefixWord ++ tailWord_569877) baseStart_569877 baseEnd_569877 := by
    simpa [prefixWord, tailWord_569877, baseEnd_569877] using wordTrace_append hprefix tailTrace_569877
  have hstable : (prefixWord ++ tailWord_569877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569877).length < 2 ^ (prefixWord ++ tailWord_569877).sum := by decide
  have hdescent : baseEnd_569877 < baseStart_569877 := by decide
  rcases family_descends (prefixWord ++ tailWord_569877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569880 : List Nat := [2, 1, 2, 3, 3, 3, 2, 4]
def baseStart_569880 : Nat := 118140960795 + 569880 * 2 ^ 59
def prefixEnd_569880 : Nat := 4983230072969 + 3 ^ 40 * 569880 * 2
def baseEnd_569880 : Nat := 86702920113877207579015

theorem tailTrace_569880 : CollatzResearch.WordTrace tailWord_569880 prefixEnd_569880 86702920113877207579015 := by
  unfold tailWord_569880
  simp only [CollatzResearch.WordTrace]
  refine ⟨10392615587714781300225547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13856820783619708400300729 10392615587714781300225547)
  ·
    refine ⟨15588923381572171950338321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10392615587714781300225547 15588923381572171950338321)
    ·
      refine ⟨11691692536179128962753741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15588923381572171950338321 11691692536179128962753741)
      ·
        refine ⟨4384384701067173361032653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11691692536179128962753741 4384384701067173361032653)
        ·
          refine ⟨1644144262900190010387245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4384384701067173361032653 1644144262900190010387245)
          ·
            refine ⟨616554098587571253895217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1644144262900190010387245 616554098587571253895217)
            ·
              refine ⟨462415573940678440421413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 616554098587571253895217 462415573940678440421413)
              ·
                refine ⟨86702920113877207579015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 462415573940678440421413 86702920113877207579015)
                ·
                  rfl

theorem cell20_569880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_569880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569880 prefixEnd_569880 := by exact prefixLift 569880
  have htrace : WordTrace (prefixWord ++ tailWord_569880) baseStart_569880 baseEnd_569880 := by
    simpa [prefixWord, tailWord_569880, baseEnd_569880] using wordTrace_append hprefix tailTrace_569880
  have hstable : (prefixWord ++ tailWord_569880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569880).length < 2 ^ (prefixWord ++ tailWord_569880).sum := by decide
  have hdescent : baseEnd_569880 < baseStart_569880 := by decide
  rcases family_descends (prefixWord ++ tailWord_569880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569911 : List Nat := [1, 1, 3, 1, 2, 3, 5, 2, 2]
def baseStart_569911 : Nat := 118140960795 + 569911 * 2 ^ 59
def prefixEnd_569911 : Nat := 4983230072969 + 3 ^ 40 * 569911 * 2
def baseEnd_569911 : Nat := 260122909586333292703585

theorem tailTrace_569911 : CollatzResearch.WordTrace tailWord_569911 prefixEnd_569911 260122909586333292703585 := by
  unfold tailWord_569911
  simp only [CollatzResearch.WordTrace]
  refine ⟨20786361838317254894829587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13857574558878169929886391 20786361838317254894829587)
  ·
    refine ⟨31179542757475882342244381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20786361838317254894829587 31179542757475882342244381)
    ·
      refine ⟨11692328534053455878341643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31179542757475882342244381 11692328534053455878341643)
      ·
        refine ⟨17538492801080183817512465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11692328534053455878341643 17538492801080183817512465)
        ·
          refine ⟨13153869600810137863134349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17538492801080183817512465 13153869600810137863134349)
          ·
            refine ⟨4932701100303801698675381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13153869600810137863134349 4932701100303801698675381)
            ·
              refine ⟨462440728153481409250817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4932701100303801698675381 462440728153481409250817)
              ·
                refine ⟨346830546115111056938113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462440728153481409250817 346830546115111056938113)
                ·
                  refine ⟨260122909586333292703585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346830546115111056938113 260122909586333292703585)
                  ·
                    rfl

theorem cell20_569911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 2].length) (baseStart_569911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569911 prefixEnd_569911 := by exact prefixLift 569911
  have htrace : WordTrace (prefixWord ++ tailWord_569911) baseStart_569911 baseEnd_569911 := by
    simpa [prefixWord, tailWord_569911, baseEnd_569911] using wordTrace_append hprefix tailTrace_569911
  have hstable : (prefixWord ++ tailWord_569911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569911).length < 2 ^ (prefixWord ++ tailWord_569911).sum := by decide
  have hdescent : baseEnd_569911 < baseStart_569911 := by decide
  rcases family_descends (prefixWord ++ tailWord_569911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569925 : List Nat := [1, 3, 1, 1, 1, 5, 4, 1, 3]
def baseStart_569925 : Nat := 118140960795 + 569925 * 2 ^ 59
def prefixEnd_569925 : Nat := 4983230072969 + 3 ^ 40 * 569925 * 2
def baseEnd_569925 : Nat := 260129299567811466236861

theorem tailTrace_569925 : CollatzResearch.WordTrace tailWord_569925 prefixEnd_569925 260129299567811466236861 := by
  unfold tailWord_569925
  simp only [CollatzResearch.WordTrace]
  refine ⟨20786872460266535285839229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13857914973511023523892819 20786872460266535285839229)
  ·
    refine ⟨7795077172599950732189711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20786872460266535285839229 7795077172599950732189711)
    ·
      refine ⟨11692615758899926098284567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7795077172599950732189711 11692615758899926098284567)
      ·
        refine ⟨17538923638349889147426851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11692615758899926098284567 17538923638349889147426851)
        ·
          refine ⟨26308385457524833721140277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17538923638349889147426851 26308385457524833721140277)
          ·
            refine ⟨2466411136642953161356901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26308385457524833721140277 2466411136642953161356901)
            ·
              refine ⟨462452088120553717754419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2466411136642953161356901 462452088120553717754419)
              ·
                refine ⟨693678132180830576631629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462452088120553717754419 693678132180830576631629)
                ·
                  refine ⟨260129299567811466236861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 693678132180830576631629 260129299567811466236861)
                  ·
                    rfl

theorem cell20_569925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_569925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569925 prefixEnd_569925 := by exact prefixLift 569925
  have htrace : WordTrace (prefixWord ++ tailWord_569925) baseStart_569925 baseEnd_569925 := by
    simpa [prefixWord, tailWord_569925, baseEnd_569925] using wordTrace_append hprefix tailTrace_569925
  have hstable : (prefixWord ++ tailWord_569925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569925).length < 2 ^ (prefixWord ++ tailWord_569925).sum := by decide
  have hdescent : baseEnd_569925 < baseStart_569925 := by decide
  rcases family_descends (prefixWord ++ tailWord_569925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569960 : List Nat := [2, 1, 4, 3, 10]
def baseStart_569960 : Nat := 118140960795 + 569960 * 2 ^ 59
def prefixEnd_569960 : Nat := 4983230072969 + 3 ^ 40 * 569960 * 2
def baseEnd_569960 : Nat := 3211670055821072840371

theorem tailTrace_569960 : CollatzResearch.WordTrace tailWord_569960 prefixEnd_569960 3211670055821072840371 := by
  unfold tailWord_569960
  simp only [CollatzResearch.WordTrace]
  refine ⟨10394074507569868131681667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13858766010093157508908889 10394074507569868131681667)
  ·
    refine ⟨15591111761354802197522501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10394074507569868131681667 15591111761354802197522501)
    ·
      refine ⟨2923333455254025412035469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15591111761354802197522501 2923333455254025412035469)
      ·
        refine ⟨1096250045720259529513301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2923333455254025412035469 1096250045720259529513301)
        ·
          refine ⟨3211670055821072840371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1096250045720259529513301 3211670055821072840371)
          ·
            rfl

theorem cell20_569960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 10].length) (baseStart_569960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569960 prefixEnd_569960 := by exact prefixLift 569960
  have htrace : WordTrace (prefixWord ++ tailWord_569960) baseStart_569960 baseEnd_569960 := by
    simpa [prefixWord, tailWord_569960, baseEnd_569960] using wordTrace_append hprefix tailTrace_569960
  have hstable : (prefixWord ++ tailWord_569960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569960).length < 2 ^ (prefixWord ++ tailWord_569960).sum := by decide
  have hdescent : baseEnd_569960 < baseStart_569960 := by decide
  rcases family_descends (prefixWord ++ tailWord_569960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569966 : List Nat := [4, 1, 2, 2, 2, 1, 4, 2, 2]
def baseStart_569966 : Nat := 118140960795 + 569966 * 2 ^ 59
def prefixEnd_569966 : Nat := 4983230072969 + 3 ^ 40 * 569966 * 2
def baseEnd_569966 : Nat := 260148013084997545870027

theorem tailTrace_569966 : CollatzResearch.WordTrace tailWord_569966 prefixEnd_569966 260148013084997545870027 := by
  unfold tailWord_569966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2598545981639749911010219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13858911902078666192054501 2598545981639749911010219)
  ·
    refine ⟨3897818972459624866515329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2598545981639749911010219 3897818972459624866515329)
    ·
      refine ⟨2923364229344718649886497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3897818972459624866515329 2923364229344718649886497)
      ·
        refine ⟨2192523172008538987414873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2923364229344718649886497 2192523172008538987414873)
        ·
          refine ⟨1644392379006404240561155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2192523172008538987414873 1644392379006404240561155)
          ·
            refine ⟨2466588568509606360841733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1644392379006404240561155 2466588568509606360841733)
            ·
              refine ⟨462485356595551192657825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2466588568509606360841733 462485356595551192657825)
              ·
                refine ⟨346864017446663394493369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462485356595551192657825 346864017446663394493369)
                ·
                  refine ⟨260148013084997545870027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346864017446663394493369 260148013084997545870027)
                  ·
                    rfl

theorem cell20_569966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_569966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569966 prefixEnd_569966 := by exact prefixLift 569966
  have htrace : WordTrace (prefixWord ++ tailWord_569966) baseStart_569966 baseEnd_569966 := by
    simpa [prefixWord, tailWord_569966, baseEnd_569966] using wordTrace_append hprefix tailTrace_569966
  have hstable : (prefixWord ++ tailWord_569966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569966).length < 2 ^ (prefixWord ++ tailWord_569966).sum := by decide
  have hdescent : baseEnd_569966 < baseStart_569966 := by decide
  rcases family_descends (prefixWord ++ tailWord_569966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569967 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 5]
def baseStart_569967 : Nat := 118140960795 + 569967 * 2 ^ 59
def prefixEnd_569967 : Nat := 4983230072969 + 3 ^ 40 * 569967 * 2
def baseEnd_569967 : Nat := 260148469512245986836689

theorem tailTrace_569967 : CollatzResearch.WordTrace tailWord_569967 prefixEnd_569967 260148469512245986836689 := by
  unfold tailWord_569967
  simp only [CollatzResearch.WordTrace]
  refine ⟨20788404326114376458868155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13858936217409584305912103 20788404326114376458868155)
  ·
    refine ⟨31182606489171564688302233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20788404326114376458868155 31182606489171564688302233)
    ·
      refine ⟨23386954866878673516226675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31182606489171564688302233 23386954866878673516226675)
      ·
        refine ⟨35080432300318010274340013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23386954866878673516226675 35080432300318010274340013)
        ·
          refine ⟨13155162112619253852877505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35080432300318010274340013 13155162112619253852877505)
          ·
            refine ⟨9866371584464440389658129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13155162112619253852877505 9866371584464440389658129)
            ·
              refine ⟨7399778688348330292243597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9866371584464440389658129 7399778688348330292243597)
              ·
                refine ⟨2774917008130623859591349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7399778688348330292243597 2774917008130623859591349)
                ·
                  refine ⟨260148469512245986836689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2774917008130623859591349 260148469512245986836689)
                  ·
                    rfl

theorem cell20_569967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_569967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569967 prefixEnd_569967 := by exact prefixLift 569967
  have htrace : WordTrace (prefixWord ++ tailWord_569967) baseStart_569967 baseEnd_569967 := by
    simpa [prefixWord, tailWord_569967, baseEnd_569967] using wordTrace_append hprefix tailTrace_569967
  have hstable : (prefixWord ++ tailWord_569967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569967).length < 2 ^ (prefixWord ++ tailWord_569967).sum := by decide
  have hdescent : baseEnd_569967 < baseStart_569967 := by decide
  rcases family_descends (prefixWord ++ tailWord_569967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569973 : List Nat := [1, 3, 4, 2, 3, 1, 1, 5]
def baseStart_569973 : Nat := 118140960795 + 569973 * 2 ^ 59
def prefixEnd_569973 : Nat := 4983230072969 + 3 ^ 40 * 569973 * 2
def baseEnd_569973 : Nat := 86717069358578877545555

theorem tailTrace_569973 : CollatzResearch.WordTrace tailWord_569973 prefixEnd_569973 86717069358578877545555 := by
  unfold tailWord_569973
  simp only [CollatzResearch.WordTrace]
  refine ⟨20788623164092639483586573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13859082109395092989057715 20788623164092639483586573)
  ·
    refine ⟨7795733686534739806344965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20788623164092639483586573 7795733686534739806344965)
    ·
      refine ⟨1461700066225263713689681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7795733686534739806344965 1461700066225263713689681)
      ·
        refine ⟨1096275049668947785267261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1461700066225263713689681 1096275049668947785267261)
        ·
          refine ⟨411103143625855419475223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1096275049668947785267261 411103143625855419475223)
          ·
            refine ⟨616654715438783129212835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411103143625855419475223 616654715438783129212835)
            ·
              refine ⟨924982073158174693819253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616654715438783129212835 924982073158174693819253)
              ·
                refine ⟨86717069358578877545555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 924982073158174693819253 86717069358578877545555)
                ·
                  rfl

theorem cell20_569973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 5].length) (baseStart_569973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569973 prefixEnd_569973 := by exact prefixLift 569973
  have htrace : WordTrace (prefixWord ++ tailWord_569973) baseStart_569973 baseEnd_569973 := by
    simpa [prefixWord, tailWord_569973, baseEnd_569973] using wordTrace_append hprefix tailTrace_569973
  have hstable : (prefixWord ++ tailWord_569973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569973).length < 2 ^ (prefixWord ++ tailWord_569973).sum := by decide
  have hdescent : baseEnd_569973 < baseStart_569973 := by decide
  rcases family_descends (prefixWord ++ tailWord_569973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569977 : List Nat := [1, 2, 1, 3, 3, 4, 1, 5]
def baseStart_569977 : Nat := 118140960795 + 569977 * 2 ^ 59
def prefixEnd_569977 : Nat := 4983230072969 + 3 ^ 40 * 569977 * 2
def baseEnd_569977 : Nat := 86717677928243465501105

theorem tailTrace_569977 : CollatzResearch.WordTrace tailWord_569977 prefixEnd_569977 86717677928243465501105 := by
  unfold tailWord_569977
  simp only [CollatzResearch.WordTrace]
  refine ⟨20788769056078148166732185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13859179370718765444488123 20788769056078148166732185)
  ·
    refine ⟨15591576792058611125049139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20788769056078148166732185 15591576792058611125049139)
    ·
      refine ⟨23387365188087916687573709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15591576792058611125049139 23387365188087916687573709)
      ·
        refine ⟨8770261945532968757840141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23387365188087916687573709 8770261945532968757840141)
        ·
          refine ⟨3288848229574863284190053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8770261945532968757840141 3288848229574863284190053)
          ·
            refine ⟨616659043045286865785635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3288848229574863284190053 616659043045286865785635)
            ·
              refine ⟨924988564567930298678453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616659043045286865785635 924988564567930298678453)
              ·
                refine ⟨86717677928243465501105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 924988564567930298678453 86717677928243465501105)
                ·
                  rfl

theorem cell20_569977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 5].length) (baseStart_569977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569977 prefixEnd_569977 := by exact prefixLift 569977
  have htrace : WordTrace (prefixWord ++ tailWord_569977) baseStart_569977 baseEnd_569977 := by
    simpa [prefixWord, tailWord_569977, baseEnd_569977] using wordTrace_append hprefix tailTrace_569977
  have hstable : (prefixWord ++ tailWord_569977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569977).length < 2 ^ (prefixWord ++ tailWord_569977).sum := by decide
  have hdescent : baseEnd_569977 < baseStart_569977 := by decide
  rcases family_descends (prefixWord ++ tailWord_569977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569984 : List Nat := [2, 1, 1, 2, 1, 5, 2, 3, 3]
def baseStart_569984 : Nat := 118140960795 + 569984 * 2 ^ 59
def prefixEnd_569984 : Nat := 4983230072969 + 3 ^ 40 * 569984 * 2
def baseEnd_569984 : Nat := 260156228775469483269953

theorem tailTrace_569984 : CollatzResearch.WordTrace tailWord_569984 prefixEnd_569984 260156228775469483269953 := by
  unfold tailWord_569984
  simp only [CollatzResearch.WordTrace]
  refine ⟨10394512183526394181118503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13859349578035192241491337 10394512183526394181118503)
  ·
    refine ⟨15591768275289591271677755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10394512183526394181118503 15591768275289591271677755)
    ·
      refine ⟨23387652412934386907516633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15591768275289591271677755 23387652412934386907516633)
      ·
        refine ⟨17540739309700790180637475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23387652412934386907516633 17540739309700790180637475)
        ·
          refine ⟨26311108964551185270956213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17540739309700790180637475 26311108964551185270956213)
          ·
            refine ⟨2466666465426673619152145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26311108964551185270956213 2466666465426673619152145)
            ·
              refine ⟨1849999849070005214364109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2466666465426673619152145 1849999849070005214364109)
              ·
                refine ⟨693749943401251955386541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1849999849070005214364109 693749943401251955386541)
                ·
                  refine ⟨260156228775469483269953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 693749943401251955386541 260156228775469483269953)
                  ·
                    rfl

theorem cell20_569984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_569984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569984 prefixEnd_569984 := by exact prefixLift 569984
  have htrace : WordTrace (prefixWord ++ tailWord_569984) baseStart_569984 baseEnd_569984 := by
    simpa [prefixWord, tailWord_569984, baseEnd_569984] using wordTrace_append hprefix tailTrace_569984
  have hstable : (prefixWord ++ tailWord_569984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569984).length < 2 ^ (prefixWord ++ tailWord_569984).sum := by decide
  have hdescent : baseEnd_569984 < baseStart_569984 := by decide
  rcases family_descends (prefixWord ++ tailWord_569984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569991 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 4]
def baseStart_569991 : Nat := 118140960795 + 569991 * 2 ^ 59
def prefixEnd_569991 : Nat := 4983230072969 + 3 ^ 40 * 569991 * 2
def baseEnd_569991 : Nat := 260159423766208570036591

theorem tailTrace_569991 : CollatzResearch.WordTrace tailWord_569991 prefixEnd_569991 260159423766208570036591 := by
  unfold tailWord_569991
  simp only [CollatzResearch.WordTrace]
  refine ⟨20789279678027428557741827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13859519785351619038494551 20789279678027428557741827)
  ·
    refine ⟨31183919517041142836612741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20789279678027428557741827 31183919517041142836612741)
    ·
      refine ⟨5846984909445214281864889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31183919517041142836612741 5846984909445214281864889)
      ·
        refine ⟨4385238682083910711398667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5846984909445214281864889 4385238682083910711398667)
        ·
          refine ⟨6577858023125866067098001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4385238682083910711398667 6577858023125866067098001)
          ·
            refine ⟨4933393517344399550323501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6577858023125866067098001 4933393517344399550323501)
            ·
              refine ⟨1850022569004149831371313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4933393517344399550323501 1850022569004149831371313)
              ·
                refine ⟨1387516926753112373528485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1850022569004149831371313 1387516926753112373528485)
                ·
                  refine ⟨260159423766208570036591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1387516926753112373528485 260159423766208570036591)
                  ·
                    rfl

theorem cell20_569991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_569991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569991 prefixEnd_569991 := by exact prefixLift 569991
  have htrace : WordTrace (prefixWord ++ tailWord_569991) baseStart_569991 baseEnd_569991 := by
    simpa [prefixWord, tailWord_569991, baseEnd_569991] using wordTrace_append hprefix tailTrace_569991
  have hstable : (prefixWord ++ tailWord_569991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569991).length < 2 ^ (prefixWord ++ tailWord_569991).sum := by decide
  have hdescent : baseEnd_569991 < baseStart_569991 := by decide
  rcases family_descends (prefixWord ++ tailWord_569991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569994 : List Nat := [3, 1, 2, 3, 3, 1, 3, 4]
def baseStart_569994 : Nat := 118140960795 + 569994 * 2 ^ 59
def prefixEnd_569994 : Nat := 4983230072969 + 3 ^ 40 * 569994 * 2
def baseEnd_569994 : Nat := 86720264349317964312193

theorem tailTrace_569994 : CollatzResearch.WordTrace tailWord_569994 prefixEnd_569994 86720264349317964312193 := by
  unfold tailWord_569994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5197347274254140017525259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13859592731344373380067357 5197347274254140017525259)
  ·
    refine ⟨7796020911381210026287889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5197347274254140017525259 7796020911381210026287889)
    ·
      refine ⟨5847015683535907519715917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7796020911381210026287889 5847015683535907519715917)
      ·
        refine ⟨2192630881325965319893469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5847015683535907519715917 2192630881325965319893469)
        ·
          refine ⟨822236580497236994960051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2192630881325965319893469 822236580497236994960051)
          ·
            refine ⟨1233354870745855492440077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 822236580497236994960051 1233354870745855492440077)
            ·
              refine ⟨462508076529695809665029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1233354870745855492440077 462508076529695809665029)
              ·
                refine ⟨86720264349317964312193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 462508076529695809665029 86720264349317964312193)
                ·
                  rfl

theorem cell20_569994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_569994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_569994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_569994 prefixEnd_569994 := by exact prefixLift 569994
  have htrace : WordTrace (prefixWord ++ tailWord_569994) baseStart_569994 baseEnd_569994 := by
    simpa [prefixWord, tailWord_569994, baseEnd_569994] using wordTrace_append hprefix tailTrace_569994
  have hstable : (prefixWord ++ tailWord_569994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569994).length < 2 ^ (prefixWord ++ tailWord_569994).sum := by decide
  have hdescent : baseEnd_569994 < baseStart_569994 := by decide
  rcases family_descends (prefixWord ++ tailWord_569994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570004 : List Nat := [2, 4, 2, 2, 1, 2, 2, 3, 2]
def baseStart_570004 : Nat := 118140960795 + 570004 * 2 ^ 59
def prefixEnd_570004 : Nat := 4983230072969 + 3 ^ 40 * 570004 * 2
def baseEnd_570004 : Nat := 260165357320438302603205

theorem tailTrace_570004 : CollatzResearch.WordTrace tailWord_570004 prefixEnd_570004 260165357320438302603205 := by
  unfold tailWord_570004
  simp only [CollatzResearch.WordTrace]
  refine ⟨10394876913490165888982533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13859835884653554518643377 10394876913490165888982533)
  ·
    refine ⟨1949039421279406104184225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10394876913490165888982533 1949039421279406104184225)
    ·
      refine ⟨1461779565959554578138169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1949039421279406104184225 1461779565959554578138169)
      ·
        refine ⟨1096334674469665933603627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1461779565959554578138169 1096334674469665933603627)
        ·
          refine ⟨1644502011704498900405441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096334674469665933603627 1644502011704498900405441)
          ·
            refine ⟨1233376508778374175304081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1644502011704498900405441 1233376508778374175304081)
            ·
              refine ⟨925032381583780631478061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1233376508778374175304081 925032381583780631478061)
              ·
                refine ⟨346887143093917736804273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 925032381583780631478061 346887143093917736804273)
                ·
                  refine ⟨260165357320438302603205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346887143093917736804273 260165357320438302603205)
                  ·
                    rfl

theorem cell20_570004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_570004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570004 prefixEnd_570004 := by exact prefixLift 570004
  have htrace : WordTrace (prefixWord ++ tailWord_570004) baseStart_570004 baseEnd_570004 := by
    simpa [prefixWord, tailWord_570004, baseEnd_570004] using wordTrace_append hprefix tailTrace_570004
  have hstable : (prefixWord ++ tailWord_570004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570004).length < 2 ^ (prefixWord ++ tailWord_570004).sum := by decide
  have hdescent : baseEnd_570004 < baseStart_570004 := by decide
  rcases family_descends (prefixWord ++ tailWord_570004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570060 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 5]
def baseStart_570060 : Nat := 118140960795 + 570060 * 2 ^ 59
def prefixEnd_570060 : Nat := 4983230072969 + 3 ^ 40 * 570060 * 2
def baseEnd_570060 : Nat := 260190917246350996736309

theorem tailTrace_570060 : CollatzResearch.WordTrace tailWord_570060 prefixEnd_570060 260190917246350996736309 := by
  unfold tailWord_570060
  simp only [CollatzResearch.WordTrace]
  refine ⟨10395898157388726671001817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13861197543184968894669089 10395898157388726671001817)
  ·
    refine ⟨7796923618041545003251363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10395898157388726671001817 7796923618041545003251363)
    ·
      refine ⟨11695385427062317504877045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7796923618041545003251363 11695385427062317504877045)
      ·
        refine ⟨1096442383787092266082223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11695385427062317504877045 1096442383787092266082223)
        ·
          refine ⟨1644663575680638399123335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096442383787092266082223 1644663575680638399123335)
          ·
            refine ⟨2466995363520957598685003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1644663575680638399123335 2466995363520957598685003)
            ·
              refine ⟨3700493045281436398027505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466995363520957598685003 3700493045281436398027505)
              ·
                refine ⟨2775369783961077298520629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3700493045281436398027505 2775369783961077298520629)
                ·
                  refine ⟨260190917246350996736309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2775369783961077298520629 260190917246350996736309)
                  ·
                    rfl

theorem cell20_570060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_570060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570060 prefixEnd_570060 := by exact prefixLift 570060
  have htrace : WordTrace (prefixWord ++ tailWord_570060) baseStart_570060 baseEnd_570060 := by
    simpa [prefixWord, tailWord_570060, baseEnd_570060] using wordTrace_append hprefix tailTrace_570060
  have hstable : (prefixWord ++ tailWord_570060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570060).length < 2 ^ (prefixWord ++ tailWord_570060).sum := by decide
  have hdescent : baseEnd_570060 < baseStart_570060 := by decide
  rcases family_descends (prefixWord ++ tailWord_570060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570084 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 4]
def baseStart_570084 : Nat := 118140960795 + 570084 * 2 ^ 59
def prefixEnd_570084 : Nat := 4983230072969 + 3 ^ 40 * 570084 * 2
def baseEnd_570084 : Nat := 260201871500313579936211

theorem tailTrace_570084 : CollatzResearch.WordTrace tailWord_570084 prefixEnd_570084 260201871500313579936211 := by
  unfold tailWord_570084
  simp only [CollatzResearch.WordTrace]
  refine ⟨10396335833345252720438653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13861781111127003627251537 10396335833345252720438653)
  ·
    refine ⟨3898625937504469770164495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10396335833345252720438653 3898625937504469770164495)
    ·
      refine ⟨5847938906256704655246743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3898625937504469770164495 5847938906256704655246743)
      ·
        refine ⟨8771908359385056982870115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5847938906256704655246743 8771908359385056982870115)
        ·
          refine ⟨13157862539077585474305173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8771908359385056982870115 13157862539077585474305173)
          ·
            refine ⟨616774806519261819108055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13157862539077585474305173 616774806519261819108055)
            ·
              refine ⟨925162209778892728662083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616774806519261819108055 925162209778892728662083)
              ·
                refine ⟨1387743314668339092993125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 925162209778892728662083 1387743314668339092993125)
                ·
                  refine ⟨260201871500313579936211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1387743314668339092993125 260201871500313579936211)
                  ·
                    rfl

theorem cell20_570084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_570084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570084 prefixEnd_570084 := by exact prefixLift 570084
  have htrace : WordTrace (prefixWord ++ tailWord_570084) baseStart_570084 baseEnd_570084 := by
    simpa [prefixWord, tailWord_570084, baseEnd_570084] using wordTrace_append hprefix tailTrace_570084
  have hstable : (prefixWord ++ tailWord_570084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570084).length < 2 ^ (prefixWord ++ tailWord_570084).sum := by decide
  have hdescent : baseEnd_570084 < baseStart_570084 := by decide
  rcases family_descends (prefixWord ++ tailWord_570084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570094 : List Nat := [4, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_570094 : Nat := 118140960795 + 570094 * 2 ^ 59
def prefixEnd_570094 : Nat := 4983230072969 + 3 ^ 40 * 570094 * 2
def baseEnd_570094 : Nat := 260206435772797989602837

theorem tailTrace_570094 : CollatzResearch.WordTrace tailWord_570094 prefixEnd_570094 260206435772797989602837 := by
  unfold tailWord_570094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2599129549581784643592667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13862024264436184765827557 2599129549581784643592667)
  ·
    refine ⟨3898694324372676965389001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2599129549581784643592667 3898694324372676965389001)
    ·
      refine ⟨2924020743279507724041751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3898694324372676965389001 2924020743279507724041751)
      ·
        refine ⟨4386031114919261586062627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2924020743279507724041751 4386031114919261586062627)
        ·
          refine ⟨6579046672378892379093941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4386031114919261586062627 6579046672378892379093941)
          ·
            refine ⟨616785625535521160540057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6579046672378892379093941 616785625535521160540057)
            ·
              refine ⟨462589219151640870405043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 616785625535521160540057 462589219151640870405043)
              ·
                refine ⟨693883828727461305607565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462589219151640870405043 693883828727461305607565)
                ·
                  refine ⟨260206435772797989602837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 693883828727461305607565 260206435772797989602837)
                  ·
                    rfl

theorem cell20_570094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_570094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570094 prefixEnd_570094 := by exact prefixLift 570094
  have htrace : WordTrace (prefixWord ++ tailWord_570094) baseStart_570094 baseEnd_570094 := by
    simpa [prefixWord, tailWord_570094, baseEnd_570094] using wordTrace_append hprefix tailTrace_570094
  have hstable : (prefixWord ++ tailWord_570094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570094).length < 2 ^ (prefixWord ++ tailWord_570094).sum := by decide
  have hdescent : baseEnd_570094 < baseStart_570094 := by decide
  rcases family_descends (prefixWord ++ tailWord_570094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570122 : List Nat := [3, 1, 2, 2, 1, 2, 2, 5, 2]
def baseStart_570122 : Nat := 118140960795 + 570122 * 2 ^ 59
def prefixEnd_570122 : Nat := 4983230072969 + 3 ^ 40 * 570122 * 2
def baseEnd_570122 : Nat := 260219215735754336669389

theorem tailTrace_570122 : CollatzResearch.WordTrace tailWord_570122 prefixEnd_570122 260219215735754336669389 := by
  unfold tailWord_570122
  simp only [CollatzResearch.WordTrace]
  refine ⟨5198514410138209482690155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13862705093701891953840413 5198514410138209482690155)
  ·
    refine ⟨7797771615207314224035233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5198514410138209482690155 7797771615207314224035233)
    ·
      refine ⟨5848328711405485668026425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7797771615207314224035233 5848328711405485668026425)
      ·
        refine ⟨4386246533554114251019819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5848328711405485668026425 4386246533554114251019819)
        ·
          refine ⟨6579369800331171376529729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4386246533554114251019819 6579369800331171376529729)
          ·
            refine ⟨4934527350248378532397297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6579369800331171376529729 4934527350248378532397297)
            ·
              refine ⟨3700895512686283899297973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4934527350248378532397297 3700895512686283899297973)
              ·
                refine ⟨346958954314339115559185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3700895512686283899297973 346958954314339115559185)
                ·
                  refine ⟨260219215735754336669389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346958954314339115559185 260219215735754336669389)
                  ·
                    rfl

theorem cell20_570122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_570122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570122 prefixEnd_570122 := by exact prefixLift 570122
  have htrace : WordTrace (prefixWord ++ tailWord_570122) baseStart_570122 baseEnd_570122 := by
    simpa [prefixWord, tailWord_570122, baseEnd_570122] using wordTrace_append hprefix tailTrace_570122
  have hstable : (prefixWord ++ tailWord_570122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570122).length < 2 ^ (prefixWord ++ tailWord_570122).sum := by decide
  have hdescent : baseEnd_570122 < baseStart_570122 := by decide
  rcases family_descends (prefixWord ++ tailWord_570122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570135 : List Nat := [1, 1, 3, 4, 4, 1, 2, 2, 2]
def baseStart_570135 : Nat := 118140960795 + 570135 * 2 ^ 59
def prefixEnd_570135 : Nat := 4983230072969 + 3 ^ 40 * 570135 * 2
def baseEnd_570135 : Nat := 260225149289984069236003

theorem tailTrace_570135 : CollatzResearch.WordTrace tailWord_570135 prefixEnd_570135 260225149289984069236003 := by
  unfold tailWord_570135
  simp only [CollatzResearch.WordTrace]
  refine ⟨20794531789505741150983859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13863021193003827433989239 20794531789505741150983859)
  ·
    refine ⟨31191797684258611726475789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20794531789505741150983859 31191797684258611726475789)
    ·
      refine ⟨11696924131596979397428421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31191797684258611726475789 11696924131596979397428421)
      ·
        refine ⟨2193173274674433637017829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11696924131596979397428421 2193173274674433637017829)
        ·
          refine ⟨411219989001456306940843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2193173274674433637017829 411219989001456306940843)
          ·
            refine ⟨616829983502184460411265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411219989001456306940843 616829983502184460411265)
            ·
              refine ⟨462622487626638345308449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 616829983502184460411265 462622487626638345308449)
              ·
                refine ⟨346966865719978758981337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462622487626638345308449 346966865719978758981337)
                ·
                  refine ⟨260225149289984069236003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346966865719978758981337 260225149289984069236003)
                  ·
                    rfl

theorem cell20_570135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 2].length) (baseStart_570135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570135 prefixEnd_570135 := by exact prefixLift 570135
  have htrace : WordTrace (prefixWord ++ tailWord_570135) baseStart_570135 baseEnd_570135 := by
    simpa [prefixWord, tailWord_570135, baseEnd_570135] using wordTrace_append hprefix tailTrace_570135
  have hstable : (prefixWord ++ tailWord_570135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570135).length < 2 ^ (prefixWord ++ tailWord_570135).sum := by decide
  have hdescent : baseEnd_570135 < baseStart_570135 := by decide
  rcases family_descends (prefixWord ++ tailWord_570135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570188 : List Nat := [2, 2, 1, 3, 3, 2, 7]
def baseStart_570188 : Nat := 118140960795 + 570188 * 2 ^ 59
def prefixEnd_570188 : Nat := 4983230072969 + 3 ^ 40 * 570188 * 2
def baseEnd_570188 : Nat := 28916593326016826718791

theorem tailTrace_570188 : CollatzResearch.WordTrace tailWord_570188 prefixEnd_570188 28916593326016826718791 := by
  unfold tailWord_570188
  simp only [CollatzResearch.WordTrace]
  refine ⟨10398232429156865601331609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13864309905542487468442145 10398232429156865601331609)
  ·
    refine ⟨7798674321867649200998707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10398232429156865601331609 7798674321867649200998707)
    ·
      refine ⟨11698011482801473801498061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7798674321867649200998707 11698011482801473801498061)
      ·
        refine ⟨4386754306050552675561773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11698011482801473801498061 4386754306050552675561773)
        ·
          refine ⟨1645032864768957253335665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4386754306050552675561773 1645032864768957253335665)
          ·
            refine ⟨1233774648576717940001749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1645032864768957253335665 1233774648576717940001749)
            ·
              refine ⟨28916593326016826718791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1233774648576717940001749 28916593326016826718791)
              ·
                rfl

theorem cell20_570188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 7].length) (baseStart_570188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570188 prefixEnd_570188 := by exact prefixLift 570188
  have htrace : WordTrace (prefixWord ++ tailWord_570188) baseStart_570188 baseEnd_570188 := by
    simpa [prefixWord, tailWord_570188, baseEnd_570188] using wordTrace_append hprefix tailTrace_570188
  have hstable : (prefixWord ++ tailWord_570188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570188).length < 2 ^ (prefixWord ++ tailWord_570188).sum := by decide
  have hdescent : baseEnd_570188 < baseStart_570188 := by decide
  rcases family_descends (prefixWord ++ tailWord_570188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570233 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 5]
def baseStart_570233 : Nat := 118140960795 + 570233 * 2 ^ 59
def prefixEnd_570233 : Nat := 4983230072969 + 3 ^ 40 * 570233 * 2
def baseEnd_570233 : Nat := 260269879160331283968935

theorem tailTrace_570233 : CollatzResearch.WordTrace tailWord_570233 prefixEnd_570233 260269879160331283968935 := by
  unfold tailWord_570233
  simp only [CollatzResearch.WordTrace]
  refine ⟨20798106143150703888051353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13865404095433802592034235 20798106143150703888051353)
  ·
    refine ⟨15598579607363027916038515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20798106143150703888051353 15598579607363027916038515)
    ·
      refine ⟨23397869411044541874057773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15598579607363027916038515 23397869411044541874057773)
      ·
        refine ⟨8774201029141703202771665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23397869411044541874057773 8774201029141703202771665)
        ·
          refine ⟨6580650771856277402078749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8774201029141703202771665 6580650771856277402078749)
          ·
            refine ⟨2467744039446104025779531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6580650771856277402078749 2467744039446104025779531)
            ·
              refine ⟨3701616059169156038669297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2467744039446104025779531 3701616059169156038669297)
              ·
                refine ⟨2776212044376867029001973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3701616059169156038669297 2776212044376867029001973)
                ·
                  refine ⟨260269879160331283968935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2776212044376867029001973 260269879160331283968935)
                  ·
                    rfl

theorem cell20_570233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_570233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570233 prefixEnd_570233 := by exact prefixLift 570233
  have htrace : WordTrace (prefixWord ++ tailWord_570233) baseStart_570233 baseEnd_570233 := by
    simpa [prefixWord, tailWord_570233, baseEnd_570233] using wordTrace_append hprefix tailTrace_570233
  have hstable : (prefixWord ++ tailWord_570233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570233).length < 2 ^ (prefixWord ++ tailWord_570233).sum := by decide
  have hdescent : baseEnd_570233 < baseStart_570233 := by decide
  rcases family_descends (prefixWord ++ tailWord_570233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570250 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_570250 : Nat := 118140960795 + 570250 * 2 ^ 59
def prefixEnd_570250 : Nat := 4983230072969 + 3 ^ 40 * 570250 * 2
def baseEnd_570250 : Nat := 260277638423554780402199

theorem tailTrace_570250 : CollatzResearch.WordTrace tailWord_570250 prefixEnd_570250 260277638423554780402199 := by
  unfold tailWord_570250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5199681546022278947855051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13865817456059410527613469 5199681546022278947855051)
  ·
    refine ⟨7799522319033418421782577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5199681546022278947855051 7799522319033418421782577)
    ·
      refine ⟨5849641739275063816336933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7799522319033418421782577 5849641739275063816336933)
      ·
        refine ⟨1096807826114074465563175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5849641739275063816336933 1096807826114074465563175)
        ·
          refine ⟨1645211739171111698344763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096807826114074465563175 1645211739171111698344763)
          ·
            refine ⟨2467817608756667547517145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645211739171111698344763 2467817608756667547517145)
            ·
              refine ⟨1850863206567500660637859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2467817608756667547517145 1850863206567500660637859)
              ·
                refine ⟨2776294809851250990956789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1850863206567500660637859 2776294809851250990956789)
                ·
                  refine ⟨260277638423554780402199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2776294809851250990956789 260277638423554780402199)
                  ·
                    rfl

theorem cell20_570250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_570250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570250 prefixEnd_570250 := by exact prefixLift 570250
  have htrace : WordTrace (prefixWord ++ tailWord_570250) baseStart_570250 baseEnd_570250 := by
    simpa [prefixWord, tailWord_570250, baseEnd_570250] using wordTrace_append hprefix tailTrace_570250
  have hstable : (prefixWord ++ tailWord_570250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570250).length < 2 ^ (prefixWord ++ tailWord_570250).sum := by decide
  have hdescent : baseEnd_570250 < baseStart_570250 := by decide
  rcases family_descends (prefixWord ++ tailWord_570250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570308 : List Nat := [2, 3, 3, 3, 1, 1, 1, 4, 2]
def baseStart_570308 : Nat := 118140960795 + 570308 * 2 ^ 59
def prefixEnd_570308 : Nat := 4983230072969 + 3 ^ 40 * 570308 * 2
def baseEnd_570308 : Nat := 260304111203964356468629

theorem tailTrace_570308 : CollatzResearch.WordTrace tailWord_570308 prefixEnd_570308 260304111203964356468629 := by
  unfold tailWord_570308
  simp only [CollatzResearch.WordTrace]
  refine ⟨10400420808939495848515789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13867227745252661131354385 10400420808939495848515789)
  ·
    refine ⟨3900157803352310943193421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10400420808939495848515789 3900157803352310943193421)
    ·
      refine ⟨1462559176257116603697533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3900157803352310943193421 1462559176257116603697533)
      ·
        refine ⟨548459691096418726386575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1462559176257116603697533 548459691096418726386575)
        ·
          refine ⟨822689536644628089579863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548459691096418726386575 822689536644628089579863)
          ·
            refine ⟨1234034304966942134369795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 822689536644628089579863 1234034304966942134369795)
            ·
              refine ⟨1851051457450413201554693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1234034304966942134369795 1851051457450413201554693)
              ·
                refine ⟨347072148271952475291505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1851051457450413201554693 347072148271952475291505)
                ·
                  refine ⟨260304111203964356468629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347072148271952475291505 260304111203964356468629)
                  ·
                    rfl

theorem cell20_570308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_570308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570308 prefixEnd_570308 := by exact prefixLift 570308
  have htrace : WordTrace (prefixWord ++ tailWord_570308) baseStart_570308 baseEnd_570308 := by
    simpa [prefixWord, tailWord_570308, baseEnd_570308] using wordTrace_append hprefix tailTrace_570308
  have hstable : (prefixWord ++ tailWord_570308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570308).length < 2 ^ (prefixWord ++ tailWord_570308).sum := by decide
  have hdescent : baseEnd_570308 < baseStart_570308 := by decide
  rcases family_descends (prefixWord ++ tailWord_570308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570333 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 6]
def baseStart_570333 : Nat := 118140960795 + 570333 * 2 ^ 59
def prefixEnd_570333 : Nat := 4983230072969 + 3 ^ 40 * 570333 * 2
def baseEnd_570333 : Nat := 260315521885175380635193

theorem tailTrace_570333 : CollatzResearch.WordTrace tailWord_570333 prefixEnd_570333 260315521885175380635193 := by
  unfold tailWord_570333
  simp only [CollatzResearch.WordTrace]
  refine ⟨20801753442788420966691653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13867835628525613977794435 20801753442788420966691653)
  ·
    refine ⟨3900328770522828931254685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20801753442788420966691653 3900328770522828931254685)
    ·
      refine ⟨1462623288946060849220507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3900328770522828931254685 1462623288946060849220507)
      ·
        refine ⟨2193934933419091273830761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1462623288946060849220507 2193934933419091273830761)
        ·
          refine ⟨1645451200064318455373071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2193934933419091273830761 1645451200064318455373071)
          ·
            refine ⟨2468176800096477683059607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645451200064318455373071 2468176800096477683059607)
            ·
              refine ⟨3702265200144716524589411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2468176800096477683059607 3702265200144716524589411)
              ·
                refine ⟨5553397800217074786884117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3702265200144716524589411 5553397800217074786884117)
                ·
                  refine ⟨260315521885175380635193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5553397800217074786884117 260315521885175380635193)
                  ·
                    rfl

theorem cell20_570333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_570333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570333 prefixEnd_570333 := by exact prefixLift 570333
  have htrace : WordTrace (prefixWord ++ tailWord_570333) baseStart_570333 baseEnd_570333 := by
    simpa [prefixWord, tailWord_570333, baseEnd_570333] using wordTrace_append hprefix tailTrace_570333
  have hstable : (prefixWord ++ tailWord_570333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570333).length < 2 ^ (prefixWord ++ tailWord_570333).sum := by decide
  have hdescent : baseEnd_570333 < baseStart_570333 := by decide
  rcases family_descends (prefixWord ++ tailWord_570333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570361 : List Nat := [1, 2, 1, 3, 1, 3, 9]
def baseStart_570361 : Nat := 118140960795 + 570361 * 2 ^ 59
def prefixEnd_570361 : Nat := 4983230072969 + 3 ^ 40 * 570361 * 2
def baseEnd_570361 : Nat := 28925366872014636411305

theorem tailTrace_570361 : CollatzResearch.WordTrace tailWord_570361 prefixEnd_570361 28925366872014636411305 := by
  unfold tailWord_570361
  simp only [CollatzResearch.WordTrace]
  refine ⟨20802774686686981748710937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13868516457791321165807291 20802774686686981748710937)
  ·
    refine ⟨15602081015015236311533203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20802774686686981748710937 15602081015015236311533203)
    ·
      refine ⟨23403121522522854467299805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15602081015015236311533203 23403121522522854467299805)
      ·
        refine ⟨8776170570946070425237427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23403121522522854467299805 8776170570946070425237427)
        ·
          refine ⟨13164255856419105637856141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8776170570946070425237427 13164255856419105637856141)
          ·
            refine ⟨4936595946157164614196053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13164255856419105637856141 4936595946157164614196053)
            ·
              refine ⟨28925366872014636411305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4936595946157164614196053 28925366872014636411305)
              ·
                rfl

theorem cell20_570361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 9].length) (baseStart_570361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570361 prefixEnd_570361 := by exact prefixLift 570361
  have htrace : WordTrace (prefixWord ++ tailWord_570361) baseStart_570361 baseEnd_570361 := by
    simpa [prefixWord, tailWord_570361, baseEnd_570361] using wordTrace_append hprefix tailTrace_570361
  have hstable : (prefixWord ++ tailWord_570361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570361).length < 2 ^ (prefixWord ++ tailWord_570361).sum := by decide
  have hdescent : baseEnd_570361 < baseStart_570361 := by decide
  rcases family_descends (prefixWord ++ tailWord_570361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570364 : List Nat := [2, 2, 2, 1, 2, 3, 3, 2, 3]
def baseStart_570364 : Nat := 118140960795 + 570364 * 2 ^ 59
def prefixEnd_570364 : Nat := 4983230072969 + 3 ^ 40 * 570364 * 2
def baseEnd_570364 : Nat := 260329671129877050601733

theorem tailTrace_570364 : CollatzResearch.WordTrace tailWord_570364 prefixEnd_570364 260329671129877050601733 := by
  unfold tailWord_570364
  simp only [CollatzResearch.WordTrace]
  refine ⟨10401442052838056630535073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13868589403784075507380097 10401442052838056630535073)
  ·
    refine ⟨7801081539628542472901305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10401442052838056630535073 7801081539628542472901305)
    ·
      refine ⟨5850811154721406854675979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7801081539628542472901305 5850811154721406854675979)
      ·
        refine ⟨8776216732082110282013969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5850811154721406854675979 8776216732082110282013969)
        ·
          refine ⟨6582162549061582711510477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8776216732082110282013969 6582162549061582711510477)
          ·
            refine ⟨2468310955898093516816429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6582162549061582711510477 2468310955898093516816429)
            ·
              refine ⟨925616608461785068806161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2468310955898093516816429 925616608461785068806161)
              ·
                refine ⟨694212456346338801604621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 925616608461785068806161 694212456346338801604621)
                ·
                  refine ⟨260329671129877050601733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 694212456346338801604621 260329671129877050601733)
                  ·
                    rfl

theorem cell20_570364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_570364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570364 prefixEnd_570364 := by exact prefixLift 570364
  have htrace : WordTrace (prefixWord ++ tailWord_570364) baseStart_570364 baseEnd_570364 := by
    simpa [prefixWord, tailWord_570364, baseEnd_570364] using wordTrace_append hprefix tailTrace_570364
  have hstable : (prefixWord ++ tailWord_570364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570364).length < 2 ^ (prefixWord ++ tailWord_570364).sum := by decide
  have hdescent : baseEnd_570364 < baseStart_570364 := by decide
  rcases family_descends (prefixWord ++ tailWord_570364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570385 : List Nat := [1, 2, 2, 1, 1, 2, 1, 7, 3]
def baseStart_570385 : Nat := 118140960795 + 570385 * 2 ^ 59
def prefixEnd_570385 : Nat := 4983230072969 + 3 ^ 40 * 570385 * 2
def baseEnd_570385 : Nat := 260339256102094310901647

theorem tailTrace_570385 : CollatzResearch.WordTrace tailWord_570385 prefixEnd_570385 260339256102094310901647 := by
  unfold tailWord_570385
  simp only [CollatzResearch.WordTrace]
  refine ⟨20803650038600033847584609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13869100025733355898389739 20803650038600033847584609)
  ·
    refine ⟨15602737528950025385688457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20803650038600033847584609 15602737528950025385688457)
    ·
      refine ⟨11702053146712519039266343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15602737528950025385688457 11702053146712519039266343)
      ·
        refine ⟨17553079720068778558899515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11702053146712519039266343 17553079720068778558899515)
        ·
          refine ⟨26329619580103167838349273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17553079720068778558899515 26329619580103167838349273)
          ·
            refine ⟨19747214685077375878761955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26329619580103167838349273 19747214685077375878761955)
            ·
              refine ⟨29620822027616063818142933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19747214685077375878761955 29620822027616063818142933)
              ·
                refine ⟨694238016272251495737725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29620822027616063818142933 694238016272251495737725)
                ·
                  refine ⟨260339256102094310901647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 694238016272251495737725 260339256102094310901647)
                  ·
                    rfl

theorem cell20_570385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_570385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570385 prefixEnd_570385 := by exact prefixLift 570385
  have htrace : WordTrace (prefixWord ++ tailWord_570385) baseStart_570385 baseEnd_570385 := by
    simpa [prefixWord, tailWord_570385, baseEnd_570385] using wordTrace_append hprefix tailTrace_570385
  have hstable : (prefixWord ++ tailWord_570385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570385).length < 2 ^ (prefixWord ++ tailWord_570385).sum := by decide
  have hdescent : baseEnd_570385 < baseStart_570385 := by decide
  rcases family_descends (prefixWord ++ tailWord_570385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570422 : List Nat := [5, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_570422 : Nat := 118140960795 + 570422 * 2 ^ 59
def prefixEnd_570422 : Nat := 4983230072969 + 3 ^ 40 * 570422 * 2
def baseEnd_570422 : Nat := 260356143910286626668163

theorem tailTrace_570422 : CollatzResearch.WordTrace tailWord_570422 prefixEnd_570422 260356143910286626668163 := by
  unfold tailWord_570422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1300312471216624322917595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13869999692977326111121013 1300312471216624322917595)
  ·
    refine ⟨1950468706824936484376393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1300312471216624322917595 1950468706824936484376393)
    ·
      refine ⟨1462851530118702363282295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1950468706824936484376393 1462851530118702363282295)
      ·
        refine ⟨2194277295178053544923443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1462851530118702363282295 2194277295178053544923443)
        ·
          refine ⟨3291415942767080317385165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2194277295178053544923443 3291415942767080317385165)
          ·
            refine ⟨1234280978537655119019437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3291415942767080317385165 1234280978537655119019437)
            ·
              refine ⟨462855366951620669632289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1234280978537655119019437 462855366951620669632289)
              ·
                refine ⟨347141525213715502224217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462855366951620669632289 347141525213715502224217)
                ·
                  refine ⟨260356143910286626668163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347141525213715502224217 260356143910286626668163)
                  ·
                    rfl

theorem cell20_570422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_570422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570422 prefixEnd_570422 := by exact prefixLift 570422
  have htrace : WordTrace (prefixWord ++ tailWord_570422) baseStart_570422 baseEnd_570422 := by
    simpa [prefixWord, tailWord_570422, baseEnd_570422] using wordTrace_append hprefix tailTrace_570422
  have hstable : (prefixWord ++ tailWord_570422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570422).length < 2 ^ (prefixWord ++ tailWord_570422).sum := by decide
  have hdescent : baseEnd_570422 < baseStart_570422 := by decide
  rcases family_descends (prefixWord ++ tailWord_570422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570423 : List Nat := [1, 1, 3, 1, 2, 2, 1, 6, 3]
def baseStart_570423 : Nat := 118140960795 + 570423 * 2 ^ 59
def prefixEnd_570423 : Nat := 4983230072969 + 3 ^ 40 * 570423 * 2
def baseEnd_570423 : Nat := 260356600337535067634825

theorem tailTrace_570423 : CollatzResearch.WordTrace tailWord_570423 prefixEnd_570423 260356600337535067634825 := by
  unfold tailWord_570423
  simp only [CollatzResearch.WordTrace]
  refine ⟨20805036012462366337467923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13870024008308244224978615 20805036012462366337467923)
  ·
    refine ⟨31207554018693549506201885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20805036012462366337467923 31207554018693549506201885)
    ·
      refine ⟨11702832757010081064825707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31207554018693549506201885 11702832757010081064825707)
      ·
        refine ⟨17554249135515121597238561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11702832757010081064825707 17554249135515121597238561)
        ·
          refine ⟨13165686851636341197928921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17554249135515121597238561 13165686851636341197928921)
          ·
            refine ⟨9874265138727255898446691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13165686851636341197928921 9874265138727255898446691)
            ·
              refine ⟨14811397708090883847670037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9874265138727255898446691 14811397708090883847670037)
              ·
                refine ⟨694284267566760180359533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14811397708090883847670037 694284267566760180359533)
                ·
                  refine ⟨260356600337535067634825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 694284267566760180359533 260356600337535067634825)
                  ·
                    rfl

theorem cell20_570423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 3].length) (baseStart_570423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570423 prefixEnd_570423 := by exact prefixLift 570423
  have htrace : WordTrace (prefixWord ++ tailWord_570423) baseStart_570423 baseEnd_570423 := by
    simpa [prefixWord, tailWord_570423, baseEnd_570423] using wordTrace_append hprefix tailTrace_570423
  have hstable : (prefixWord ++ tailWord_570423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570423).length < 2 ^ (prefixWord ++ tailWord_570423).sum := by decide
  have hdescent : baseEnd_570423 < baseStart_570423 := by decide
  rcases family_descends (prefixWord ++ tailWord_570423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570433 : List Nat := [1, 2, 5, 1, 3, 1, 2, 5]
def baseStart_570433 : Nat := 118140960795 + 570433 * 2 ^ 59
def prefixEnd_570433 : Nat := 4983230072969 + 3 ^ 40 * 570433 * 2
def baseEnd_570433 : Nat := 86787054870006492433817

theorem tailTrace_570433 : CollatzResearch.WordTrace tailWord_570433 prefixEnd_570433 86787054870006492433817 := by
  unfold tailWord_570433
  simp only [CollatzResearch.WordTrace]
  refine ⟨20805400742426138045331953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13870267161617425363554635 20805400742426138045331953)
  ·
    refine ⟨15604050556819603533998965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20805400742426138045331953 15604050556819603533998965)
    ·
      refine ⟨1462879739701837831312403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15604050556819603533998965 1462879739701837831312403)
      ·
        refine ⟨2194319609552756746968605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1462879739701837831312403 2194319609552756746968605)
        ·
          refine ⟨822869853582283780113227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2194319609552756746968605 822869853582283780113227)
          ·
            refine ⟨1234304780373425670169841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 822869853582283780113227 1234304780373425670169841)
            ·
              refine ⟨925728585280069252627381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1234304780373425670169841 925728585280069252627381)
              ·
                refine ⟨86787054870006492433817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 925728585280069252627381 86787054870006492433817)
                ·
                  rfl

theorem cell20_570433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 5].length) (baseStart_570433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570433 prefixEnd_570433 := by exact prefixLift 570433
  have htrace : WordTrace (prefixWord ++ tailWord_570433) baseStart_570433 baseEnd_570433 := by
    simpa [prefixWord, tailWord_570433, baseEnd_570433] using wordTrace_append hprefix tailTrace_570433
  have hstable : (prefixWord ++ tailWord_570433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570433).length < 2 ^ (prefixWord ++ tailWord_570433).sum := by decide
  have hdescent : baseEnd_570433 < baseStart_570433 := by decide
  rcases family_descends (prefixWord ++ tailWord_570433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570437 : List Nat := [1, 3, 1, 1, 1, 3, 3, 7]
def baseStart_570437 : Nat := 118140960795 + 570437 * 2 ^ 59
def prefixEnd_570437 : Nat := 4983230072969 + 3 ^ 40 * 570437 * 2
def baseEnd_570437 : Nat := 86787663439671080389367

theorem tailTrace_570437 : CollatzResearch.WordTrace tailWord_570437 prefixEnd_570437 86787663439671080389367 := by
  unfold tailWord_570437
  simp only [CollatzResearch.WordTrace]
  refine ⟨20805546634411646728477565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13870364422941097818985043 20805546634411646728477565)
  ·
    refine ⟨7802079987904367523179087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20805546634411646728477565 7802079987904367523179087)
    ·
      refine ⟨11703119981856551284768631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7802079987904367523179087 11703119981856551284768631)
      ·
        refine ⟨17554679972784826927152947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11703119981856551284768631 17554679972784826927152947)
        ·
          refine ⟨26332019959177240390729421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17554679972784826927152947 26332019959177240390729421)
          ·
            refine ⟨9874507484691465146523533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26332019959177240390729421 9874507484691465146523533)
            ·
              refine ⟨3702940306759299429946325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9874507484691465146523533 3702940306759299429946325)
              ·
                refine ⟨86787663439671080389367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3702940306759299429946325 86787663439671080389367)
                ·
                  rfl

theorem cell20_570437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 7].length) (baseStart_570437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570437 prefixEnd_570437 := by exact prefixLift 570437
  have htrace : WordTrace (prefixWord ++ tailWord_570437) baseStart_570437 baseEnd_570437 := by
    simpa [prefixWord, tailWord_570437, baseEnd_570437] using wordTrace_append hprefix tailTrace_570437
  have hstable : (prefixWord ++ tailWord_570437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570437).length < 2 ^ (prefixWord ++ tailWord_570437).sum := by decide
  have hdescent : baseEnd_570437 < baseStart_570437 := by decide
  rcases family_descends (prefixWord ++ tailWord_570437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570478 : List Nat := [4, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_570478 : Nat := 118140960795 + 570478 * 2 ^ 59
def prefixEnd_570478 : Nat := 4983230072969 + 3 ^ 40 * 570478 * 2
def baseEnd_570478 : Nat := 260381703836199320801267

theorem tailTrace_570478 : CollatzResearch.WordTrace tailWord_570478 prefixEnd_570478 260381703836199320801267 := by
  unfold tailWord_570478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2600880253407888841340011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13871361351508740487146725 2600880253407888841340011)
  ·
    refine ⟨3901320380111833262010017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2600880253407888841340011 3901320380111833262010017)
    ·
      refine ⟨2925990285083874946507513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3901320380111833262010017 2925990285083874946507513)
      ·
        refine ⟨2194492713812906209880635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2925990285083874946507513 2194492713812906209880635)
        ·
          refine ⟨3291739070719359314820953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2194492713812906209880635 3291739070719359314820953)
          ·
            refine ⟨2468804303039519486115715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3291739070719359314820953 2468804303039519486115715)
            ·
              refine ⟨3703206454559279229173573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2468804303039519486115715 3703206454559279229173573)
              ·
                refine ⟨694351210229864855470045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3703206454559279229173573 694351210229864855470045)
                ·
                  refine ⟨260381703836199320801267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 694351210229864855470045 260381703836199320801267)
                  ·
                    rfl

theorem cell20_570478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_570478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570478 prefixEnd_570478 := by exact prefixLift 570478
  have htrace : WordTrace (prefixWord ++ tailWord_570478) baseStart_570478 baseEnd_570478 := by
    simpa [prefixWord, tailWord_570478, baseEnd_570478] using wordTrace_append hprefix tailTrace_570478
  have hstable : (prefixWord ++ tailWord_570478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570478).length < 2 ^ (prefixWord ++ tailWord_570478).sum := by decide
  have hdescent : baseEnd_570478 < baseStart_570478 := by decide
  rcases family_descends (prefixWord ++ tailWord_570478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570499 : List Nat := [1, 1, 1, 3, 3, 2, 1, 5, 3]
def baseStart_570499 : Nat := 118140960795 + 570499 * 2 ^ 59
def prefixEnd_570499 : Nat := 4983230072969 + 3 ^ 40 * 570499 * 2
def baseEnd_570499 : Nat := 260391288808416581101181

theorem tailTrace_570499 : CollatzResearch.WordTrace tailWord_570499 prefixEnd_570499 260391288808416581101181 := by
  unfold tailWord_570499
  simp only [CollatzResearch.WordTrace]
  refine ⟨20807807960187031317234551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13871871973458020878156367 20807807960187031317234551)
  ·
    refine ⟨31211711940280546975851827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20807807960187031317234551 31211711940280546975851827)
    ·
      refine ⟨46817567910420820463777741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31211711940280546975851827 46817567910420820463777741)
      ·
        refine ⟨17556587966407807673916653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46817567910420820463777741 17556587966407807673916653)
        ·
          refine ⟨6583720487402927877718745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17556587966407807673916653 6583720487402927877718745)
          ·
            refine ⟨4937790365552195908289059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6583720487402927877718745 4937790365552195908289059)
            ·
              refine ⟨7406685548328293862433589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4937790365552195908289059 7406685548328293862433589)
              ·
                refine ⟨694376770155777549603149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7406685548328293862433589 694376770155777549603149)
                ·
                  refine ⟨260391288808416581101181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 694376770155777549603149 260391288808416581101181)
                  ·
                    rfl

theorem cell20_570499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 3].length) (baseStart_570499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570499 prefixEnd_570499 := by exact prefixLift 570499
  have htrace : WordTrace (prefixWord ++ tailWord_570499) baseStart_570499 baseEnd_570499 := by
    simpa [prefixWord, tailWord_570499, baseEnd_570499] using wordTrace_append hprefix tailTrace_570499
  have hstable : (prefixWord ++ tailWord_570499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570499).length < 2 ^ (prefixWord ++ tailWord_570499).sum := by decide
  have hdescent : baseEnd_570499 < baseStart_570499 := by decide
  rcases family_descends (prefixWord ++ tailWord_570499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570551 : List Nat := [1, 1, 3, 1, 4, 1, 2, 7]
def baseStart_570551 : Nat := 118140960795 + 570551 * 2 ^ 59
def prefixEnd_570551 : Nat := 4983230072969 + 3 ^ 40 * 570551 * 2
def baseEnd_570551 : Nat := 86805007675111837122545

theorem tailTrace_570551 : CollatzResearch.WordTrace tailWord_570551 prefixEnd_570551 86805007675111837122545 := by
  unfold tailWord_570551
  simp only [CollatzResearch.WordTrace]
  refine ⟨20809704555998644198127507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13873136370665762798751671 20809704555998644198127507)
  ·
    refine ⟨31214556833997966297191261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20809704555998644198127507 31214556833997966297191261)
    ·
      refine ⟨11705458812749237361446723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31214556833997966297191261 11705458812749237361446723)
      ·
        refine ⟨17558188219123856042170085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11705458812749237361446723 17558188219123856042170085)
        ·
          refine ⟨3292160291085723007906891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17558188219123856042170085 3292160291085723007906891)
          ·
            refine ⟨4938240436628584511860337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3292160291085723007906891 4938240436628584511860337)
            ·
              refine ⟨3703680327471438383895253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4938240436628584511860337 3703680327471438383895253)
              ·
                refine ⟨86805007675111837122545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3703680327471438383895253 86805007675111837122545)
                ·
                  rfl

theorem cell20_570551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 7].length) (baseStart_570551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570551 prefixEnd_570551 := by exact prefixLift 570551
  have htrace : WordTrace (prefixWord ++ tailWord_570551) baseStart_570551 baseEnd_570551 := by
    simpa [prefixWord, tailWord_570551, baseEnd_570551] using wordTrace_append hprefix tailTrace_570551
  have hstable : (prefixWord ++ tailWord_570551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570551).length < 2 ^ (prefixWord ++ tailWord_570551).sum := by decide
  have hdescent : baseEnd_570551 < baseStart_570551 := by decide
  rcases family_descends (prefixWord ++ tailWord_570551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570564 : List Nat := [2, 3, 3, 1, 3, 2, 2, 4]
def baseStart_570564 : Nat := 118140960795 + 570564 * 2 ^ 59
def prefixEnd_570564 : Nat := 4983230072969 + 3 ^ 40 * 570564 * 2
def baseEnd_570564 : Nat := 86806985526521747978083

theorem tailTrace_570564 : CollatzResearch.WordTrace tailWord_570564 prefixEnd_570564 86806985526521747978083 := by
  unfold tailWord_570564
  simp only [CollatzResearch.WordTrace]
  refine ⟨10405089352475773709175373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13873452469967698278900497 10405089352475773709175373)
  ·
    refine ⟨3901908507178415140940765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10405089352475773709175373 3901908507178415140940765)
    ·
      refine ⟨1463215690191905677852787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3901908507178415140940765 1463215690191905677852787)
      ·
        refine ⟨2194823535287858516779181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1463215690191905677852787 2194823535287858516779181)
        ·
          refine ⟨823058825732946943792193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2194823535287858516779181 823058825732946943792193)
          ·
            refine ⟨617294119299710207844145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 823058825732946943792193 617294119299710207844145)
            ·
              refine ⟨462970589474782655883109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 617294119299710207844145 462970589474782655883109)
              ·
                refine ⟨86806985526521747978083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 462970589474782655883109 86806985526521747978083)
                ·
                  rfl

theorem cell20_570564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_570564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570564 prefixEnd_570564 := by exact prefixLift 570564
  have htrace : WordTrace (prefixWord ++ tailWord_570564) baseStart_570564 baseEnd_570564 := by
    simpa [prefixWord, tailWord_570564, baseEnd_570564] using wordTrace_append hprefix tailTrace_570564
  have hstable : (prefixWord ++ tailWord_570564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570564).length < 2 ^ (prefixWord ++ tailWord_570564).sum := by decide
  have hdescent : baseEnd_570564 < baseStart_570564 := by decide
  rcases family_descends (prefixWord ++ tailWord_570564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570568 : List Nat := [2, 1, 3, 1, 2, 1, 6, 4]
def baseStart_570568 : Nat := 118140960795 + 570568 * 2 ^ 59
def prefixEnd_570568 : Nat := 4983230072969 + 3 ^ 40 * 570568 * 2
def baseEnd_570568 : Nat := 86807594096186335933633

theorem tailTrace_570568 : CollatzResearch.WordTrace tailWord_570568 prefixEnd_570568 86807594096186335933633 := by
  unfold tailWord_570568
  simp only [CollatzResearch.WordTrace]
  refine ⟨10405162298468528050748179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13873549731291370734330905 10405162298468528050748179)
  ·
    refine ⟨15607743447702792076122269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10405162298468528050748179 15607743447702792076122269)
    ·
      refine ⟨5852903792888547028545851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15607743447702792076122269 5852903792888547028545851)
      ·
        refine ⟨8779355689332820542818777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5852903792888547028545851 8779355689332820542818777)
        ·
          refine ⟨6584516766999615407114083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8779355689332820542818777 6584516766999615407114083)
          ·
            refine ⟨9876775150499423110671125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6584516766999615407114083 9876775150499423110671125)
            ·
              refine ⟨462973835179660458312709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9876775150499423110671125 462973835179660458312709)
              ·
                refine ⟨86807594096186335933633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 462973835179660458312709 86807594096186335933633)
                ·
                  rfl

theorem cell20_570568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_570568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570568 prefixEnd_570568 := by exact prefixLift 570568
  have htrace : WordTrace (prefixWord ++ tailWord_570568) baseStart_570568 baseEnd_570568 := by
    simpa [prefixWord, tailWord_570568, baseEnd_570568] using wordTrace_append hprefix tailTrace_570568
  have hstable : (prefixWord ++ tailWord_570568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570568).length < 2 ^ (prefixWord ++ tailWord_570568).sum := by decide
  have hdescent : baseEnd_570568 < baseStart_570568 := by decide
  rcases family_descends (prefixWord ++ tailWord_570568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570574 : List Nat := [4, 1, 1, 1, 6, 1, 1, 3, 2]
def baseStart_570574 : Nat := 118140960795 + 570574 * 2 ^ 59
def prefixEnd_570574 : Nat := 4983230072969 + 3 ^ 40 * 570574 * 2
def baseEnd_570574 : Nat := 260425520852049653600875

theorem tailTrace_570574 : CollatzResearch.WordTrace tailWord_570574 prefixEnd_570574 260425520852049653600875 := by
  unfold tailWord_570574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2601317929364414890776847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13873695623276879417476517 2601317929364414890776847)
  ·
    refine ⟨3901976894046622336165271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2601317929364414890776847 3901976894046622336165271)
    ·
      refine ⟨5852965341069933504247907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3901976894046622336165271 5852965341069933504247907)
      ·
        refine ⟨8779448011604900256371861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5852965341069933504247907 8779448011604900256371861)
        ·
          refine ⟨411536625543979699517431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8779448011604900256371861 411536625543979699517431)
          ·
            refine ⟨617304938315969549276147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411536625543979699517431 617304938315969549276147)
            ·
              refine ⟨925957407473954323914221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617304938315969549276147 925957407473954323914221)
              ·
                refine ⟨347234027802732871467833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 925957407473954323914221 347234027802732871467833)
                ·
                  refine ⟨260425520852049653600875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347234027802732871467833 260425520852049653600875)
                  ·
                    rfl

theorem cell20_570574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_570574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570574 prefixEnd_570574 := by exact prefixLift 570574
  have htrace : WordTrace (prefixWord ++ tailWord_570574) baseStart_570574 baseEnd_570574 := by
    simpa [prefixWord, tailWord_570574, baseEnd_570574] using wordTrace_append hprefix tailTrace_570574
  have hstable : (prefixWord ++ tailWord_570574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570574).length < 2 ^ (prefixWord ++ tailWord_570574).sum := by decide
  have hdescent : baseEnd_570574 < baseStart_570574 := by decide
  rcases family_descends (prefixWord ++ tailWord_570574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570627 : List Nat := [1, 1, 1, 3, 2, 4, 2, 6]
def baseStart_570627 : Nat := 118140960795 + 570627 * 2 ^ 59
def prefixEnd_570627 : Nat := 4983230072969 + 3 ^ 40 * 570627 * 2
def baseEnd_570627 : Nat := 86816570498739008277997

theorem tailTrace_570627 : CollatzResearch.WordTrace tailWord_570627 prefixEnd_570627 86816570498739008277997 := by
  unfold tailWord_570627
  simp only [CollatzResearch.WordTrace]
  refine ⟨20812476503723309177894135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13874984335815539451929423 20812476503723309177894135)
  ·
    refine ⟨31218714755584963766841203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20812476503723309177894135 31218714755584963766841203)
    ·
      refine ⟨46828072133377445650261805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31218714755584963766841203 46828072133377445650261805)
      ·
        refine ⟨17560527050016542118848177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46828072133377445650261805 17560527050016542118848177)
        ·
          refine ⟨13170395287512406589136133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17560527050016542118848177 13170395287512406589136133)
          ·
            refine ⟨2469449116408576235463025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13170395287512406589136133 2469449116408576235463025)
            ·
              refine ⟨1852086837306432176597269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2469449116408576235463025 1852086837306432176597269)
              ·
                refine ⟨86816570498739008277997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1852086837306432176597269 86816570498739008277997)
                ·
                  rfl

theorem cell20_570627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 6].length) (baseStart_570627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570627 prefixEnd_570627 := by exact prefixLift 570627
  have htrace : WordTrace (prefixWord ++ tailWord_570627) baseStart_570627 baseEnd_570627 := by
    simpa [prefixWord, tailWord_570627, baseEnd_570627] using wordTrace_append hprefix tailTrace_570627
  have hstable : (prefixWord ++ tailWord_570627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570627).length < 2 ^ (prefixWord ++ tailWord_570627).sum := by decide
  have hdescent : baseEnd_570627 < baseStart_570627 := by decide
  rcases family_descends (prefixWord ++ tailWord_570627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570682 : List Nat := [3, 1, 1, 1, 4, 1, 5, 4]
def baseStart_570682 : Nat := 118140960795 + 570682 * 2 ^ 59
def prefixEnd_570682 : Nat := 4983230072969 + 3 ^ 40 * 570682 * 2
def baseEnd_570682 : Nat := 86824938331627092666811

theorem tailTrace_570682 : CollatzResearch.WordTrace tailWord_570682 prefixEnd_570682 86824938331627092666811 := by
  unfold tailWord_570682
  simp only [CollatzResearch.WordTrace]
  refine ⟨5203620629631013392786575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13876321679016035714097533 5203620629631013392786575)
  ·
    refine ⟨7805430944446520089179863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5203620629631013392786575 7805430944446520089179863)
    ·
      refine ⟨11708146416669780133769795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7805430944446520089179863 11708146416669780133769795)
      ·
        refine ⟨17562219625004670200654693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11708146416669780133769795 17562219625004670200654693)
        ·
          refine ⟨3292916179688375662622755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17562219625004670200654693 3292916179688375662622755)
          ·
            refine ⟨4939374269532563493934133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3292916179688375662622755 4939374269532563493934133)
            ·
              refine ⟨463066337768677827556325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4939374269532563493934133 463066337768677827556325)
              ·
                refine ⟨86824938331627092666811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 463066337768677827556325 86824938331627092666811)
                ·
                  rfl

theorem cell20_570682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_570682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570682 prefixEnd_570682 := by exact prefixLift 570682
  have htrace : WordTrace (prefixWord ++ tailWord_570682) baseStart_570682 baseEnd_570682 := by
    simpa [prefixWord, tailWord_570682, baseEnd_570682] using wordTrace_append hprefix tailTrace_570682
  have hstable : (prefixWord ++ tailWord_570682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570682).length < 2 ^ (prefixWord ++ tailWord_570682).sum := by decide
  have hdescent : baseEnd_570682 < baseStart_570682 := by decide
  rcases family_descends (prefixWord ++ tailWord_570682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570713 : List Nat := [1, 2, 1, 2, 2, 2, 4, 4, 2]
def baseStart_570713 : Nat := 118140960795 + 570713 * 2 ^ 59
def prefixEnd_570713 : Nat := 4983230072969 + 3 ^ 40 * 570713 * 2
def baseEnd_570713 : Nat := 260488964239582947966973

theorem tailTrace_570713 : CollatzResearch.WordTrace tailWord_570713 prefixEnd_570713 260488964239582947966973 := by
  unfold tailWord_570713
  simp only [CollatzResearch.WordTrace]
  refine ⟨20815613181411745865524793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13877075454274497243683195 20815613181411745865524793)
  ·
    refine ⟨15611709886058809399143595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20815613181411745865524793 15611709886058809399143595)
    ·
      refine ⟨23417564829088214098715393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15611709886058809399143595 23417564829088214098715393)
      ·
        refine ⟨17563173621816160574036545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23417564829088214098715393 17563173621816160574036545)
        ·
          refine ⟨13172380216362120430527409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17563173621816160574036545 13172380216362120430527409)
          ·
            refine ⟨9879285162271590322895557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13172380216362120430527409 9879285162271590322895557)
            ·
              refine ⟨1852365967925923185542917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9879285162271590322895557 1852365967925923185542917)
              ·
                refine ⟨347318618986110597289297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1852365967925923185542917 347318618986110597289297)
                ·
                  refine ⟨260488964239582947966973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347318618986110597289297 260488964239582947966973)
                  ·
                    rfl

theorem cell20_570713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 2].length) (baseStart_570713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570713 prefixEnd_570713 := by exact prefixLift 570713
  have htrace : WordTrace (prefixWord ++ tailWord_570713) baseStart_570713 baseEnd_570713 := by
    simpa [prefixWord, tailWord_570713, baseEnd_570713] using wordTrace_append hprefix tailTrace_570713
  have hstable : (prefixWord ++ tailWord_570713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570713).length < 2 ^ (prefixWord ++ tailWord_570713).sum := by decide
  have hdescent : baseEnd_570713 < baseStart_570713 := by decide
  rcases family_descends (prefixWord ++ tailWord_570713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570748 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 7]
def baseStart_570748 : Nat := 118140960795 + 570748 * 2 ^ 59
def prefixEnd_570748 : Nat := 4983230072969 + 3 ^ 40 * 570748 * 2
def baseEnd_570748 : Nat := 260504939193278381800163

theorem tailTrace_570748 : CollatzResearch.WordTrace tailWord_570748 prefixEnd_570748 260504939193278381800163 := by
  unfold tailWord_570748
  simp only [CollatzResearch.WordTrace]
  refine ⟨10408444868142473421524449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13877926490856631228699265 10408444868142473421524449)
  ·
    refine ⟨7806333651106855066143337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10408444868142473421524449 7806333651106855066143337)
    ·
      refine ⟨5854750238330141299607503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7806333651106855066143337 5854750238330141299607503)
      ·
        refine ⟨8782125357495211949411255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5854750238330141299607503 8782125357495211949411255)
        ·
          refine ⟨13173188036242817924116883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8782125357495211949411255 13173188036242817924116883)
          ·
            refine ⟨19759782054364226886175325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13173188036242817924116883 19759782054364226886175325)
            ·
              refine ⟨7409918270386585082315747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19759782054364226886175325 7409918270386585082315747)
              ·
                refine ⟨11114877405579877623473621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7409918270386585082315747 11114877405579877623473621)
                ·
                  refine ⟨260504939193278381800163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11114877405579877623473621 260504939193278381800163)
                  ·
                    rfl

theorem cell20_570748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_570748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570748 prefixEnd_570748 := by exact prefixLift 570748
  have htrace : WordTrace (prefixWord ++ tailWord_570748) baseStart_570748 baseEnd_570748 := by
    simpa [prefixWord, tailWord_570748, baseEnd_570748] using wordTrace_append hprefix tailTrace_570748
  have hstable : (prefixWord ++ tailWord_570748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570748).length < 2 ^ (prefixWord ++ tailWord_570748).sum := by decide
  have hdescent : baseEnd_570748 < baseStart_570748 := by decide
  rcases family_descends (prefixWord ++ tailWord_570748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570820 : List Nat := [2, 3, 3, 2, 1, 1, 1, 4, 3]
def baseStart_570820 : Nat := 118140960795 + 570820 * 2 ^ 59
def prefixEnd_570820 : Nat := 4983230072969 + 3 ^ 40 * 570820 * 2
def baseEnd_570820 : Nat := 260537801955166131399869

theorem tailTrace_570820 : CollatzResearch.WordTrace tailWord_570820 prefixEnd_570820 260537801955166131399869 := by
  unfold tailWord_570820
  simp only [CollatzResearch.WordTrace]
  refine ⟨10409757896012051569834957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13879677194682735426446609 10409757896012051569834957)
  ·
    refine ⟨3903659211004519338688109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10409757896012051569834957 3903659211004519338688109)
    ·
      refine ⟨1463872204126694752008041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3903659211004519338688109 1463872204126694752008041)
      ·
        refine ⟨1097904153095021064006031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1463872204126694752008041 1097904153095021064006031)
        ·
          refine ⟨1646856229642531596009047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1097904153095021064006031 1646856229642531596009047)
          ·
            refine ⟨2470284344463797394013571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1646856229642531596009047 2470284344463797394013571)
            ·
              refine ⟨3705426516695696091020357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2470284344463797394013571 3705426516695696091020357)
              ·
                refine ⟨694767471880443017066317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3705426516695696091020357 694767471880443017066317)
                ·
                  refine ⟨260537801955166131399869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 694767471880443017066317 260537801955166131399869)
                  ·
                    rfl

theorem cell20_570820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_570820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570820 prefixEnd_570820 := by exact prefixLift 570820
  have htrace : WordTrace (prefixWord ++ tailWord_570820) baseStart_570820 baseEnd_570820 := by
    simpa [prefixWord, tailWord_570820, baseEnd_570820] using wordTrace_append hprefix tailTrace_570820
  have hstable : (prefixWord ++ tailWord_570820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570820).length < 2 ^ (prefixWord ++ tailWord_570820).sum := by decide
  have hdescent : baseEnd_570820 < baseStart_570820 := by decide
  rcases family_descends (prefixWord ++ tailWord_570820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570841 : List Nat := [1, 2, 1, 2, 4, 2, 2, 3, 3]
def baseStart_570841 : Nat := 118140960795 + 570841 * 2 ^ 59
def prefixEnd_570841 : Nat := 4983230072969 + 3 ^ 40 * 570841 * 2
def baseEnd_570841 : Nat := 260547386927383391699783

theorem tailTrace_570841 : CollatzResearch.WordTrace tailWord_570841 prefixEnd_570841 260547386927383391699783 := by
  unfold tailWord_570841
  simp only [CollatzResearch.WordTrace]
  refine ⟨20820281724948023726184377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13880187816632015817456251 20820281724948023726184377)
  ·
    refine ⟨15615211293711017794638283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20820281724948023726184377 15615211293711017794638283)
    ·
      refine ⟨23422816940566526691957425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15615211293711017794638283 23422816940566526691957425)
      ·
        refine ⟨17567112705424895018968069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23422816940566526691957425 17567112705424895018968069)
        ·
          refine ⟨3293833632267167816056513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17567112705424895018968069 3293833632267167816056513)
          ·
            refine ⟨2470375224200375862042385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3293833632267167816056513 2470375224200375862042385)
            ·
              refine ⟨1852781418150281896531789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2470375224200375862042385 1852781418150281896531789)
              ·
                refine ⟨694793031806355711199421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1852781418150281896531789 694793031806355711199421)
                ·
                  refine ⟨260547386927383391699783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 694793031806355711199421 260547386927383391699783)
                  ·
                    rfl

theorem cell20_570841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_570841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570841 prefixEnd_570841 := by exact prefixLift 570841
  have htrace : WordTrace (prefixWord ++ tailWord_570841) baseStart_570841 baseEnd_570841 := by
    simpa [prefixWord, tailWord_570841, baseEnd_570841] using wordTrace_append hprefix tailTrace_570841
  have hstable : (prefixWord ++ tailWord_570841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570841).length < 2 ^ (prefixWord ++ tailWord_570841).sum := by decide
  have hdescent : baseEnd_570841 < baseStart_570841 := by decide
  rcases family_descends (prefixWord ++ tailWord_570841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570861 : List Nat := [1, 5, 1, 3, 2, 1, 2, 3, 2]
def baseStart_570861 : Nat := 118140960795 + 570861 * 2 ^ 59
def prefixEnd_570861 : Nat := 4983230072969 + 3 ^ 40 * 570861 * 2
def baseEnd_570861 : Nat := 260556515472352211033035

theorem tailTrace_570861 : CollatzResearch.WordTrace tailWord_570861 prefixEnd_570861 260556515472352211033035 := by
  unfold tailWord_570861
  simp only [CollatzResearch.WordTrace]
  refine ⟨20821011184875567141912437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13880674123250378094608291 20821011184875567141912437)
  ·
    refine ⟨1951969798582084419554291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20821011184875567141912437 1951969798582084419554291)
    ·
      refine ⟨2927954697873126629331437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1951969798582084419554291 2927954697873126629331437)
      ·
        refine ⟨1097983011702422485999289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2927954697873126629331437 1097983011702422485999289)
        ·
          refine ⟨823487258776816864499467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1097983011702422485999289 823487258776816864499467)
          ·
            refine ⟨1235230888165225296749201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823487258776816864499467 1235230888165225296749201)
            ·
              refine ⟨926423166123918972561901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1235230888165225296749201 926423166123918972561901)
              ·
                refine ⟨347408687296469614710713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 926423166123918972561901 347408687296469614710713)
                ·
                  refine ⟨260556515472352211033035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347408687296469614710713 260556515472352211033035)
                  ·
                    rfl

theorem cell20_570861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_570861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570861 prefixEnd_570861 := by exact prefixLift 570861
  have htrace : WordTrace (prefixWord ++ tailWord_570861) baseStart_570861 baseEnd_570861 := by
    simpa [prefixWord, tailWord_570861, baseEnd_570861] using wordTrace_append hprefix tailTrace_570861
  have hstable : (prefixWord ++ tailWord_570861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570861).length < 2 ^ (prefixWord ++ tailWord_570861).sum := by decide
  have hdescent : baseEnd_570861 < baseStart_570861 := by decide
  rcases family_descends (prefixWord ++ tailWord_570861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570865 : List Nat := [1, 2, 2, 2, 3, 2, 1, 5, 2]
def baseStart_570865 : Nat := 118140960795 + 570865 * 2 ^ 59
def prefixEnd_570865 : Nat := 4983230072969 + 3 ^ 40 * 570865 * 2
def baseEnd_570865 : Nat := 260558341181345974899685

theorem tailTrace_570865 : CollatzResearch.WordTrace tailWord_570865 prefixEnd_570865 260558341181345974899685 := by
  unfold tailWord_570865
  simp only [CollatzResearch.WordTrace]
  refine ⟨20821157076861075825058049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13880771384574050550038699 20821157076861075825058049)
  ·
    refine ⟨15615867807645806868793537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20821157076861075825058049 15615867807645806868793537)
    ·
      refine ⟨11711900855734355151595153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15615867807645806868793537 11711900855734355151595153)
      ·
        refine ⟨8783925641800766363696365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11711900855734355151595153 8783925641800766363696365)
        ·
          refine ⟨3293972115675287386386137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8783925641800766363696365 3293972115675287386386137)
          ·
            refine ⟨2470479086756465539789603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3293972115675287386386137 2470479086756465539789603)
            ·
              refine ⟨3705718630134698309684405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2470479086756465539789603 3705718630134698309684405)
              ·
                refine ⟨347411121575127966532913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3705718630134698309684405 347411121575127966532913)
                ·
                  refine ⟨260558341181345974899685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347411121575127966532913 260558341181345974899685)
                  ·
                    rfl

theorem cell20_570865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 2].length) (baseStart_570865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570865 prefixEnd_570865 := by exact prefixLift 570865
  have htrace : WordTrace (prefixWord ++ tailWord_570865) baseStart_570865 baseEnd_570865 := by
    simpa [prefixWord, tailWord_570865, baseEnd_570865] using wordTrace_append hprefix tailTrace_570865
  have hstable : (prefixWord ++ tailWord_570865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570865).length < 2 ^ (prefixWord ++ tailWord_570865).sum := by decide
  have hdescent : baseEnd_570865 < baseStart_570865 := by decide
  rcases family_descends (prefixWord ++ tailWord_570865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570882 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_570882 : Nat := 118140960795 + 570882 * 2 ^ 59
def prefixEnd_570882 : Nat := 4983230072969 + 3 ^ 40 * 570882 * 2
def baseEnd_570882 : Nat := 260566100444569471332949

theorem tailTrace_570882 : CollatzResearch.WordTrace tailWord_570882 prefixEnd_570882 260566100444569471332949 := by
  unfold tailWord_570882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5205444279449871932106725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13881184745199658485617933 5205444279449871932106725)
  ·
    refine ⟨976020802396850987270011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5205444279449871932106725 976020802396850987270011)
    ·
      refine ⟨1464031203595276480905017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 976020802396850987270011 1464031203595276480905017)
      ·
        refine ⟨1098023402696457360678763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1464031203595276480905017 1098023402696457360678763)
        ·
          refine ⟨1647035104044686041018145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1098023402696457360678763 1647035104044686041018145)
          ·
            refine ⟨1235276328033514530763609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1647035104044686041018145 1235276328033514530763609)
            ·
              refine ⟨926457246025135898072707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1235276328033514530763609 926457246025135898072707)
              ·
                refine ⟨1389685869037703847109061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926457246025135898072707 1389685869037703847109061)
                ·
                  refine ⟨260566100444569471332949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1389685869037703847109061 260566100444569471332949)
                  ·
                    rfl

theorem cell20_570882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_570882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570882 prefixEnd_570882 := by exact prefixLift 570882
  have htrace : WordTrace (prefixWord ++ tailWord_570882) baseStart_570882 baseEnd_570882 := by
    simpa [prefixWord, tailWord_570882, baseEnd_570882] using wordTrace_append hprefix tailTrace_570882
  have hstable : (prefixWord ++ tailWord_570882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570882).length < 2 ^ (prefixWord ++ tailWord_570882).sum := by decide
  have hdescent : baseEnd_570882 < baseStart_570882 := by decide
  rcases family_descends (prefixWord ++ tailWord_570882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570931 : List Nat := [1, 1, 1, 2, 4, 5, 6]
def baseStart_570931 : Nat := 118140960795 + 570931 * 2 ^ 59
def prefixEnd_570931 : Nat := 4983230072969 + 3 ^ 40 * 570931 * 2
def baseEnd_570931 : Nat := 28954273931082564299935

theorem tailTrace_570931 : CollatzResearch.WordTrace tailWord_570931 prefixEnd_570931 28954273931082564299935 := by
  unfold tailWord_570931
  simp only [CollatzResearch.WordTrace]
  refine ⟨20823564294621969096960647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13882376196414646064640431 20823564294621969096960647)
  ·
    refine ⟨31235346441932953645440971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20823564294621969096960647 31235346441932953645440971)
    ·
      refine ⟨46853019662899430468161457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31235346441932953645440971 46853019662899430468161457)
      ·
        refine ⟨35139764747174572851121093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46853019662899430468161457 35139764747174572851121093)
        ·
          refine ⟨6588705890095232409585205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35139764747174572851121093 6588705890095232409585205)
          ·
            refine ⟨617691177196428038398613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6588705890095232409585205 617691177196428038398613)
            ·
              refine ⟨28954273931082564299935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 617691177196428038398613 28954273931082564299935)
              ·
                rfl

theorem cell20_570931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 6].length) (baseStart_570931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570931 prefixEnd_570931 := by exact prefixLift 570931
  have htrace : WordTrace (prefixWord ++ tailWord_570931) baseStart_570931 baseEnd_570931 := by
    simpa [prefixWord, tailWord_570931, baseEnd_570931] using wordTrace_append hprefix tailTrace_570931
  have hstable : (prefixWord ++ tailWord_570931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570931).length < 2 ^ (prefixWord ++ tailWord_570931).sum := by decide
  have hdescent : baseEnd_570931 < baseStart_570931 := by decide
  rcases family_descends (prefixWord ++ tailWord_570931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570938 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_570938 : Nat := 118140960795 + 570938 * 2 ^ 59
def prefixEnd_570938 : Nat := 4983230072969 + 3 ^ 40 * 570938 * 2
def baseEnd_570938 : Nat := 260591660370482165466053

theorem tailTrace_570938 : CollatzResearch.WordTrace tailWord_570938 prefixEnd_570938 260591660370482165466053 := by
  unfold tailWord_570938
  simp only [CollatzResearch.WordTrace]
  refine ⟨5205954901399152323116367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13882546403731072861643645 5205954901399152323116367)
  ·
    refine ⟨7808932352098728484674551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5205954901399152323116367 7808932352098728484674551)
    ·
      refine ⟨11713398528148092727011827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7808932352098728484674551 11713398528148092727011827)
      ·
        refine ⟨17570097792222139090517741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11713398528148092727011827 17570097792222139090517741)
        ·
          refine ⟨6588786672083302158944153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17570097792222139090517741 6588786672083302158944153)
          ·
            refine ⟨4941590004062476619208115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6588786672083302158944153 4941590004062476619208115)
            ·
              refine ⟨7412385006093714928812173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4941590004062476619208115 7412385006093714928812173)
              ·
                refine ⟨2779644377285143098304565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7412385006093714928812173 2779644377285143098304565)
                ·
                  refine ⟨260591660370482165466053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2779644377285143098304565 260591660370482165466053)
                  ·
                    rfl

theorem cell20_570938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_570938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570938 prefixEnd_570938 := by exact prefixLift 570938
  have htrace : WordTrace (prefixWord ++ tailWord_570938) baseStart_570938 baseEnd_570938 := by
    simpa [prefixWord, tailWord_570938, baseEnd_570938] using wordTrace_append hprefix tailTrace_570938
  have hstable : (prefixWord ++ tailWord_570938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570938).length < 2 ^ (prefixWord ++ tailWord_570938).sum := by decide
  have hdescent : baseEnd_570938 < baseStart_570938 := by decide
  rcases family_descends (prefixWord ++ tailWord_570938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570951 : List Nat := [1, 1, 4, 1, 5, 2, 2, 1, 3]
def baseStart_570951 : Nat := 118140960795 + 570951 * 2 ^ 59
def prefixEnd_570951 : Nat := 4983230072969 + 3 ^ 40 * 570951 * 2
def baseEnd_570951 : Nat := 260597593924711898032667

theorem tailTrace_570951 : CollatzResearch.WordTrace tailWord_570951 prefixEnd_570951 260597593924711898032667 := by
  unfold tailWord_570951
  simp only [CollatzResearch.WordTrace]
  refine ⟨20824293754549512512688707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13882862503033008341792471 20824293754549512512688707)
  ·
    refine ⟨31236440631824268769033061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20824293754549512512688707 31236440631824268769033061)
    ·
      refine ⟨5856832618467050394193699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31236440631824268769033061 5856832618467050394193699)
      ·
        refine ⟨8785248927700575591290549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5856832618467050394193699 8785248927700575591290549)
        ·
          refine ⟨823617086971928961683489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8785248927700575591290549 823617086971928961683489)
          ·
            refine ⟨617712815228946721262617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 823617086971928961683489 617712815228946721262617)
            ·
              refine ⟨463284611421710040946963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 617712815228946721262617 463284611421710040946963)
              ·
                refine ⟨694926917132565061420445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463284611421710040946963 694926917132565061420445)
                ·
                  refine ⟨260597593924711898032667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 694926917132565061420445 260597593924711898032667)
                  ·
                    rfl

theorem cell20_570951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 3].length) (baseStart_570951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_570951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_570951 prefixEnd_570951 := by exact prefixLift 570951
  have htrace : WordTrace (prefixWord ++ tailWord_570951) baseStart_570951 baseEnd_570951 := by
    simpa [prefixWord, tailWord_570951, baseEnd_570951] using wordTrace_append hprefix tailTrace_570951
  have hstable : (prefixWord ++ tailWord_570951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570951).length < 2 ^ (prefixWord ++ tailWord_570951).sum := by decide
  have hdescent : baseEnd_570951 < baseStart_570951 := by decide
  rcases family_descends (prefixWord ++ tailWord_570951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571076 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 4]
def baseStart_571076 : Nat := 118140960795 + 571076 * 2 ^ 59
def prefixEnd_571076 : Nat := 4983230072969 + 3 ^ 40 * 571076 * 2
def baseEnd_571076 : Nat := 260654647330767018865489

theorem tailTrace_571076 : CollatzResearch.WordTrace tailWord_571076 prefixEnd_571076 260654647330767018865489 := by
  unfold tailWord_571076
  simp only [CollatzResearch.WordTrace]
  refine ⟨10414426439548329430494541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13885901919397772573992721 10414426439548329430494541)
  ·
    refine ⟨3905409914830623536435453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10414426439548329430494541 3905409914830623536435453)
    ·
      refine ⟨1464528718061483826163295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3905409914830623536435453 1464528718061483826163295)
      ·
        refine ⟨2196793077092225739244943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1464528718061483826163295 2196793077092225739244943)
        ·
          refine ⟨3295189615638338608867415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2196793077092225739244943 3295189615638338608867415)
          ·
            refine ⟨4942784423457507913301123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3295189615638338608867415 4942784423457507913301123)
            ·
              refine ⟨7414176635186261869951685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4942784423457507913301123 7414176635186261869951685)
              ·
                refine ⟨1390158119097424100615941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7414176635186261869951685 1390158119097424100615941)
                ·
                  refine ⟨260654647330767018865489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1390158119097424100615941 260654647330767018865489)
                  ·
                    rfl

theorem cell20_571076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_571076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571076 prefixEnd_571076 := by exact prefixLift 571076
  have htrace : WordTrace (prefixWord ++ tailWord_571076) baseStart_571076 baseEnd_571076 := by
    simpa [prefixWord, tailWord_571076, baseEnd_571076] using wordTrace_append hprefix tailTrace_571076
  have hstable : (prefixWord ++ tailWord_571076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571076).length < 2 ^ (prefixWord ++ tailWord_571076).sum := by decide
  have hdescent : baseEnd_571076 < baseStart_571076 := by decide
  rcases family_descends (prefixWord ++ tailWord_571076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571104 : List Nat := [2, 1, 1, 3, 1, 2, 10]
def baseStart_571104 : Nat := 118140960795 + 571104 * 2 ^ 59
def prefixEnd_571104 : Nat := 4983230072969 + 3 ^ 40 * 571104 * 2
def baseEnd_571104 : Nat := 28963047477080373992449

theorem tailTrace_571104 : CollatzResearch.WordTrace tailWord_571104 prefixEnd_571104 28963047477080373992449 := by
  unfold tailWord_571104
  simp only [CollatzResearch.WordTrace]
  refine ⟨10414937061497609821504183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13886582748663479762005577 10414937061497609821504183)
  ·
    refine ⟨15622405592246414732256275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10414937061497609821504183 15622405592246414732256275)
    ·
      refine ⟨23433608388369622098384413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15622405592246414732256275 23433608388369622098384413)
      ·
        refine ⟨8787603145638608286894155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23433608388369622098384413 8787603145638608286894155)
        ·
          refine ⟨13181404718457912430341233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8787603145638608286894155 13181404718457912430341233)
          ·
            refine ⟨9886053538843434322755925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13181404718457912430341233 9886053538843434322755925)
            ·
              refine ⟨28963047477080373992449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9886053538843434322755925 28963047477080373992449)
              ·
                rfl

theorem cell20_571104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 10].length) (baseStart_571104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571104 prefixEnd_571104 := by exact prefixLift 571104
  have htrace : WordTrace (prefixWord ++ tailWord_571104) baseStart_571104 baseEnd_571104 := by
    simpa [prefixWord, tailWord_571104, baseEnd_571104] using wordTrace_append hprefix tailTrace_571104
  have hstable : (prefixWord ++ tailWord_571104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571104).length < 2 ^ (prefixWord ++ tailWord_571104).sum := by decide
  have hdescent : baseEnd_571104 < baseStart_571104 := by decide
  rcases family_descends (prefixWord ++ tailWord_571104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571114 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_571114 : Nat := 118140960795 + 571114 * 2 ^ 59
def prefixEnd_571114 : Nat := 4983230072969 + 3 ^ 40 * 571114 * 2
def baseEnd_571114 : Nat := 260671991566207775598667

theorem tailTrace_571114 : CollatzResearch.WordTrace tailWord_571114 prefixEnd_571114 260671991566207775598667 := by
  unfold tailWord_571114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5207559713239747837718099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13886825901972660900581597 5207559713239747837718099)
  ·
    refine ⟨7811339569859621756577149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5207559713239747837718099 7811339569859621756577149)
    ·
      refine ⟨2929252338697358158716431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7811339569859621756577149 2929252338697358158716431)
      ·
        refine ⟨4393878508046037238074647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2929252338697358158716431 4393878508046037238074647)
        ·
          refine ⟨6590817762069055857111971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4393878508046037238074647 6590817762069055857111971)
          ·
            refine ⟨9886226643103583785667957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6590817762069055857111971 9886226643103583785667957)
            ·
              refine ⟨926833747790960979906371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9886226643103583785667957 926833747790960979906371)
              ·
                refine ⟨1390250621686441469859557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926833747790960979906371 1390250621686441469859557)
                ·
                  refine ⟨260671991566207775598667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1390250621686441469859557 260671991566207775598667)
                  ·
                    rfl

theorem cell20_571114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_571114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571114 prefixEnd_571114 := by exact prefixLift 571114
  have htrace : WordTrace (prefixWord ++ tailWord_571114) baseStart_571114 baseEnd_571114 := by
    simpa [prefixWord, tailWord_571114, baseEnd_571114] using wordTrace_append hprefix tailTrace_571114
  have hstable : (prefixWord ++ tailWord_571114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571114).length < 2 ^ (prefixWord ++ tailWord_571114).sum := by decide
  have hdescent : baseEnd_571114 < baseStart_571114 := by decide
  rcases family_descends (prefixWord ++ tailWord_571114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571121 : List Nat := [1, 2, 2, 2, 2, 4, 2, 5]
def baseStart_571121 : Nat := 118140960795 + 571121 * 2 ^ 59
def prefixEnd_571121 : Nat := 4983230072969 + 3 ^ 40 * 571121 * 2
def baseEnd_571121 : Nat := 86891728852315620788435

theorem tailTrace_571121 : CollatzResearch.WordTrace tailWord_571121 prefixEnd_571121 86891728852315620788435 := by
  unfold tailWord_571121
  simp only [CollatzResearch.WordTrace]
  refine ⟨20830494163933631546377217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13886996109289087697584811 20830494163933631546377217)
  ·
    refine ⟨15622870622950223659782913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20830494163933631546377217 15622870622950223659782913)
    ·
      refine ⟨11717152967212667744837185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15622870622950223659782913 11717152967212667744837185)
      ·
        refine ⟨8787864725409500808627889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11717152967212667744837185 8787864725409500808627889)
        ·
          refine ⟨6590898544057125606470917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8787864725409500808627889 6590898544057125606470917)
          ·
            refine ⟨1235793477010711051213297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6590898544057125606470917 1235793477010711051213297)
            ·
              refine ⟨926845107758033288409973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1235793477010711051213297 926845107758033288409973)
              ·
                refine ⟨86891728852315620788435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 926845107758033288409973 86891728852315620788435)
                ·
                  rfl

theorem cell20_571121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 5].length) (baseStart_571121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571121 prefixEnd_571121 := by exact prefixLift 571121
  have htrace : WordTrace (prefixWord ++ tailWord_571121) baseStart_571121 baseEnd_571121 := by
    simpa [prefixWord, tailWord_571121, baseEnd_571121] using wordTrace_append hprefix tailTrace_571121
  have hstable : (prefixWord ++ tailWord_571121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571121).length < 2 ^ (prefixWord ++ tailWord_571121).sum := by decide
  have hdescent : baseEnd_571121 < baseStart_571121 := by decide
  rcases family_descends (prefixWord ++ tailWord_571121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571135 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 4]
def baseStart_571135 : Nat := 118140960795 + 571135 * 2 ^ 59
def prefixEnd_571135 : Nat := 4983230072969 + 3 ^ 40 * 571135 * 2
def baseEnd_571135 : Nat := 260681576538425035898581

theorem tailTrace_571135 : CollatzResearch.WordTrace tailWord_571135 prefixEnd_571135 260681576538425035898581 := by
  unfold tailWord_571135
  simp only [CollatzResearch.WordTrace]
  refine ⟨20831004785882911937386859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13887336523921941291591239 20831004785882911937386859)
  ·
    refine ⟨31246507178824367906080289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20831004785882911937386859 31246507178824367906080289)
    ·
      refine ⟨23434880384118275929560217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31246507178824367906080289 23434880384118275929560217)
      ·
        refine ⟨17576160288088706947170163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23434880384118275929560217 17576160288088706947170163)
        ·
          refine ⟨26364240432133060420755245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17576160288088706947170163 26364240432133060420755245)
          ·
            refine ⟨9886590162049897657783217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26364240432133060420755245 9886590162049897657783217)
            ·
              refine ⟨7414942621537423243337413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9886590162049897657783217 7414942621537423243337413)
              ·
                refine ⟨1390301741538266858125765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7414942621537423243337413 1390301741538266858125765)
                ·
                  refine ⟨260681576538425035898581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1390301741538266858125765 260681576538425035898581)
                  ·
                    rfl

theorem cell20_571135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_571135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571135 prefixEnd_571135 := by exact prefixLift 571135
  have htrace : WordTrace (prefixWord ++ tailWord_571135) baseStart_571135 baseEnd_571135 := by
    simpa [prefixWord, tailWord_571135, baseEnd_571135] using wordTrace_append hprefix tailTrace_571135
  have hstable : (prefixWord ++ tailWord_571135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571135).length < 2 ^ (prefixWord ++ tailWord_571135).sum := by decide
  have hdescent : baseEnd_571135 < baseStart_571135 := by decide
  rcases family_descends (prefixWord ++ tailWord_571135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571169 : List Nat := [1, 2, 3, 2, 1, 4, 1, 4, 2]
def baseStart_571169 : Nat := 118140960795 + 571169 * 2 ^ 59
def prefixEnd_571169 : Nat := 4983230072969 + 3 ^ 40 * 571169 * 2
def baseEnd_571169 : Nat := 260697095064872028765109

theorem tailTrace_571169 : CollatzResearch.WordTrace tailWord_571169 prefixEnd_571169 260697095064872028765109 := by
  unfold tailWord_571169
  simp only [CollatzResearch.WordTrace]
  refine ⟨20832244867759735744124561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13888163245173157162749707 20832244867759735744124561)
  ·
    refine ⟨15624183650819801808093421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20832244867759735744124561 15624183650819801808093421)
    ·
      refine ⟨5859068869057425678035033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15624183650819801808093421 5859068869057425678035033)
      ·
        refine ⟨4394301651793069258526275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5859068869057425678035033 4394301651793069258526275)
        ·
          refine ⟨6591452477689603887789413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4394301651793069258526275 6591452477689603887789413)
          ·
            refine ⟨1235897339566800728960515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6591452477689603887789413 1235897339566800728960515)
            ·
              refine ⟨1853846009350201093440773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235897339566800728960515 1853846009350201093440773)
              ·
                refine ⟨347596126753162705020145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1853846009350201093440773 347596126753162705020145)
                ·
                  refine ⟨260697095064872028765109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347596126753162705020145 260697095064872028765109)
                  ·
                    rfl

theorem cell20_571169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 2].length) (baseStart_571169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571169 prefixEnd_571169 := by exact prefixLift 571169
  have htrace : WordTrace (prefixWord ++ tailWord_571169) baseStart_571169 baseEnd_571169 := by
    simpa [prefixWord, tailWord_571169, baseEnd_571169] using wordTrace_append hprefix tailTrace_571169
  have hstable : (prefixWord ++ tailWord_571169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571169).length < 2 ^ (prefixWord ++ tailWord_571169).sum := by decide
  have hdescent : baseEnd_571169 < baseStart_571169 := by decide
  rcases family_descends (prefixWord ++ tailWord_571169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571176 : List Nat := [2, 1, 5, 1, 1, 4, 1, 5]
def baseStart_571176 : Nat := 118140960795 + 571176 * 2 ^ 59
def prefixEnd_571176 : Nat := 4983230072969 + 3 ^ 40 * 571176 * 2
def baseEnd_571176 : Nat := 86900096685203705177249

theorem tailTrace_571176 : CollatzResearch.WordTrace tailWord_571176 prefixEnd_571176 86900096685203705177249 := by
  unfold tailWord_571176
  simp only [CollatzResearch.WordTrace]
  refine ⟨10416250089367187969814691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13888333452489583959752921 10416250089367187969814691)
  ·
    refine ⟨15624375134050781954722037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10416250089367187969814691 15624375134050781954722037)
    ·
      refine ⟨1464785168817260808255191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15624375134050781954722037 1464785168817260808255191)
      ·
        refine ⟨2197177753225891212382787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1464785168817260808255191 2197177753225891212382787)
        ·
          refine ⟨3295766629838836818574181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2197177753225891212382787 3295766629838836818574181)
          ·
            refine ⟨617956243094781903482659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3295766629838836818574181 617956243094781903482659)
            ·
              refine ⟨926934364642172855223989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617956243094781903482659 926934364642172855223989)
              ·
                refine ⟨86900096685203705177249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 926934364642172855223989 86900096685203705177249)
                ·
                  rfl

theorem cell20_571176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_571176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571176 prefixEnd_571176 := by exact prefixLift 571176
  have htrace : WordTrace (prefixWord ++ tailWord_571176) baseStart_571176 baseEnd_571176 := by
    simpa [prefixWord, tailWord_571176, baseEnd_571176] using wordTrace_append hprefix tailTrace_571176
  have hstable : (prefixWord ++ tailWord_571176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571176).length < 2 ^ (prefixWord ++ tailWord_571176).sum := by decide
  have hdescent : baseEnd_571176 < baseStart_571176 := by decide
  rcases family_descends (prefixWord ++ tailWord_571176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571193 : List Nat := [1, 2, 1, 7, 1, 1, 3, 4]
def baseStart_571193 : Nat := 118140960795 + 571193 * 2 ^ 59
def prefixEnd_571193 : Nat := 4983230072969 + 3 ^ 40 * 571193 * 2
def baseEnd_571193 : Nat := 86902683106278203988337

theorem tailTrace_571193 : CollatzResearch.WordTrace tailWord_571193 prefixEnd_571193 86902683106278203988337 := by
  unfold tailWord_571193
  simp only [CollatzResearch.WordTrace]
  refine ⟨20833120219672787842998233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13888746813115191895332155 20833120219672787842998233)
  ·
    refine ⟨15624840164754590882248675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20833120219672787842998233 15624840164754590882248675)
    ·
      refine ⟨23437260247131886323373013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15624840164754590882248675 23437260247131886323373013)
      ·
        refine ⟨549310787042153585704055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 23437260247131886323373013 549310787042153585704055)
        ·
          refine ⟨823966180563230378556083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549310787042153585704055 823966180563230378556083)
          ·
            refine ⟨1235949270844845567834125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823966180563230378556083 1235949270844845567834125)
            ·
              refine ⟨463480976566817087937797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1235949270844845567834125 463480976566817087937797)
              ·
                refine ⟨86902683106278203988337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 463480976566817087937797 86902683106278203988337)
                ·
                  rfl

theorem cell20_571193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 4].length) (baseStart_571193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571193 prefixEnd_571193 := by exact prefixLift 571193
  have htrace : WordTrace (prefixWord ++ tailWord_571193) baseStart_571193 baseEnd_571193 := by
    simpa [prefixWord, tailWord_571193, baseEnd_571193] using wordTrace_append hprefix tailTrace_571193
  have hstable : (prefixWord ++ tailWord_571193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571193).length < 2 ^ (prefixWord ++ tailWord_571193).sum := by decide
  have hdescent : baseEnd_571193 < baseStart_571193 := by decide
  rcases family_descends (prefixWord ++ tailWord_571193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571221 : List Nat := [1, 3, 2, 2, 2, 2, 3, 2, 3]
def baseStart_571221 : Nat := 118140960795 + 571221 * 2 ^ 59
def prefixEnd_571221 : Nat := 4983230072969 + 3 ^ 40 * 571221 * 2
def baseEnd_571221 : Nat := 260720829281790959031563

theorem tailTrace_571221 : CollatzResearch.WordTrace tailWord_571221 prefixEnd_571221 260720829281790959031563 := by
  unfold tailWord_571221
  simp only [CollatzResearch.WordTrace]
  refine ⟨20834141463571348625017517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13889427642380899083345011 20834141463571348625017517)
  ·
    refine ⟨7812803048839255734381569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20834141463571348625017517 7812803048839255734381569)
    ·
      refine ⟨5859602286629441800786177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7812803048839255734381569 5859602286629441800786177)
      ·
        refine ⟨4394701714972081350589633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5859602286629441800786177 4394701714972081350589633)
        ·
          refine ⟨3296026286229061012942225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4394701714972081350589633 3296026286229061012942225)
          ·
            refine ⟨2472019714671795759706669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3296026286229061012942225 2472019714671795759706669)
            ·
              refine ⟨927007393001923409890001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2472019714671795759706669 927007393001923409890001)
              ·
                refine ⟨695255544751442557417501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 927007393001923409890001 695255544751442557417501)
                ·
                  refine ⟨260720829281790959031563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 695255544751442557417501 260720829281790959031563)
                  ·
                    rfl

theorem cell20_571221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_571221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571221 prefixEnd_571221 := by exact prefixLift 571221
  have htrace : WordTrace (prefixWord ++ tailWord_571221) baseStart_571221 baseEnd_571221 := by
    simpa [prefixWord, tailWord_571221, baseEnd_571221] using wordTrace_append hprefix tailTrace_571221
  have hstable : (prefixWord ++ tailWord_571221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571221).length < 2 ^ (prefixWord ++ tailWord_571221).sum := by decide
  have hdescent : baseEnd_571221 < baseStart_571221 := by decide
  rcases family_descends (prefixWord ++ tailWord_571221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571249 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 4]
def baseStart_571249 : Nat := 118140960795 + 571249 * 2 ^ 59
def prefixEnd_571249 : Nat := 4983230072969 + 3 ^ 40 * 571249 * 2
def baseEnd_571249 : Nat := 260733609244747306098115

theorem tailTrace_571249 : CollatzResearch.WordTrace tailWord_571249 prefixEnd_571249 260733609244747306098115 := by
  unfold tailWord_571249
  simp only [CollatzResearch.WordTrace]
  refine ⟨20835162707469909407036801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13890108471646606271357867 20835162707469909407036801)
  ·
    refine ⟨15626372030602432055277601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20835162707469909407036801 15626372030602432055277601)
    ·
      refine ⟨11719779022951824041458201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15626372030602432055277601 11719779022951824041458201)
      ·
        refine ⟨8789834267213868031093651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11719779022951824041458201 8789834267213868031093651)
        ·
          refine ⟨13184751400820802046640477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8789834267213868031093651 13184751400820802046640477)
          ·
            refine ⟨4944281775307800767490179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13184751400820802046640477 4944281775307800767490179)
            ·
              refine ⟨7416422662961701151235269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4944281775307800767490179 7416422662961701151235269)
              ·
                refine ⟨1390579249305318965856613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7416422662961701151235269 1390579249305318965856613)
                ·
                  refine ⟨260733609244747306098115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1390579249305318965856613 260733609244747306098115)
                  ·
                    rfl

theorem cell20_571249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_571249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571249 prefixEnd_571249 := by exact prefixLift 571249
  have htrace : WordTrace (prefixWord ++ tailWord_571249) baseStart_571249 baseEnd_571249 := by
    simpa [prefixWord, tailWord_571249, baseEnd_571249] using wordTrace_append hprefix tailTrace_571249
  have hstable : (prefixWord ++ tailWord_571249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571249).length < 2 ^ (prefixWord ++ tailWord_571249).sum := by decide
  have hdescent : baseEnd_571249 < baseStart_571249 := by decide
  rcases family_descends (prefixWord ++ tailWord_571249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571286 : List Nat := [5, 3, 1, 1, 2, 1, 2, 5]
def baseStart_571286 : Nat := 118140960795 + 571286 * 2 ^ 59
def prefixEnd_571286 : Nat := 4983230072969 + 3 ^ 40 * 571286 * 2
def baseEnd_571286 : Nat := 86916832350979873954877

theorem tailTrace_571286 : CollatzResearch.WordTrace tailWord_571286 prefixEnd_571286 86916832350979873954877 := by
  unfold tailWord_571286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1302282013020991545383357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13891008138890576484089141 1302282013020991545383357)
  ·
    refine ⟨488355754882871829518759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1302282013020991545383357 488355754882871829518759)
    ·
      refine ⟨732533632324307744278139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 488355754882871829518759 732533632324307744278139)
      ·
        refine ⟨1098800448486461616417209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 732533632324307744278139 1098800448486461616417209)
        ·
          refine ⟨824100336364846212312907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1098800448486461616417209 824100336364846212312907)
          ·
            refine ⟨1236150504547269318469361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824100336364846212312907 1236150504547269318469361)
            ·
              refine ⟨927112878410451988852021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1236150504547269318469361 927112878410451988852021)
              ·
                refine ⟨86916832350979873954877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 927112878410451988852021 86916832350979873954877)
                ·
                  rfl

theorem cell20_571286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_571286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571286 prefixEnd_571286 := by exact prefixLift 571286
  have htrace : WordTrace (prefixWord ++ tailWord_571286) baseStart_571286 baseEnd_571286 := by
    simpa [prefixWord, tailWord_571286, baseEnd_571286] using wordTrace_append hprefix tailTrace_571286
  have hstable : (prefixWord ++ tailWord_571286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571286).length < 2 ^ (prefixWord ++ tailWord_571286).sum := by decide
  have hdescent : baseEnd_571286 < baseStart_571286 := by decide
  rcases family_descends (prefixWord ++ tailWord_571286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571332 : List Nat := [2, 3, 3, 12]
def baseStart_571332 : Nat := 118140960795 + 571332 * 2 ^ 59
def prefixEnd_571332 : Nat := 4983230072969 + 3 ^ 40 * 571332 * 2
def baseEnd_571332 : Nat := 1073133714841020190663

theorem tailTrace_571332 : CollatzResearch.WordTrace tailWord_571332 prefixEnd_571332 1073133714841020190663 := by
  unfold tailWord_571332
  simp only [CollatzResearch.WordTrace]
  refine ⟨10419094983084607291154125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13892126644112809721538833 10419094983084607291154125)
  ·
    refine ⟨3907160618656727734182797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10419094983084607291154125 3907160618656727734182797)
    ·
      refine ⟨1465185231996272900318549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3907160618656727734182797 1465185231996272900318549)
      ·
        refine ⟨1073133714841020190663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1465185231996272900318549 1073133714841020190663)
        ·
          rfl

theorem cell20_571332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 12].length) (baseStart_571332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571332 prefixEnd_571332 := by exact prefixLift 571332
  have htrace : WordTrace (prefixWord ++ tailWord_571332) baseStart_571332 baseEnd_571332 := by
    simpa [prefixWord, tailWord_571332, baseEnd_571332] using wordTrace_append hprefix tailTrace_571332
  have hstable : (prefixWord ++ tailWord_571332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571332).length < 2 ^ (prefixWord ++ tailWord_571332).sum := by decide
  have hdescent : baseEnd_571332 < baseStart_571332 := by decide
  rcases family_descends (prefixWord ++ tailWord_571332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571349 : List Nat := [1, 3, 2, 3, 2, 1, 3, 5]
def baseStart_571349 : Nat := 118140960795 + 571349 * 2 ^ 59
def prefixEnd_571349 : Nat := 4983230072969 + 3 ^ 40 * 571349 * 2
def baseEnd_571349 : Nat := 86926417323197134254791

theorem tailTrace_571349 : CollatzResearch.WordTrace tailWord_571349 prefixEnd_571349 86926417323197134254791 := by
  unfold tailWord_571349
  simp only [CollatzResearch.WordTrace]
  refine ⟨20838810007107626485677101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13892540004738417657118067 20838810007107626485677101)
  ·
    refine ⟨7814553752665359932128913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20838810007107626485677101 7814553752665359932128913)
    ·
      refine ⟨5860915314499019949096685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7814553752665359932128913 5860915314499019949096685)
      ·
        refine ⟨2197843242937132480911257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5860915314499019949096685 2197843242937132480911257)
        ·
          refine ⟨1648382432202849360683443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2197843242937132480911257 1648382432202849360683443)
          ·
            refine ⟨2472573648304274041025165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648382432202849360683443 2472573648304274041025165)
            ·
              refine ⟨927215118114102765384437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2472573648304274041025165 927215118114102765384437)
              ·
                refine ⟨86926417323197134254791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 927215118114102765384437 86926417323197134254791)
                ·
                  rfl

theorem cell20_571349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 5].length) (baseStart_571349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571349 prefixEnd_571349 := by exact prefixLift 571349
  have htrace : WordTrace (prefixWord ++ tailWord_571349) baseStart_571349 baseEnd_571349 := by
    simpa [prefixWord, tailWord_571349, baseEnd_571349] using wordTrace_append hprefix tailTrace_571349
  have hstable : (prefixWord ++ tailWord_571349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571349).length < 2 ^ (prefixWord ++ tailWord_571349).sum := by decide
  have hdescent : baseEnd_571349 < baseStart_571349 := by decide
  rcases family_descends (prefixWord ++ tailWord_571349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
