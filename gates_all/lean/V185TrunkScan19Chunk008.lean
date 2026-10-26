import V185TrunkScan19Chunk007

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_80778 : List Nat := [3, 1, 2, 4, 1, 2, 2, 4]
def baseStart_80778 : Nat := 118140960795 + 80778 * 2 ^ 59
def prefixEnd_80778 : Nat := 4983230072969 + 3 ^ 40 * 80778 * 2
def baseEnd_80778 : Nat := 24579520183105297424305

theorem tailTrace_80778 : CollatzResearch.WordTrace tailWord_80778 prefixEnd_80778 24579520183105297424305 := by
  unfold tailWord_80778
  simp only [CollatzResearch.WordTrace]
  refine ⟨736553925340644157292747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1964143800908384419447325 736553925340644157292747)
  ·
    refine ⟨1104830888010966235939121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 736553925340644157292747 1104830888010966235939121)
    ·
      refine ⟨828623166008224676954341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1104830888010966235939121 828623166008224676954341)
      ·
        refine ⟨155366843626542126928939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 828623166008224676954341 155366843626542126928939)
        ·
          refine ⟨233050265439813190393409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155366843626542126928939 233050265439813190393409)
          ·
            refine ⟨174787699079859892795057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233050265439813190393409 174787699079859892795057)
            ·
              refine ⟨131090774309894919596293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174787699079859892795057 131090774309894919596293)
              ·
                refine ⟨24579520183105297424305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131090774309894919596293 24579520183105297424305)
                ·
                  rfl

theorem cell19_80778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_80778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80778 prefixEnd_80778 := by exact prefixLift 80778
  have htrace : WordTrace (prefixWord ++ tailWord_80778) baseStart_80778 baseEnd_80778 := by
    simpa [prefixWord, tailWord_80778, baseEnd_80778] using wordTrace_append hprefix tailTrace_80778
  have hstable : (prefixWord ++ tailWord_80778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80778).length < 2 ^ (prefixWord ++ tailWord_80778).sum := by decide
  have hdescent : baseEnd_80778 < baseStart_80778 := by decide
  rcases family_descends (prefixWord ++ tailWord_80778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80799 : List Nat := [1, 1, 2, 5, 2, 1, 2, 5]
def baseStart_80799 : Nat := 118140960795 + 80799 * 2 ^ 59
def prefixEnd_80799 : Nat := 4983230072969 + 3 ^ 40 * 80799 * 2
def baseEnd_80799 : Nat := 24585910164583470957581

theorem tailTrace_80799 : CollatzResearch.WordTrace tailWord_80799 prefixEnd_80799 24585910164583470957581 := by
  unfold tailWord_80799
  simp only [CollatzResearch.WordTrace]
  refine ⟨2946981634286497215685451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1964654422857664810456967 2946981634286497215685451)
  ·
    refine ⟨4420472451429745823528177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2946981634286497215685451 4420472451429745823528177)
    ·
      refine ⟨3315354338572309367646133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4420472451429745823528177 3315354338572309367646133)
      ·
        refine ⟨310814469241154003216825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3315354338572309367646133 310814469241154003216825)
        ·
          refine ⟨233110851930865502412619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310814469241154003216825 233110851930865502412619)
          ·
            refine ⟨349666277896298253618929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233110851930865502412619 349666277896298253618929)
            ·
              refine ⟨262249708422223690214197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349666277896298253618929 262249708422223690214197)
              ·
                refine ⟨24585910164583470957581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 262249708422223690214197 24585910164583470957581)
                ·
                  rfl

theorem cell19_80799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_80799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80799 prefixEnd_80799 := by exact prefixLift 80799
  have htrace : WordTrace (prefixWord ++ tailWord_80799) baseStart_80799 baseEnd_80799 := by
    simpa [prefixWord, tailWord_80799, baseEnd_80799] using wordTrace_append hprefix tailTrace_80799
  have hstable : (prefixWord ++ tailWord_80799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80799).length < 2 ^ (prefixWord ++ tailWord_80799).sum := by decide
  have hdescent : baseEnd_80799 < baseStart_80799 := by decide
  rcases family_descends (prefixWord ++ tailWord_80799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80928 : List Nat := [2, 1, 1, 7, 2, 1, 5]
def baseStart_80928 : Nat := 118140960795 + 80928 * 2 ^ 59
def prefixEnd_80928 : Nat := 4983230072969 + 3 ^ 40 * 80928 * 2
def baseEnd_80928 : Nat := 8208387635983131363521

theorem tailTrace_80928 : CollatzResearch.WordTrace tailWord_80928 prefixEnd_80928 8208387635983131363521 := by
  unfold tailWord_80928
  simp only [CollatzResearch.WordTrace]
  refine ⟨1475843325409576123565719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1967791100546101498087625 1475843325409576123565719)
  ·
    refine ⟨2213764988114364185348579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1475843325409576123565719 2213764988114364185348579)
    ·
      refine ⟨3320647482171546278022869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2213764988114364185348579 3320647482171546278022869)
      ·
        refine ⟨77827675363395615891161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 3320647482171546278022869 77827675363395615891161)
        ·
          refine ⟨58370756522546711918371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77827675363395615891161 58370756522546711918371)
          ·
            refine ⟨87556134783820067877557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58370756522546711918371 87556134783820067877557)
            ·
              refine ⟨8208387635983131363521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87556134783820067877557 8208387635983131363521)
              ·
                rfl

theorem cell19_80928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 5].length) (baseStart_80928 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80928 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80928 prefixEnd_80928 := by exact prefixLift 80928
  have htrace : WordTrace (prefixWord ++ tailWord_80928) baseStart_80928 baseEnd_80928 := by
    simpa [prefixWord, tailWord_80928, baseEnd_80928] using wordTrace_append hprefix tailTrace_80928
  have hstable : (prefixWord ++ tailWord_80928).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80928).length < 2 ^ (prefixWord ++ tailWord_80928).sum := by decide
  have hdescent : baseEnd_80928 < baseStart_80928 := by decide
  rcases family_descends (prefixWord ++ tailWord_80928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80932 : List Nat := [2, 3, 1, 4, 1, 1, 7]
def baseStart_80932 : Nat := 118140960795 + 80932 * 2 ^ 59
def prefixEnd_80932 : Nat := 4983230072969 + 3 ^ 40 * 80932 * 2
def baseEnd_80932 : Nat := 8208793349092856667221

theorem tailTrace_80932 : CollatzResearch.WordTrace tailWord_80932 prefixEnd_80932 8208793349092856667221 := by
  unfold tailWord_80932
  simp only [CollatzResearch.WordTrace]
  refine ⟨1475916271402330465138525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1967888361869773953518033 1475916271402330465138525)
  ·
    refine ⟨553468601775873924426947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1475916271402330465138525 553468601775873924426947)
    ·
      refine ⟨830202902663810886640421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 553468601775873924426947 830202902663810886640421)
      ·
        refine ⟨155663044249464541245079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 830202902663810886640421 155663044249464541245079)
        ·
          refine ⟨233494566374196811867619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155663044249464541245079 233494566374196811867619)
          ·
            refine ⟨350241849561295217801429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233494566374196811867619 350241849561295217801429)
            ·
              refine ⟨8208793349092856667221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 350241849561295217801429 8208793349092856667221)
              ·
                rfl

theorem cell19_80932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 7].length) (baseStart_80932 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80932 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80932 prefixEnd_80932 := by exact prefixLift 80932
  have htrace : WordTrace (prefixWord ++ tailWord_80932) baseStart_80932 baseEnd_80932 := by
    simpa [prefixWord, tailWord_80932, baseEnd_80932] using wordTrace_append hprefix tailTrace_80932
  have hstable : (prefixWord ++ tailWord_80932).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80932).length < 2 ^ (prefixWord ++ tailWord_80932).sum := by decide
  have hdescent : baseEnd_80932 < baseStart_80932 := by decide
  rcases family_descends (prefixWord ++ tailWord_80932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80989 : List Nat := [1, 4, 4, 1, 9]
def baseStart_80989 : Nat := 118140960795 + 80989 * 2 ^ 59
def prefixEnd_80989 : Nat := 4983230072969 + 3 ^ 40 * 80989 * 2
def baseEnd_80989 : Nat := 912730528989604693883

theorem tailTrace_80989 : CollatzResearch.WordTrace tailWord_80989 prefixEnd_80989 912730528989604693883 := by
  unfold tailWord_80989
  simp only [CollatzResearch.WordTrace]
  refine ⟨2953911503598159665102021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1969274335732106443401347 2953911503598159665102021)
  ·
    refine ⟨553858406924654937206629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2953911503598159665102021 553858406924654937206629)
    ·
      refine ⟨103848451298372800726243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 553858406924654937206629 103848451298372800726243)
      ·
        refine ⟨155772676947559201089365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103848451298372800726243 155772676947559201089365)
        ·
          refine ⟨912730528989604693883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 155772676947559201089365 912730528989604693883)
          ·
            rfl

theorem cell19_80989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 9].length) (baseStart_80989 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_80989 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_80989 prefixEnd_80989 := by exact prefixLift 80989
  have htrace : WordTrace (prefixWord ++ tailWord_80989) baseStart_80989 baseEnd_80989 := by
    simpa [prefixWord, tailWord_80989, baseEnd_80989] using wordTrace_append hprefix tailTrace_80989
  have hstable : (prefixWord ++ tailWord_80989).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80989).length < 2 ^ (prefixWord ++ tailWord_80989).sum := by decide
  have hdescent : baseEnd_80989 < baseStart_80989 := by decide
  rcases family_descends (prefixWord ++ tailWord_80989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81006 : List Nat := [4, 1, 2, 2, 1, 4, 1, 4]
def baseStart_81006 : Nat := 118140960795 + 81006 * 2 ^ 59
def prefixEnd_81006 : Nat := 4983230072969 + 3 ^ 40 * 81006 * 2
def baseEnd_81006 : Nat := 24648897124868324357017

theorem tailTrace_81006 : CollatzResearch.WordTrace tailWord_81006 prefixEnd_81006 24648897124868324357017 := by
  unfold tailWord_81006
  simp only [CollatzResearch.WordTrace]
  refine ⟨369316443067071446058859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1969687696357714378980581 369316443067071446058859)
  ·
    refine ⟨553974664600607169088289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 369316443067071446058859 553974664600607169088289)
    ·
      refine ⟨415480998450455376816217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 553974664600607169088289 415480998450455376816217)
      ·
        refine ⟨311610748837841532612163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415480998450455376816217 311610748837841532612163)
        ·
          refine ⟨467416123256762298918245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311610748837841532612163 467416123256762298918245)
          ·
            refine ⟨87640523110642931047171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 467416123256762298918245 87640523110642931047171)
            ·
              refine ⟨131460784665964396570757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87640523110642931047171 131460784665964396570757)
              ·
                refine ⟨24648897124868324357017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131460784665964396570757 24648897124868324357017)
                ·
                  rfl

theorem cell19_81006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_81006 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81006 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81006 prefixEnd_81006 := by exact prefixLift 81006
  have htrace : WordTrace (prefixWord ++ tailWord_81006) baseStart_81006 baseEnd_81006 := by
    simpa [prefixWord, tailWord_81006, baseEnd_81006] using wordTrace_append hprefix tailTrace_81006
  have hstable : (prefixWord ++ tailWord_81006).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81006).length < 2 ^ (prefixWord ++ tailWord_81006).sum := by decide
  have hdescent : baseEnd_81006 < baseStart_81006 := by decide
  rcases family_descends (prefixWord ++ tailWord_81006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81025 : List Nat := [1, 2, 4, 2, 2, 2, 3, 3]
def baseStart_81025 : Nat := 118140960795 + 81025 * 2 ^ 59
def prefixEnd_81025 : Nat := 4983230072969 + 3 ^ 40 * 81025 * 2
def baseEnd_81025 : Nat := 24654678536681909934743

theorem tailTrace_81025 : CollatzResearch.WordTrace tailWord_81025 prefixEnd_81025 24654678536681909934743 := by
  unfold tailWord_81025
  simp only [CollatzResearch.WordTrace]
  refine ⟨2955224531467737813412529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1970149687645158542275019 2955224531467737813412529)
  ·
    refine ⟨2216418398600803360059397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2955224531467737813412529 2216418398600803360059397)
    ·
      refine ⟨415578449737650630011137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2216418398600803360059397 415578449737650630011137)
      ·
        refine ⟨311683837303237972508353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415578449737650630011137 311683837303237972508353)
        ·
          refine ⟨233762877977428479381265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311683837303237972508353 233762877977428479381265)
          ·
            refine ⟨175322158483071359535949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233762877977428479381265 175322158483071359535949)
            ·
              refine ⟨65745809431151759825981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175322158483071359535949 65745809431151759825981)
              ·
                refine ⟨24654678536681909934743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65745809431151759825981 24654678536681909934743)
                ·
                  rfl

theorem cell19_81025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 3].length) (baseStart_81025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81025 prefixEnd_81025 := by exact prefixLift 81025
  have htrace : WordTrace (prefixWord ++ tailWord_81025) baseStart_81025 baseEnd_81025 := by
    simpa [prefixWord, tailWord_81025, baseEnd_81025] using wordTrace_append hprefix tailTrace_81025
  have hstable : (prefixWord ++ tailWord_81025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81025).length < 2 ^ (prefixWord ++ tailWord_81025).sum := by decide
  have hdescent : baseEnd_81025 < baseStart_81025 := by decide
  rcases family_descends (prefixWord ++ tailWord_81025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81027 : List Nat := [1, 1, 1, 3, 3, 2, 5, 3]
def baseStart_81027 : Nat := 118140960795 + 81027 * 2 ^ 59
def prefixEnd_81027 : Nat := 4983230072969 + 3 ^ 40 * 81027 * 2
def baseEnd_81027 : Nat := 24655287106346497890293

theorem tailTrace_81027 : CollatzResearch.WordTrace tailWord_81027 prefixEnd_81027 24655287106346497890293 := by
  unfold tailWord_81027
  simp only [CollatzResearch.WordTrace]
  refine ⟨2955297477460492154985335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1970198318306994769990223 2955297477460492154985335)
  ·
    refine ⟨4432946216190738232478003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2955297477460492154985335 4432946216190738232478003)
    ·
      refine ⟨6649419324286107348717005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4432946216190738232478003 6649419324286107348717005)
      ·
        refine ⟨2493532246607290255768877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6649419324286107348717005 2493532246607290255768877)
        ·
          refine ⟨935074592477733845913329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2493532246607290255768877 935074592477733845913329)
          ·
            refine ⟨701305944358300384434997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 935074592477733845913329 701305944358300384434997)
            ·
              refine ⟨65747432283590661040781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 701305944358300384434997 65747432283590661040781)
              ·
                refine ⟨24655287106346497890293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65747432283590661040781 24655287106346497890293)
                ·
                  rfl

theorem cell19_81027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 3].length) (baseStart_81027 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81027 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81027 prefixEnd_81027 := by exact prefixLift 81027
  have htrace : WordTrace (prefixWord ++ tailWord_81027) baseStart_81027 baseEnd_81027 := by
    simpa [prefixWord, tailWord_81027, baseEnd_81027] using wordTrace_append hprefix tailTrace_81027
  have hstable : (prefixWord ++ tailWord_81027).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81027).length < 2 ^ (prefixWord ++ tailWord_81027).sum := by decide
  have hdescent : baseEnd_81027 < baseStart_81027 := by decide
  rcases family_descends (prefixWord ++ tailWord_81027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81084 : List Nat := [2, 2, 2, 3, 2, 2, 1, 5]
def baseStart_81084 : Nat := 118140960795 + 81084 * 2 ^ 59
def prefixEnd_81084 : Nat := 4983230072969 + 3 ^ 40 * 81084 * 2
def baseEnd_81084 : Nat := 24672631341787254623471

theorem tailTrace_81084 : CollatzResearch.WordTrace tailWord_81084 prefixEnd_81084 24672631341787254623471 := by
  unfold tailWord_81084
  simp only [CollatzResearch.WordTrace]
  refine ⟨1478688219126995444905153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1971584292169327259873537 1478688219126995444905153)
  ·
    refine ⟨1109016164345246583678865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1478688219126995444905153 1109016164345246583678865)
    ·
      refine ⟨831762123258934937759149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1109016164345246583678865 831762123258934937759149)
      ·
        refine ⟨311910796222100601659681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 831762123258934937759149 311910796222100601659681)
        ·
          refine ⟨233933097166575451244761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311910796222100601659681 233933097166575451244761)
          ·
            refine ⟨175449822874931588433571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233933097166575451244761 175449822874931588433571)
            ·
              refine ⟨263174734312397382650357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175449822874931588433571 263174734312397382650357)
              ·
                refine ⟨24672631341787254623471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 263174734312397382650357 24672631341787254623471)
                ·
                  rfl

theorem cell19_81084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_81084 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81084 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81084 prefixEnd_81084 := by exact prefixLift 81084
  have htrace : WordTrace (prefixWord ++ tailWord_81084) baseStart_81084 baseEnd_81084 := by
    simpa [prefixWord, tailWord_81084, baseEnd_81084] using wordTrace_append hprefix tailTrace_81084
  have hstable : (prefixWord ++ tailWord_81084).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81084).length < 2 ^ (prefixWord ++ tailWord_81084).sum := by decide
  have hdescent : baseEnd_81084 < baseStart_81084 := by decide
  rcases family_descends (prefixWord ++ tailWord_81084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81124 : List Nat := [2, 3, 1, 1, 1, 2, 3, 6]
def baseStart_81124 : Nat := 118140960795 + 81124 * 2 ^ 59
def prefixEnd_81124 : Nat := 4983230072969 + 3 ^ 40 * 81124 * 2
def baseEnd_81124 : Nat := 24684802735079013734473

theorem tailTrace_81124 : CollatzResearch.WordTrace tailWord_81124 prefixEnd_81124 24684802735079013734473 := by
  unfold tailWord_81124
  simp only [CollatzResearch.WordTrace]
  refine ⟨1479417679054538860633213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1972556905406051814177617 1479417679054538860633213)
  ·
    refine ⟨554781629645452072737455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1479417679054538860633213 554781629645452072737455)
    ·
      refine ⟨832172444468178109106183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 554781629645452072737455 832172444468178109106183)
      ·
        refine ⟨1248258666702267163659275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 832172444468178109106183 1248258666702267163659275)
        ·
          refine ⟨1872388000053400745488913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248258666702267163659275 1872388000053400745488913)
          ·
            refine ⟨1404291000040050559116685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1872388000053400745488913 1404291000040050559116685)
            ·
              refine ⟨526609125015018959668757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1404291000040050559116685 526609125015018959668757)
              ·
                refine ⟨24684802735079013734473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 526609125015018959668757 24684802735079013734473)
                ·
                  rfl

theorem cell19_81124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_81124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81124 prefixEnd_81124 := by exact prefixLift 81124
  have htrace : WordTrace (prefixWord ++ tailWord_81124) baseStart_81124 baseEnd_81124 := by
    simpa [prefixWord, tailWord_81124, baseEnd_81124] using wordTrace_append hprefix tailTrace_81124
  have hstable : (prefixWord ++ tailWord_81124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81124).length < 2 ^ (prefixWord ++ tailWord_81124).sum := by decide
  have hdescent : baseEnd_81124 < baseStart_81124 := by decide
  rcases family_descends (prefixWord ++ tailWord_81124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81160 : List Nat := [2, 1, 3, 2, 5, 6]
def baseStart_81160 : Nat := 118140960795 + 81160 * 2 ^ 59
def prefixEnd_81160 : Nat := 4983230072969 + 3 ^ 40 * 81160 * 2
def baseEnd_81160 : Nat := 2743972998782399659375

theorem tailTrace_81160 : CollatzResearch.WordTrace tailWord_81160 prefixEnd_81160 2743972998782399659375 := by
  unfold tailWord_81160
  simp only [CollatzResearch.WordTrace]
  refine ⟨1480074192989327934788467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1973432257319103913051289 1480074192989327934788467)
  ·
    refine ⟨2220111289483991902182701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1480074192989327934788467 2220111289483991902182701)
    ·
      refine ⟨832541733556496963318513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2220111289483991902182701 832541733556496963318513)
      ·
        refine ⟨624406300167372722488885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 832541733556496963318513 624406300167372722488885)
        ·
          refine ⟨58538090640691192733333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 624406300167372722488885 58538090640691192733333)
          ·
            refine ⟨2743972998782399659375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58538090640691192733333 2743972998782399659375)
            ·
              rfl

theorem cell19_81160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 6].length) (baseStart_81160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81160 prefixEnd_81160 := by exact prefixLift 81160
  have htrace : WordTrace (prefixWord ++ tailWord_81160) baseStart_81160 baseEnd_81160 := by
    simpa [prefixWord, tailWord_81160, baseEnd_81160] using wordTrace_append hprefix tailTrace_81160
  have hstable : (prefixWord ++ tailWord_81160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81160).length < 2 ^ (prefixWord ++ tailWord_81160).sum := by decide
  have hdescent : baseEnd_81160 < baseStart_81160 := by decide
  rcases family_descends (prefixWord ++ tailWord_81160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81217 : List Nat := [1, 2, 5, 2, 1, 2, 6]
def baseStart_81217 : Nat := 118140960795 + 81217 * 2 ^ 59
def prefixEnd_81217 : Nat := 4983230072969 + 3 ^ 40 * 81217 * 2
def baseEnd_81217 : Nat := 8237700408160784555851

theorem tailTrace_81217 : CollatzResearch.WordTrace tailWord_81217 prefixEnd_81217 8237700408160784555851 := by
  unfold tailWord_81217
  simp only [CollatzResearch.WordTrace]
  refine ⟨2962227346772154604401905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1974818231181436402934603 2962227346772154604401905)
  ·
    refine ⟨2221670510079115953301429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2962227346772154604401905 2221670510079115953301429)
    ·
      refine ⟨208281610319917120622009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2221670510079115953301429 208281610319917120622009)
      ·
        refine ⟨156211207739937840466507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208281610319917120622009 156211207739937840466507)
        ·
          refine ⟨234316811609906760699761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156211207739937840466507 234316811609906760699761)
          ·
            refine ⟨175737608707430070524821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234316811609906760699761 175737608707430070524821)
            ·
              refine ⟨8237700408160784555851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 175737608707430070524821 8237700408160784555851)
              ·
                rfl

theorem cell19_81217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 6].length) (baseStart_81217 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81217 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81217 prefixEnd_81217 := by exact prefixLift 81217
  have htrace : WordTrace (prefixWord ++ tailWord_81217) baseStart_81217 baseEnd_81217 := by
    simpa [prefixWord, tailWord_81217, baseEnd_81217] using wordTrace_append hprefix tailTrace_81217
  have hstable : (prefixWord ++ tailWord_81217).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81217).length < 2 ^ (prefixWord ++ tailWord_81217).sum := by decide
  have hdescent : baseEnd_81217 < baseStart_81217 := by decide
  rcases family_descends (prefixWord ++ tailWord_81217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81255 : List Nat := [1, 1, 5, 1, 4, 1, 1, 5]
def baseStart_81255 : Nat := 118140960795 + 81255 * 2 ^ 59
def prefixEnd_81255 : Nat := 4983230072969 + 3 ^ 40 * 81255 * 2
def baseEnd_81255 : Nat := 24724664048109524823005

theorem tailTrace_81255 : CollatzResearch.WordTrace tailWord_81255 prefixEnd_81255 24724664048109524823005 := by
  unfold tailWord_81255
  simp only [CollatzResearch.WordTrace]
  refine ⟨2963613320634487094285219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1975742213756324729523479 2963613320634487094285219)
  ·
    refine ⟨4445419980951730641427829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2963613320634487094285219 4445419980951730641427829)
    ·
      refine ⟨416758123214224747633859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4445419980951730641427829 416758123214224747633859)
      ·
        refine ⟨625137184821337121450789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416758123214224747633859 625137184821337121450789)
        ·
          refine ⟨117213222154000710272023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 625137184821337121450789 117213222154000710272023)
          ·
            refine ⟨175819833231001065408035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117213222154000710272023 175819833231001065408035)
            ·
              refine ⟨263729749846501598112053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175819833231001065408035 263729749846501598112053)
              ·
                refine ⟨24724664048109524823005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 263729749846501598112053 24724664048109524823005)
                ·
                  rfl

theorem cell19_81255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_81255 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81255 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81255 prefixEnd_81255 := by exact prefixLift 81255
  have htrace : WordTrace (prefixWord ++ tailWord_81255) baseStart_81255 baseEnd_81255 := by
    simpa [prefixWord, tailWord_81255, baseEnd_81255] using wordTrace_append hprefix tailTrace_81255
  have hstable : (prefixWord ++ tailWord_81255).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81255).length < 2 ^ (prefixWord ++ tailWord_81255).sum := by decide
  have hdescent : baseEnd_81255 < baseStart_81255 := by decide
  rcases family_descends (prefixWord ++ tailWord_81255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81333 : List Nat := [1, 3, 3, 2, 2, 8]
def baseStart_81333 : Nat := 118140960795 + 81333 * 2 ^ 59
def prefixEnd_81333 : Nat := 4983230072969 + 3 ^ 40 * 81333 * 2
def baseEnd_81333 : Nat := 2749822029447606121051

theorem tailTrace_81333 : CollatzResearch.WordTrace tailWord_81333 prefixEnd_81333 2749822029447606121051 := by
  unfold tailWord_81333
  simp only [CollatzResearch.WordTrace]
  refine ⟨2966458214351906415624653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1977638809567937610416435 2966458214351906415624653)
  ·
    refine ⟨1112421830381964905859245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2966458214351906415624653 1112421830381964905859245)
    ·
      refine ⟨417158186393236839697217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1112421830381964905859245 417158186393236839697217)
      ·
        refine ⟨312868639794927629772913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417158186393236839697217 312868639794927629772913)
        ·
          refine ⟨234651479846195722329685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312868639794927629772913 234651479846195722329685)
          ·
            refine ⟨2749822029447606121051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 234651479846195722329685 2749822029447606121051)
            ·
              rfl

theorem cell19_81333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 8].length) (baseStart_81333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81333 prefixEnd_81333 := by exact prefixLift 81333
  have htrace : WordTrace (prefixWord ++ tailWord_81333) baseStart_81333 baseEnd_81333 := by
    simpa [prefixWord, tailWord_81333, baseEnd_81333] using wordTrace_append hprefix tailTrace_81333
  have hstable : (prefixWord ++ tailWord_81333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81333).length < 2 ^ (prefixWord ++ tailWord_81333).sum := by decide
  have hdescent : baseEnd_81333 < baseStart_81333 := by decide
  rcases family_descends (prefixWord ++ tailWord_81333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81348 : List Nat := [2, 3, 3, 2, 1, 3, 1, 4]
def baseStart_81348 : Nat := 118140960795 + 81348 * 2 ^ 59
def prefixEnd_81348 : Nat := 4983230072969 + 3 ^ 40 * 81348 * 2
def baseEnd_81348 : Nat := 24752962537512864756085

theorem tailTrace_81348 : CollatzResearch.WordTrace tailWord_81348 prefixEnd_81348 24752962537512864756085 := by
  unfold tailWord_81348
  simp only [CollatzResearch.WordTrace]
  refine ⟨1483502654648781988710349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1978003539531709318280465 1483502654648781988710349)
  ·
    refine ⟨556313495493293245766381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1483502654648781988710349 556313495493293245766381)
    ·
      refine ⟨208617560809984967162393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 556313495493293245766381 208617560809984967162393)
      ·
        refine ⟨156463170607488725371795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208617560809984967162393 156463170607488725371795)
        ·
          refine ⟨234694755911233088057693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156463170607488725371795 234694755911233088057693)
          ·
            refine ⟨88010533466712408021635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234694755911233088057693 88010533466712408021635)
            ·
              refine ⟨132015800200068612032453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88010533466712408021635 132015800200068612032453)
              ·
                refine ⟨24752962537512864756085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132015800200068612032453 24752962537512864756085)
                ·
                  rfl

theorem cell19_81348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_81348 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81348 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81348 prefixEnd_81348 := by exact prefixLift 81348
  have htrace : WordTrace (prefixWord ++ tailWord_81348) baseStart_81348 baseEnd_81348 := by
    simpa [prefixWord, tailWord_81348, baseEnd_81348] using wordTrace_append hprefix tailTrace_81348
  have hstable : (prefixWord ++ tailWord_81348).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81348).length < 2 ^ (prefixWord ++ tailWord_81348).sum := by decide
  have hdescent : baseEnd_81348 < baseStart_81348 := by decide
  rcases family_descends (prefixWord ++ tailWord_81348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81369 : List Nat := [1, 2, 1, 2, 4, 3, 3, 3]
def baseStart_81369 : Nat := 118140960795 + 81369 * 2 ^ 59
def prefixEnd_81369 : Nat := 4983230072969 + 3 ^ 40 * 81369 * 2
def baseEnd_81369 : Nat := 24759352518991038289361

theorem tailTrace_81369 : CollatzResearch.WordTrace tailWord_81369 prefixEnd_81369 24759352518991038289361 := by
  unfold tailWord_81369
  simp only [CollatzResearch.WordTrace]
  refine ⟨2967771242221484563935161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1978514161480989709290107 2967771242221484563935161)
  ·
    refine ⟨2225828431666113422951371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2967771242221484563935161 2225828431666113422951371)
    ·
      refine ⟨3338742647499170134427057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2225828431666113422951371 3338742647499170134427057)
      ·
        refine ⟨2504056985624377600820293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3338742647499170134427057 2504056985624377600820293)
        ·
          refine ⟨469510684804570800153805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2504056985624377600820293 469510684804570800153805)
          ·
            refine ⟨176066506801714050057677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 469510684804570800153805 176066506801714050057677)
            ·
              refine ⟨66024940050642768771629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176066506801714050057677 66024940050642768771629)
              ·
                refine ⟨24759352518991038289361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66024940050642768771629 24759352518991038289361)
                ·
                  rfl

theorem cell19_81369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 3].length) (baseStart_81369 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81369 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81369 prefixEnd_81369 := by exact prefixLift 81369
  have htrace : WordTrace (prefixWord ++ tailWord_81369) baseStart_81369 baseEnd_81369 := by
    simpa [prefixWord, tailWord_81369, baseEnd_81369] using wordTrace_append hprefix tailTrace_81369
  have hstable : (prefixWord ++ tailWord_81369).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81369).length < 2 ^ (prefixWord ++ tailWord_81369).sum := by decide
  have hdescent : baseEnd_81369 < baseStart_81369 := by decide
  rcases family_descends (prefixWord ++ tailWord_81369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81390 : List Nat := [4, 1, 2, 1, 2, 1, 8]
def baseStart_81390 : Nat := 118140960795 + 81390 * 2 ^ 59
def prefixEnd_81390 : Nat := 4983230072969 + 3 ^ 40 * 81390 * 2
def baseEnd_81390 : Nat := 8255247500156403940879

theorem tailTrace_81390 : CollatzResearch.WordTrace tailWord_81390 prefixEnd_81390 8255247500156403940879 := by
  unfold tailWord_81390
  simp only [CollatzResearch.WordTrace]
  refine ⟨371067146893175643806203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1979024783430270100299749 371067146893175643806203)
  ·
    refine ⟨556600720339763465709305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 371067146893175643806203 556600720339763465709305)
    ·
      refine ⟨417450540254822599281979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 556600720339763465709305 417450540254822599281979)
      ·
        refine ⟨626175810382233898922969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417450540254822599281979 626175810382233898922969)
        ·
          refine ⟨469631857786675424192227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 626175810382233898922969 469631857786675424192227)
          ·
            refine ⟨704447786680013136288341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469631857786675424192227 704447786680013136288341)
            ·
              refine ⟨8255247500156403940879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 704447786680013136288341 8255247500156403940879)
              ·
                rfl

theorem cell19_81390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 8].length) (baseStart_81390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81390 prefixEnd_81390 := by exact prefixLift 81390
  have htrace : WordTrace (prefixWord ++ tailWord_81390) baseStart_81390 baseEnd_81390 := by
    simpa [prefixWord, tailWord_81390, baseEnd_81390] using wordTrace_append hprefix tailTrace_81390
  have hstable : (prefixWord ++ tailWord_81390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81390).length < 2 ^ (prefixWord ++ tailWord_81390).sum := by decide
  have hdescent : baseEnd_81390 < baseStart_81390 := by decide
  rcases family_descends (prefixWord ++ tailWord_81390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81422 : List Nat := [4, 1, 1, 2, 5, 1, 2, 3]
def baseStart_81422 : Nat := 118140960795 + 81422 * 2 ^ 59
def prefixEnd_81422 : Nat := 4983230072969 + 3 ^ 40 * 81422 * 2
def baseEnd_81422 : Nat := 24775479615102619111439

theorem tailTrace_81422 : CollatzResearch.WordTrace tailWord_81422 prefixEnd_81422 24775479615102619111439 := by
  unfold tailWord_81422
  simp only [CollatzResearch.WordTrace]
  refine ⟨371213038878684326951815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1979802874019649743743013 371213038878684326951815)
  ·
    refine ⟨556819558318026490427723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 371213038878684326951815 556819558318026490427723)
    ·
      refine ⟨835229337477039735641585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 556819558318026490427723 835229337477039735641585)
      ·
        refine ⟨626422003107779801731189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 835229337477039735641585 626422003107779801731189)
        ·
          refine ⟨58727062791354356412299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 626422003107779801731189 58727062791354356412299)
          ·
            refine ⟨88090594187031534618449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58727062791354356412299 88090594187031534618449)
            ·
              refine ⟨66067945640273650963837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88090594187031534618449 66067945640273650963837)
              ·
                refine ⟨24775479615102619111439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66067945640273650963837 24775479615102619111439)
                ·
                  rfl

theorem cell19_81422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_81422 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81422 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81422 prefixEnd_81422 := by exact prefixLift 81422
  have htrace : WordTrace (prefixWord ++ tailWord_81422) baseStart_81422 baseEnd_81422 := by
    simpa [prefixWord, tailWord_81422, baseEnd_81422] using wordTrace_append hprefix tailTrace_81422
  have hstable : (prefixWord ++ tailWord_81422).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81422).length < 2 ^ (prefixWord ++ tailWord_81422).sum := by decide
  have hdescent : baseEnd_81422 < baseStart_81422 := by decide
  rcases family_descends (prefixWord ++ tailWord_81422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81462 : List Nat := [5, 1, 2, 1, 3, 1, 2, 4]
def baseStart_81462 : Nat := 118140960795 + 81462 * 2 ^ 59
def prefixEnd_81462 : Nat := 4983230072969 + 3 ^ 40 * 81462 * 2
def baseEnd_81462 : Nat := 24787651008394378222441

theorem tailTrace_81462 : CollatzResearch.WordTrace tailWord_81462 prefixEnd_81462 24787651008394378222441 := by
  unfold tailWord_81462
  simp only [CollatzResearch.WordTrace]
  refine ⟨185697701930285090441915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1980775487256374298047093 185697701930285090441915)
  ·
    refine ⟨278546552895427635662873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185697701930285090441915 278546552895427635662873)
    ·
      refine ⟨208909914671570726747155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278546552895427635662873 208909914671570726747155)
      ·
        refine ⟨313364872007356090120733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208909914671570726747155 313364872007356090120733)
        ·
          refine ⟨117511827002758533795275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313364872007356090120733 117511827002758533795275)
          ·
            refine ⟨176267740504137800692913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117511827002758533795275 176267740504137800692913)
            ·
              refine ⟨132200805378103350519685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176267740504137800692913 132200805378103350519685)
              ·
                refine ⟨24787651008394378222441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132200805378103350519685 24787651008394378222441)
                ·
                  rfl

theorem cell19_81462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_81462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81462 prefixEnd_81462 := by exact prefixLift 81462
  have htrace : WordTrace (prefixWord ++ tailWord_81462) baseStart_81462 baseEnd_81462 := by
    simpa [prefixWord, tailWord_81462, baseEnd_81462] using wordTrace_append hprefix tailTrace_81462
  have hstable : (prefixWord ++ tailWord_81462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81462).length < 2 ^ (prefixWord ++ tailWord_81462).sum := by decide
  have hdescent : baseEnd_81462 < baseStart_81462 := by decide
  rcases family_descends (prefixWord ++ tailWord_81462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81466 : List Nat := [3, 1, 1, 1, 3, 2, 4, 4]
def baseStart_81466 : Nat := 118140960795 + 81466 * 2 ^ 59
def prefixEnd_81466 : Nat := 4983230072969 + 3 ^ 40 * 81466 * 2
def baseEnd_81466 : Nat := 24788868147723554133541

theorem tailTrace_81466 : CollatzResearch.WordTrace tailWord_81466 prefixEnd_81466 24788868147723554133541 := by
  unfold tailWord_81466
  simp only [CollatzResearch.WordTrace]
  refine ⟨742827280717517532554063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1980872748580046753477501 742827280717517532554063)
  ·
    refine ⟨1114240921076276298831095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 742827280717517532554063 1114240921076276298831095)
    ·
      refine ⟨1671361381614414448246643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1114240921076276298831095 1671361381614414448246643)
      ·
        refine ⟨2507042072421621672369965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1671361381614414448246643 2507042072421621672369965)
        ·
          refine ⟨940140777158108127138737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2507042072421621672369965 940140777158108127138737)
          ·
            refine ⟨705105582868581095354053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 940140777158108127138737 705105582868581095354053)
            ·
              refine ⟨132207296787858955378885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 705105582868581095354053 132207296787858955378885)
              ·
                refine ⟨24788868147723554133541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132207296787858955378885 24788868147723554133541)
                ·
                  rfl

theorem cell19_81466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_81466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81466 prefixEnd_81466 := by exact prefixLift 81466
  have htrace : WordTrace (prefixWord ++ tailWord_81466) baseStart_81466 baseEnd_81466 := by
    simpa [prefixWord, tailWord_81466, baseEnd_81466] using wordTrace_append hprefix tailTrace_81466
  have hstable : (prefixWord ++ tailWord_81466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81466).length < 2 ^ (prefixWord ++ tailWord_81466).sum := by decide
  have hdescent : baseEnd_81466 < baseStart_81466 := by decide
  rcases family_descends (prefixWord ++ tailWord_81466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81502 : List Nat := [4, 4, 1, 10]
def baseStart_81502 : Nat := 118140960795 + 81502 * 2 ^ 59
def prefixEnd_81502 : Nat := 4983230072969 + 3 ^ 40 * 81502 * 2
def baseEnd_81502 : Nat := 306170646934396757203

theorem tailTrace_81502 : CollatzResearch.WordTrace tailWord_81502 prefixEnd_81502 306170646934396757203 := by
  unfold tailWord_81502
  simp only [CollatzResearch.WordTrace]
  refine ⟨371577768842456034815845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1981748100493098852351173 371577768842456034815845)
  ·
    refine ⟨69670831657960506527971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 371577768842456034815845 69670831657960506527971)
    ·
      refine ⟨104506247486940759791957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69670831657960506527971 104506247486940759791957)
      ·
        refine ⟨306170646934396757203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 104506247486940759791957 306170646934396757203)
        ·
          rfl

theorem cell19_81502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 10].length) (baseStart_81502 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81502 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81502 prefixEnd_81502 := by exact prefixLift 81502
  have htrace : WordTrace (prefixWord ++ tailWord_81502) baseStart_81502 baseEnd_81502 := by
    simpa [prefixWord, tailWord_81502, baseEnd_81502] using wordTrace_append hprefix tailTrace_81502
  have hstable : (prefixWord ++ tailWord_81502).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81502).length < 2 ^ (prefixWord ++ tailWord_81502).sum := by decide
  have hdescent : baseEnd_81502 < baseStart_81502 := by decide
  rcases family_descends (prefixWord ++ tailWord_81502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81618 : List Nat := [3, 2, 2, 2, 2, 1, 7]
def baseStart_81618 : Nat := 118140960795 + 81618 * 2 ^ 59
def prefixEnd_81618 : Nat := 4983230072969 + 3 ^ 40 * 81618 * 2
def baseEnd_81618 : Nat := 8278373147410746251783

theorem tailTrace_81618 : CollatzResearch.WordTrace tailWord_81618 prefixEnd_81618 8278373147410746251783 := by
  unfold tailWord_81618
  simp only [CollatzResearch.WordTrace]
  refine ⟨744213254579850022437377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1984568678879600059833005 744213254579850022437377)
  ·
    refine ⟨558159940934887516828033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 744213254579850022437377 558159940934887516828033)
    ·
      refine ⟨418619955701165637621025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 558159940934887516828033 418619955701165637621025)
      ·
        refine ⟨313964966775874228215769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 418619955701165637621025 313964966775874228215769)
        ·
          refine ⟨235473725081905671161827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313964966775874228215769 235473725081905671161827)
          ·
            refine ⟨353210587622858506742741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235473725081905671161827 353210587622858506742741)
            ·
              refine ⟨8278373147410746251783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 353210587622858506742741 8278373147410746251783)
              ·
                rfl

theorem cell19_81618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 7].length) (baseStart_81618 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81618 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81618 prefixEnd_81618 := by exact prefixLift 81618
  have htrace : WordTrace (prefixWord ++ tailWord_81618) baseStart_81618 baseEnd_81618 := by
    simpa [prefixWord, tailWord_81618, baseEnd_81618] using wordTrace_append hprefix tailTrace_81618
  have hstable : (prefixWord ++ tailWord_81618).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81618).length < 2 ^ (prefixWord ++ tailWord_81618).sum := by decide
  have hdescent : baseEnd_81618 < baseStart_81618 := by decide
  rcases family_descends (prefixWord ++ tailWord_81618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81635 : List Nat := [1, 1, 1, 7, 2, 1, 2, 4]
def baseStart_81635 : Nat := 118140960795 + 81635 * 2 ^ 59
def prefixEnd_81635 : Nat := 4983230072969 + 3 ^ 40 * 81635 * 2
def baseEnd_81635 : Nat := 24840292284381236377525

theorem tailTrace_81635 : CollatzResearch.WordTrace tailWord_81635 prefixEnd_81635 24840292284381236377525 := by
  unfold tailWord_81635
  simp only [CollatzResearch.WordTrace]
  refine ⟨2977473059257811993118359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1984982039505207995412239 2977473059257811993118359)
  ·
    refine ⟨4466209588886717989677539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2977473059257811993118359 4466209588886717989677539)
    ·
      refine ⟨6699314383330076984516309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4466209588886717989677539 6699314383330076984516309)
      ·
        refine ⟨157015180859298679324601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 6699314383330076984516309 157015180859298679324601)
        ·
          refine ⟨117761385644474009493451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157015180859298679324601 117761385644474009493451)
          ·
            refine ⟨176642078466711014240177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117761385644474009493451 176642078466711014240177)
            ·
              refine ⟨132481558850033260680133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176642078466711014240177 132481558850033260680133)
              ·
                refine ⟨24840292284381236377525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132481558850033260680133 24840292284381236377525)
                ·
                  rfl

theorem cell19_81635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_81635 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81635 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81635 prefixEnd_81635 := by exact prefixLift 81635
  have htrace : WordTrace (prefixWord ++ tailWord_81635) baseStart_81635 baseEnd_81635 := by
    simpa [prefixWord, tailWord_81635, baseEnd_81635] using wordTrace_append hprefix tailTrace_81635
  have hstable : (prefixWord ++ tailWord_81635).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81635).length < 2 ^ (prefixWord ++ tailWord_81635).sum := by decide
  have hdescent : baseEnd_81635 < baseStart_81635 := by decide
  rcases family_descends (prefixWord ++ tailWord_81635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81637 : List Nat := [1, 3, 1, 4, 1, 1, 4, 4]
def baseStart_81637 : Nat := 118140960795 + 81637 * 2 ^ 59
def prefixEnd_81637 : Nat := 4983230072969 + 3 ^ 40 * 81637 * 2
def baseEnd_81637 : Nat := 24840900854045824333075

theorem tailTrace_81637 : CollatzResearch.WordTrace tailWord_81637 prefixEnd_81637 24840900854045824333075 := by
  unfold tailWord_81637
  simp only [CollatzResearch.WordTrace]
  refine ⟨2977546005250566334691165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1985030670167044223127443 2977546005250566334691165)
  ·
    refine ⟨1116579751968962375509187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2977546005250566334691165 1116579751968962375509187)
    ·
      refine ⟨1674869627953443563263781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1116579751968962375509187 1674869627953443563263781)
      ·
        refine ⟨314038055241270668111959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1674869627953443563263781 314038055241270668111959)
        ·
          refine ⟨471057082861906002167939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314038055241270668111959 471057082861906002167939)
          ·
            refine ⟨706585624292859003251909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471057082861906002167939 706585624292859003251909)
            ·
              refine ⟨132484804554911063109733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 706585624292859003251909 132484804554911063109733)
              ·
                refine ⟨24840900854045824333075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132484804554911063109733 24840900854045824333075)
                ·
                  rfl

theorem cell19_81637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_81637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81637 prefixEnd_81637 := by exact prefixLift 81637
  have htrace : WordTrace (prefixWord ++ tailWord_81637) baseStart_81637 baseEnd_81637 := by
    simpa [prefixWord, tailWord_81637, baseEnd_81637] using wordTrace_append hprefix tailTrace_81637
  have hstable : (prefixWord ++ tailWord_81637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81637).length < 2 ^ (prefixWord ++ tailWord_81637).sum := by decide
  have hdescent : baseEnd_81637 < baseStart_81637 := by decide
  rcases family_descends (prefixWord ++ tailWord_81637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81652 : List Nat := [2, 6, 1, 1, 1, 1, 2, 5]
def baseStart_81652 : Nat := 118140960795 + 81652 * 2 ^ 59
def prefixEnd_81652 : Nat := 4983230072969 + 3 ^ 40 * 81652 * 2
def baseEnd_81652 : Nat := 24845465126530233999701

theorem tailTrace_81652 : CollatzResearch.WordTrace tailWord_81652 prefixEnd_81652 24845465126530233999701 := by
  unfold tailWord_81652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1489046550098111948243605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1985395400130815930991473 1489046550098111948243605)
  ·
    refine ⟨69799057035848997573919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1489046550098111948243605 69799057035848997573919)
    ·
      refine ⟨104698585553773496360879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69799057035848997573919 104698585553773496360879)
      ·
        refine ⟨157047878330660244541319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104698585553773496360879 157047878330660244541319)
        ·
          refine ⟨235571817495990366811979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157047878330660244541319 235571817495990366811979)
          ·
            refine ⟨353357726243985550217969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235571817495990366811979 353357726243985550217969)
            ·
              refine ⟨265018294682989162663477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353357726243985550217969 265018294682989162663477)
              ·
                refine ⟨24845465126530233999701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 265018294682989162663477 24845465126530233999701)
                ·
                  rfl

theorem cell19_81652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_81652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81652 prefixEnd_81652 := by exact prefixLift 81652
  have htrace : WordTrace (prefixWord ++ tailWord_81652) baseStart_81652 baseEnd_81652 := by
    simpa [prefixWord, tailWord_81652, baseEnd_81652] using wordTrace_append hprefix tailTrace_81652
  have hstable : (prefixWord ++ tailWord_81652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81652).length < 2 ^ (prefixWord ++ tailWord_81652).sum := by decide
  have hdescent : baseEnd_81652 < baseStart_81652 := by decide
  rcases family_descends (prefixWord ++ tailWord_81652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81753 : List Nat := [1, 2, 1, 2, 2, 3, 2, 6]
def baseStart_81753 : Nat := 118140960795 + 81753 * 2 ^ 59
def prefixEnd_81753 : Nat := 4983230072969 + 3 ^ 40 * 81753 * 2
def baseEnd_81753 : Nat := 24876197894591925754981

theorem tailTrace_81753 : CollatzResearch.WordTrace tailWord_81753 prefixEnd_81753 24876197894591925754981 := by
  unfold tailWord_81753
  simp only [CollatzResearch.WordTrace]
  refine ⟨2981776872830318145913913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1987851248553545430609275 2981776872830318145913913)
  ·
    refine ⟨2236332654622738609435435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2981776872830318145913913 2236332654622738609435435)
    ·
      refine ⟨3354498981934107914153153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2236332654622738609435435 3354498981934107914153153)
      ·
        refine ⟨2515874236450580935614865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3354498981934107914153153 2515874236450580935614865)
        ·
          refine ⟨1886905677337935701711149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2515874236450580935614865 1886905677337935701711149)
          ·
            refine ⟨707589629001725888141681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1886905677337935701711149 707589629001725888141681)
            ·
              refine ⟨530692221751294416106261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 707589629001725888141681 530692221751294416106261)
              ·
                refine ⟨24876197894591925754981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 530692221751294416106261 24876197894591925754981)
                ·
                  rfl

theorem cell19_81753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_81753 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81753 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81753 prefixEnd_81753 := by exact prefixLift 81753
  have htrace : WordTrace (prefixWord ++ tailWord_81753) baseStart_81753 baseEnd_81753 := by
    simpa [prefixWord, tailWord_81753, baseEnd_81753] using wordTrace_append hprefix tailTrace_81753
  have hstable : (prefixWord ++ tailWord_81753).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81753).length < 2 ^ (prefixWord ++ tailWord_81753).sum := by decide
  have hdescent : baseEnd_81753 < baseStart_81753 := by decide
  rcases family_descends (prefixWord ++ tailWord_81753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81844 : List Nat := [2, 5, 2, 1, 2, 7]
def baseStart_81844 : Nat := 118140960795 + 81844 * 2 ^ 59
def prefixEnd_81844 : Nat := 4983230072969 + 3 ^ 40 * 81844 * 2
def baseEnd_81844 : Nat := 2767098646036741970279

theorem tailTrace_81844 : CollatzResearch.WordTrace tailWord_81844 prefixEnd_81844 2767098646036741970279 := by
  unfold tailWord_81844
  simp only [CollatzResearch.WordTrace]
  refine ⟨1492547957750320343738293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1990063943667093791651057 1492547957750320343738293)
  ·
    refine ⟨139926371039092532225465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1492547957750320343738293 139926371039092532225465)
    ·
      refine ⟨104944778279319399169099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139926371039092532225465 104944778279319399169099)
      ·
        refine ⟨157417167418979098753649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104944778279319399169099 157417167418979098753649)
        ·
          refine ⟨118062875564234324065237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157417167418979098753649 118062875564234324065237)
          ·
            refine ⟨2767098646036741970279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 118062875564234324065237 2767098646036741970279)
            ·
              rfl

theorem cell19_81844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 7].length) (baseStart_81844 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81844 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81844 prefixEnd_81844 := by exact prefixLift 81844
  have htrace : WordTrace (prefixWord ++ tailWord_81844) baseStart_81844 baseEnd_81844 := by
    simpa [prefixWord, tailWord_81844, baseEnd_81844] using wordTrace_append hprefix tailTrace_81844
  have hstable : (prefixWord ++ tailWord_81844).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81844).length < 2 ^ (prefixWord ++ tailWord_81844).sum := by decide
  have hdescent : baseEnd_81844 < baseStart_81844 := by decide
  rcases family_descends (prefixWord ++ tailWord_81844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81882 : List Nat := [3, 1, 1, 2, 5, 1, 3, 3]
def baseStart_81882 : Nat := 118140960795 + 81882 * 2 ^ 59
def prefixEnd_81882 : Nat := 4983230072969 + 3 ^ 40 * 81882 * 2
def baseEnd_81882 : Nat := 24915450637957848887963

theorem tailTrace_81882 : CollatzResearch.WordTrace tailWord_81882 prefixEnd_81882 24915450637957848887963 := by
  unfold tailWord_81882
  simp only [CollatzResearch.WordTrace]
  refine ⟨746620472340743294339975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1990987926241982118239933 746620472340743294339975)
  ·
    refine ⟨1119930708511114941509963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 746620472340743294339975 1119930708511114941509963)
    ·
      refine ⟨1679896062766672412264945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1119930708511114941509963 1679896062766672412264945)
      ·
        refine ⟨1259922047075004309198709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1679896062766672412264945 1259922047075004309198709)
        ·
          refine ⟨118117691913281653987379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1259922047075004309198709 118117691913281653987379)
          ·
            refine ⟨177176537869922480981069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118117691913281653987379 177176537869922480981069)
            ·
              refine ⟨66441201701220930367901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177176537869922480981069 66441201701220930367901)
              ·
                refine ⟨24915450637957848887963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66441201701220930367901 24915450637957848887963)
                ·
                  rfl

theorem cell19_81882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_81882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81882 prefixEnd_81882 := by exact prefixLift 81882
  have htrace : WordTrace (prefixWord ++ tailWord_81882) baseStart_81882 baseEnd_81882 := by
    simpa [prefixWord, tailWord_81882, baseEnd_81882] using wordTrace_append hprefix tailTrace_81882
  have hstable : (prefixWord ++ tailWord_81882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81882).length < 2 ^ (prefixWord ++ tailWord_81882).sum := by decide
  have hdescent : baseEnd_81882 < baseStart_81882 := by decide
  rcases family_descends (prefixWord ++ tailWord_81882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81901 : List Nat := [1, 5, 1, 4, 1, 1, 6]
def baseStart_81901 : Nat := 118140960795 + 81901 * 2 ^ 59
def prefixEnd_81901 : Nat := 4983230072969 + 3 ^ 40 * 81901 * 2
def baseEnd_81901 : Nat := 8307077349923811488563

theorem tailTrace_81901 : CollatzResearch.WordTrace tailWord_81901 prefixEnd_81901 8307077349923811488563 := by
  unfold tailWord_81901
  simp only [CollatzResearch.WordTrace]
  refine ⟨2987174876294139422301557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1991449917529426281534371 2987174876294139422301557)
  ·
    refine ⟨280047644652575570840771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2987174876294139422301557 280047644652575570840771)
    ·
      refine ⟨420071466978863356261157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280047644652575570840771 420071466978863356261157)
      ·
        refine ⟨78763400058536879298967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 420071466978863356261157 78763400058536879298967)
        ·
          refine ⟨118145100087805318948451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78763400058536879298967 118145100087805318948451)
          ·
            refine ⟨177217650131707978422677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118145100087805318948451 177217650131707978422677)
            ·
              refine ⟨8307077349923811488563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177217650131707978422677 8307077349923811488563)
              ·
                rfl

theorem cell19_81901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 6].length) (baseStart_81901 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81901 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81901 prefixEnd_81901 := by exact prefixLift 81901
  have htrace : WordTrace (prefixWord ++ tailWord_81901) baseStart_81901 baseEnd_81901 := by
    simpa [prefixWord, tailWord_81901, baseEnd_81901] using wordTrace_append hprefix tailTrace_81901
  have hstable : (prefixWord ++ tailWord_81901).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81901).length < 2 ^ (prefixWord ++ tailWord_81901).sum := by decide
  have hdescent : baseEnd_81901 < baseStart_81901 := by decide
  rcases family_descends (prefixWord ++ tailWord_81901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81933 : List Nat := [1, 7, 1, 2, 1, 2, 2, 3]
def baseStart_81933 : Nat := 118140960795 + 81933 * 2 ^ 59
def prefixEnd_81933 : Nat := 4983230072969 + 3 ^ 40 * 81933 * 2
def baseEnd_81933 : Nat := 24930969164404841754491

theorem tailTrace_81933 : CollatzResearch.WordTrace tailWord_81933 prefixEnd_81933 24930969164404841754491 := by
  unfold tailWord_81933
  simp only [CollatzResearch.WordTrace]
  refine ⟨2988342012178208887466453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1992228008118805924977635 2988342012178208887466453)
  ·
    refine ⟨70039265910426770799995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 2988342012178208887466453 70039265910426770799995)
    ·
      refine ⟨105058898865640156199993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70039265910426770799995 105058898865640156199993)
      ·
        refine ⟨78794174149230117149995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105058898865640156199993 78794174149230117149995)
        ·
          refine ⟨118191261223845175724993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78794174149230117149995 118191261223845175724993)
          ·
            refine ⟨88643445917883881793745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118191261223845175724993 88643445917883881793745)
            ·
              refine ⟨66482584438412911345309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88643445917883881793745 66482584438412911345309)
              ·
                refine ⟨24930969164404841754491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66482584438412911345309 24930969164404841754491)
                ·
                  rfl

theorem cell19_81933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 3].length) (baseStart_81933 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81933 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81933 prefixEnd_81933 := by exact prefixLift 81933
  have htrace : WordTrace (prefixWord ++ tailWord_81933) baseStart_81933 baseEnd_81933 := by
    simpa [prefixWord, tailWord_81933, baseEnd_81933] using wordTrace_append hprefix tailTrace_81933
  have hstable : (prefixWord ++ tailWord_81933).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81933).length < 2 ^ (prefixWord ++ tailWord_81933).sum := by decide
  have hdescent : baseEnd_81933 < baseStart_81933 := by decide
  rcases family_descends (prefixWord ++ tailWord_81933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81941 : List Nat := [1, 3, 2, 1, 5, 1, 1, 5]
def baseStart_81941 : Nat := 118140960795 + 81941 * 2 ^ 59
def prefixEnd_81941 : Nat := 4983230072969 + 3 ^ 40 * 81941 * 2
def baseEnd_81941 : Nat := 24933403443063193576691

theorem tailTrace_81941 : CollatzResearch.WordTrace tailWord_81941 prefixEnd_81941 24933403443063193576691 := by
  unfold tailWord_81941
  simp only [CollatzResearch.WordTrace]
  refine ⟨2988633796149226253757677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1992422530766150835838451 2988633796149226253757677)
  ·
    refine ⟨1120737673555959845159129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2988633796149226253757677 1120737673555959845159129)
    ·
      refine ⟨840553255166969883869347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1120737673555959845159129 840553255166969883869347)
      ·
        refine ⟨1260829882750454825804021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840553255166969883869347 1260829882750454825804021)
        ·
          refine ⟨118202801507855139919127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1260829882750454825804021 118202801507855139919127)
          ·
            refine ⟨177304202261782709878691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118202801507855139919127 177304202261782709878691)
            ·
              refine ⟨265956303392674064818037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177304202261782709878691 265956303392674064818037)
              ·
                refine ⟨24933403443063193576691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 265956303392674064818037 24933403443063193576691)
                ·
                  rfl

theorem cell19_81941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_81941 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_81941 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_81941 prefixEnd_81941 := by exact prefixLift 81941
  have htrace : WordTrace (prefixWord ++ tailWord_81941) baseStart_81941 baseEnd_81941 := by
    simpa [prefixWord, tailWord_81941, baseEnd_81941] using wordTrace_append hprefix tailTrace_81941
  have hstable : (prefixWord ++ tailWord_81941).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81941).length < 2 ^ (prefixWord ++ tailWord_81941).sum := by decide
  have hdescent : baseEnd_81941 < baseStart_81941 := by decide
  rcases family_descends (prefixWord ++ tailWord_81941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82074 : List Nat := [3, 1, 1, 5, 2, 1, 6]
def baseStart_82074 : Nat := 118140960795 + 82074 * 2 ^ 59
def prefixEnd_82074 : Nat := 4983230072969 + 3 ^ 40 * 82074 * 2
def baseEnd_82074 : Nat := 8324624441919430873591

theorem tailTrace_82074 : CollatzResearch.WordTrace tailWord_82074 prefixEnd_82074 8324624441919430873591 := by
  unfold tailWord_82074
  simp only [CollatzResearch.WordTrace]
  refine ⟨748371176166847492087319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1995656469778259978899517 748371176166847492087319)
  ·
    refine ⟨1122556764250271238130979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 748371176166847492087319 1122556764250271238130979)
    ·
      refine ⟨1683835146375406857196469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1122556764250271238130979 1683835146375406857196469)
      ·
        refine ⟨157859544972694392862169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1683835146375406857196469 157859544972694392862169)
        ·
          refine ⟨118394658729520794646627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157859544972694392862169 118394658729520794646627)
          ·
            refine ⟨177591988094281191969941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118394658729520794646627 177591988094281191969941)
            ·
              refine ⟨8324624441919430873591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177591988094281191969941 8324624441919430873591)
              ·
                rfl

theorem cell19_82074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 6].length) (baseStart_82074 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82074 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82074 prefixEnd_82074 := by exact prefixLift 82074
  have htrace : WordTrace (prefixWord ++ tailWord_82074) baseStart_82074 baseEnd_82074 := by
    simpa [prefixWord, tailWord_82074, baseEnd_82074] using wordTrace_append hprefix tailTrace_82074
  have hstable : (prefixWord ++ tailWord_82074).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82074).length < 2 ^ (prefixWord ++ tailWord_82074).sum := by decide
  have hdescent : baseEnd_82074 < baseStart_82074 := by decide
  rcases family_descends (prefixWord ++ tailWord_82074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82076 : List Nat := [2, 2, 3, 2, 1, 1, 8]
def baseStart_82076 : Nat := 118140960795 + 82076 * 2 ^ 59
def prefixEnd_82076 : Nat := 4983230072969 + 3 ^ 40 * 82076 * 2
def baseEnd_82076 : Nat := 8324827298474293525441

theorem tailTrace_82076 : CollatzResearch.WordTrace tailWord_82076 prefixEnd_82076 8324827298474293525441 := by
  unfold tailWord_82076
  simp only [CollatzResearch.WordTrace]
  refine ⟨1496778825330072154961041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1995705100440096206614721 1496778825330072154961041)
  ·
    refine ⟨1122584118997554116220781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1496778825330072154961041 1122584118997554116220781)
    ·
      refine ⟨420969044624082793582793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1122584118997554116220781 420969044624082793582793)
      ·
        refine ⟨315726783468062095187095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420969044624082793582793 315726783468062095187095)
        ·
          refine ⟨473590175202093142780643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315726783468062095187095 473590175202093142780643)
          ·
            refine ⟨710385262803139714170965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473590175202093142780643 710385262803139714170965)
            ·
              refine ⟨8324827298474293525441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 710385262803139714170965 8324827298474293525441)
              ·
                rfl

theorem cell19_82076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 8].length) (baseStart_82076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82076 prefixEnd_82076 := by exact prefixLift 82076
  have htrace : WordTrace (prefixWord ++ tailWord_82076) baseStart_82076 baseEnd_82076 := by
    simpa [prefixWord, tailWord_82076, baseEnd_82076] using wordTrace_append hprefix tailTrace_82076
  have hstable : (prefixWord ++ tailWord_82076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82076).length < 2 ^ (prefixWord ++ tailWord_82076).sum := by decide
  have hdescent : baseEnd_82076 < baseStart_82076 := by decide
  rcases family_descends (prefixWord ++ tailWord_82076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82108 : List Nat := [2, 2, 2, 3, 4, 1, 2, 3]
def baseStart_82108 : Nat := 118140960795 + 82108 * 2 ^ 59
def prefixEnd_82108 : Nat := 4983230072969 + 3 ^ 40 * 82108 * 2
def baseEnd_82108 : Nat := 24984219010056287865125

theorem tailTrace_82108 : CollatzResearch.WordTrace tailWord_82108 prefixEnd_82108 24984219010056287865125 := by
  unfold tailWord_82108
  simp only [CollatzResearch.WordTrace]
  refine ⟨1497362393272106887543489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1996483191029475850057985 1497362393272106887543489)
  ·
    refine ⟨1123021794954080165657617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1497362393272106887543489 1123021794954080165657617)
    ·
      refine ⟨842266346215560124243213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1123021794954080165657617 842266346215560124243213)
      ·
        refine ⟨315849879830835046591205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 842266346215560124243213 315849879830835046591205)
        ·
          refine ⟨59221852468281571235851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 315849879830835046591205 59221852468281571235851)
          ·
            refine ⟨88832778702422356853777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59221852468281571235851 88832778702422356853777)
            ·
              refine ⟨66624584026816767640333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88832778702422356853777 66624584026816767640333)
              ·
                refine ⟨24984219010056287865125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66624584026816767640333 24984219010056287865125)
                ·
                  rfl

theorem cell19_82108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_82108 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82108 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82108 prefixEnd_82108 := by exact prefixLift 82108
  have htrace : WordTrace (prefixWord ++ tailWord_82108) baseStart_82108 baseEnd_82108 := by
    simpa [prefixWord, tailWord_82108, baseEnd_82108] using wordTrace_append hprefix tailTrace_82108
  have hstable : (prefixWord ++ tailWord_82108).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82108).length < 2 ^ (prefixWord ++ tailWord_82108).sum := by decide
  have hdescent : baseEnd_82108 < baseStart_82108 := by decide
  rcases family_descends (prefixWord ++ tailWord_82108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82112 : List Nat := [2, 1, 1, 2, 5, 1, 4, 3]
def baseStart_82112 : Nat := 118140960795 + 82112 * 2 ^ 59
def prefixEnd_82112 : Nat := 4983230072969 + 3 ^ 40 * 82112 * 2
def baseEnd_82112 : Nat := 24985436149385463776225

theorem tailTrace_82112 : CollatzResearch.WordTrace tailWord_82112 prefixEnd_82112 24985436149385463776225 := by
  unfold tailWord_82112
  simp only [CollatzResearch.WordTrace]
  refine ⟨1497435339264861229116295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1996580452353148305488393 1497435339264861229116295)
  ·
    refine ⟨2246153008897291843674443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1497435339264861229116295 2246153008897291843674443)
    ·
      refine ⟨3369229513345937765511665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2246153008897291843674443 3369229513345937765511665)
      ·
        refine ⟨2526922135009453324133749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3369229513345937765511665 2526922135009453324133749)
        ·
          refine ⟨236898950157136249137539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2526922135009453324133749 236898950157136249137539)
          ·
            refine ⟨355348425235704373706309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236898950157136249137539 355348425235704373706309)
            ·
              refine ⟨66627829731694570069933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 355348425235704373706309 66627829731694570069933)
              ·
                refine ⟨24985436149385463776225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66627829731694570069933 24985436149385463776225)
                ·
                  rfl

theorem cell19_82112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_82112 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82112 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82112 prefixEnd_82112 := by exact prefixLift 82112
  have htrace : WordTrace (prefixWord ++ tailWord_82112) baseStart_82112 baseEnd_82112 := by
    simpa [prefixWord, tailWord_82112, baseEnd_82112] using wordTrace_append hprefix tailTrace_82112
  have hstable : (prefixWord ++ tailWord_82112).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82112).length < 2 ^ (prefixWord ++ tailWord_82112).sum := by decide
  have hdescent : baseEnd_82112 < baseStart_82112 := by decide
  rcases family_descends (prefixWord ++ tailWord_82112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82152 : List Nat := [2, 1, 4, 1, 2, 2, 1, 6]
def baseStart_82152 : Nat := 118140960795 + 82152 * 2 ^ 59
def prefixEnd_82152 : Nat := 4983230072969 + 3 ^ 40 * 82152 * 2
def baseEnd_82152 : Nat := 24997607542677222887227

theorem tailTrace_82152 : CollatzResearch.WordTrace tailWord_82152 prefixEnd_82152 24997607542677222887227 := by
  unfold tailWord_82152
  simp only [CollatzResearch.WordTrace]
  refine ⟨1498164799192404644844355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1997553065589872859792473 1498164799192404644844355)
  ·
    refine ⟨2247247198788606967266533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1498164799192404644844355 2247247198788606967266533)
    ·
      refine ⟨421358849772863806362475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2247247198788606967266533 421358849772863806362475)
      ·
        refine ⟨632038274659295709543713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421358849772863806362475 632038274659295709543713)
        ·
          refine ⟨474028705994471782157785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 632038274659295709543713 474028705994471782157785)
          ·
            refine ⟨355521529495853836618339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474028705994471782157785 355521529495853836618339)
            ·
              refine ⟨533282294243780754927509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355521529495853836618339 533282294243780754927509)
              ·
                refine ⟨24997607542677222887227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 533282294243780754927509 24997607542677222887227)
                ·
                  rfl

theorem cell19_82152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_82152 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82152 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82152 prefixEnd_82152 := by exact prefixLift 82152
  have htrace : WordTrace (prefixWord ++ tailWord_82152) baseStart_82152 baseEnd_82152 := by
    simpa [prefixWord, tailWord_82152, baseEnd_82152] using wordTrace_append hprefix tailTrace_82152
  have hstable : (prefixWord ++ tailWord_82152).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82152).length < 2 ^ (prefixWord ++ tailWord_82152).sum := by decide
  have hdescent : baseEnd_82152 < baseStart_82152 := by decide
  rcases family_descends (prefixWord ++ tailWord_82152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82205 : List Nat := [1, 4, 2, 3, 2, 2, 1, 4]
def baseStart_82205 : Nat := 118140960795 + 82205 * 2 ^ 59
def prefixEnd_82205 : Nat := 4983230072969 + 3 ^ 40 * 82205 * 2
def baseEnd_82205 : Nat := 25013734638788803709305

theorem tailTrace_82205 : CollatzResearch.WordTrace tailWord_82205 prefixEnd_82205 25013734638788803709305 := by
  unfold tailWord_82205
  simp only [CollatzResearch.WordTrace]
  refine ⟨2998262667192799341368069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1998841778128532894245379 2998262667192799341368069)
  ·
    refine ⟨562174250098649876506513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2998262667192799341368069 562174250098649876506513)
    ·
      refine ⟨421630687573987407379885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 562174250098649876506513 421630687573987407379885)
      ·
        refine ⟨158111507840245277767457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421630687573987407379885 158111507840245277767457)
        ·
          refine ⟨118583630880183958325593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158111507840245277767457 118583630880183958325593)
          ·
            refine ⟨88937723160137968744195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118583630880183958325593 88937723160137968744195)
            ·
              refine ⟨133406584740206953116293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88937723160137968744195 133406584740206953116293)
              ·
                refine ⟨25013734638788803709305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133406584740206953116293 25013734638788803709305)
                ·
                  rfl

theorem cell19_82205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 4].length) (baseStart_82205 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82205 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82205 prefixEnd_82205 := by exact prefixLift 82205
  have htrace : WordTrace (prefixWord ++ tailWord_82205) baseStart_82205 baseEnd_82205 := by
    simpa [prefixWord, tailWord_82205, baseEnd_82205] using wordTrace_append hprefix tailTrace_82205
  have hstable : (prefixWord ++ tailWord_82205).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82205).length < 2 ^ (prefixWord ++ tailWord_82205).sum := by decide
  have hdescent : baseEnd_82205 < baseStart_82205 := by decide
  rcases family_descends (prefixWord ++ tailWord_82205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82207 : List Nat := [1, 1, 2, 4, 3, 3, 1, 4]
def baseStart_82207 : Nat := 118140960795 + 82207 * 2 ^ 59
def prefixEnd_82207 : Nat := 4983230072969 + 3 ^ 40 * 82207 * 2
def baseEnd_82207 : Nat := 25014343208453391664855

theorem tailTrace_82207 : CollatzResearch.WordTrace tailWord_82207 prefixEnd_82207 25014343208453391664855 := by
  unfold tailWord_82207
  simp only [CollatzResearch.WordTrace]
  refine ⟨2998335613185553682940875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1998890408790369121960583 2998335613185553682940875)
  ·
    refine ⟨4497503419778330524411313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2998335613185553682940875 4497503419778330524411313)
    ·
      refine ⟨3373127564833747893308485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4497503419778330524411313 3373127564833747893308485)
      ·
        refine ⟨632461418406327729995341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3373127564833747893308485 632461418406327729995341)
        ·
          refine ⟨237173031902372898748253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 632461418406327729995341 237173031902372898748253)
          ·
            refine ⟨88939886963389837030595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237173031902372898748253 88939886963389837030595)
            ·
              refine ⟨133409830445084755545893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88939886963389837030595 133409830445084755545893)
              ·
                refine ⟨25014343208453391664855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133409830445084755545893 25014343208453391664855)
                ·
                  rfl

theorem cell19_82207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 4].length) (baseStart_82207 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82207 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82207 prefixEnd_82207 := by exact prefixLift 82207
  have htrace : WordTrace (prefixWord ++ tailWord_82207) baseStart_82207 baseEnd_82207 := by
    simpa [prefixWord, tailWord_82207, baseEnd_82207] using wordTrace_append hprefix tailTrace_82207
  have hstable : (prefixWord ++ tailWord_82207).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82207).length < 2 ^ (prefixWord ++ tailWord_82207).sum := by decide
  have hdescent : baseEnd_82207 < baseStart_82207 := by decide
  rcases family_descends (prefixWord ++ tailWord_82207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82209 : List Nat := [1, 2, 3, 2, 1, 1, 5, 4]
def baseStart_82209 : Nat := 118140960795 + 82209 * 2 ^ 59
def prefixEnd_82209 : Nat := 4983230072969 + 3 ^ 40 * 82209 * 2
def baseEnd_82209 : Nat := 25014951778117979620405

theorem tailTrace_82209 : CollatzResearch.WordTrace tailWord_82209 prefixEnd_82209 25014951778117979620405 := by
  unfold tailWord_82209
  simp only [CollatzResearch.WordTrace]
  refine ⟨2998408559178308024513681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1998939039452205349675787 2998408559178308024513681)
  ·
    refine ⟨2248806419383731018385261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2998408559178308024513681 2248806419383731018385261)
    ·
      refine ⟨843302407268899131894473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2248806419383731018385261 843302407268899131894473)
      ·
        refine ⟨632476805451674348920855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 843302407268899131894473 632476805451674348920855)
        ·
          refine ⟨948715208177511523381283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632476805451674348920855 948715208177511523381283)
          ·
            refine ⟨1423072812266267285071925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948715208177511523381283 1423072812266267285071925)
            ·
              refine ⟨133413076149962557975493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1423072812266267285071925 133413076149962557975493)
              ·
                refine ⟨25014951778117979620405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133413076149962557975493 25014951778117979620405)
                ·
                  rfl

theorem cell19_82209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_82209 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82209 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82209 prefixEnd_82209 := by exact prefixLift 82209
  have htrace : WordTrace (prefixWord ++ tailWord_82209) baseStart_82209 baseEnd_82209 := by
    simpa [prefixWord, tailWord_82209, baseEnd_82209] using wordTrace_append hprefix tailTrace_82209
  have hstable : (prefixWord ++ tailWord_82209).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82209).length < 2 ^ (prefixWord ++ tailWord_82209).sum := by decide
  have hdescent : baseEnd_82209 < baseStart_82209 := by decide
  rcases family_descends (prefixWord ++ tailWord_82209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82222 : List Nat := [4, 1, 3, 3, 1, 1, 3, 3]
def baseStart_82222 : Nat := 118140960795 + 82222 * 2 ^ 59
def prefixEnd_82222 : Nat := 4983230072969 + 3 ^ 40 * 82222 * 2
def baseEnd_82222 : Nat := 25018907480937801331481

theorem tailTrace_82222 : CollatzResearch.WordTrace tailWord_82222 prefixEnd_82222 25018907480937801331481 := by
  unfold tailWord_82222
  simp only [CollatzResearch.WordTrace]
  refine ⟨374860338516401405592115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1999255138754140829824613 374860338516401405592115)
  ·
    refine ⟨562290507774602108388173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 374860338516401405592115 562290507774602108388173)
    ·
      refine ⟨210858940415475790645565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 562290507774602108388173 210858940415475790645565)
      ·
        refine ⟨79072102655803421492087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210858940415475790645565 79072102655803421492087)
        ·
          refine ⟨118608153983705132238131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79072102655803421492087 118608153983705132238131)
          ·
            refine ⟨177912230975557698357197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118608153983705132238131 177912230975557698357197)
            ·
              refine ⟨66717086615834136883949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177912230975557698357197 66717086615834136883949)
              ·
                refine ⟨25018907480937801331481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66717086615834136883949 25018907480937801331481)
                ·
                  rfl

theorem cell19_82222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_82222 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82222 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82222 prefixEnd_82222 := by exact prefixLift 82222
  have htrace : WordTrace (prefixWord ++ tailWord_82222) baseStart_82222 baseEnd_82222 := by
    simpa [prefixWord, tailWord_82222, baseEnd_82222] using wordTrace_append hprefix tailTrace_82222
  have hstable : (prefixWord ++ tailWord_82222).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82222).length < 2 ^ (prefixWord ++ tailWord_82222).sum := by decide
  have hdescent : baseEnd_82222 < baseStart_82222 := by decide
  rcases family_descends (prefixWord ++ tailWord_82222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82285 : List Nat := [1, 5, 1, 1, 1, 2, 3, 5]
def baseStart_82285 : Nat := 118140960795 + 82285 * 2 ^ 59
def prefixEnd_82285 : Nat := 4983230072969 + 3 ^ 40 * 82285 * 2
def baseEnd_82285 : Nat := 25038077425372321931309

theorem tailTrace_82285 : CollatzResearch.WordTrace tailWord_82285 prefixEnd_82285 25038077425372321931309 := by
  unfold tailWord_82285
  simp only [CollatzResearch.WordTrace]
  refine ⟨3001180506902973004280309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2000787004601982002853539 3001180506902973004280309)
  ·
    refine ⟨281360672522153719151279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3001180506902973004280309 281360672522153719151279)
    ·
      refine ⟨422041008783230578726919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281360672522153719151279 422041008783230578726919)
      ·
        refine ⟨633061513174845868090379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422041008783230578726919 633061513174845868090379)
        ·
          refine ⟨949592269762268802135569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633061513174845868090379 949592269762268802135569)
          ·
            refine ⟨712194202321701601601677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 949592269762268802135569 712194202321701601601677)
            ·
              refine ⟨267072825870638100600629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 712194202321701601601677 267072825870638100600629)
              ·
                refine ⟨25038077425372321931309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 267072825870638100600629 25038077425372321931309)
                ·
                  rfl

theorem cell19_82285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_82285 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82285 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82285 prefixEnd_82285 := by exact prefixLift 82285
  have htrace : WordTrace (prefixWord ++ tailWord_82285) baseStart_82285 baseEnd_82285 := by
    simpa [prefixWord, tailWord_82285, baseEnd_82285] using wordTrace_append hprefix tailTrace_82285
  have hstable : (prefixWord ++ tailWord_82285).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82285).length < 2 ^ (prefixWord ++ tailWord_82285).sum := by decide
  have hdescent : baseEnd_82285 < baseStart_82285 := by decide
  rcases family_descends (prefixWord ++ tailWord_82285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82397 : List Nat := [1, 4, 3, 1, 1, 1, 5, 3]
def baseStart_82397 : Nat := 118140960795 + 82397 * 2 ^ 59
def prefixEnd_82397 : Nat := 4983230072969 + 3 ^ 40 * 82397 * 2
def baseEnd_82397 : Nat := 25072157326589247442115

theorem tailTrace_82397 : CollatzResearch.WordTrace tailWord_82397 prefixEnd_82397 25072157326589247442115 := by
  unfold tailWord_82397
  simp only [CollatzResearch.WordTrace]
  refine ⟨3005265482497216132357445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2003510321664810754904963 3005265482497216132357445)
  ·
    refine ⟨563487277968228024817021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3005265482497216132357445 563487277968228024817021)
    ·
      refine ⟨211307729238085509306383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 563487277968228024817021 211307729238085509306383)
      ·
        refine ⟨316961593857128263959575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211307729238085509306383 316961593857128263959575)
        ·
          refine ⟨475442390785692395939363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316961593857128263959575 475442390785692395939363)
          ·
            refine ⟨713163586178538593909045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475442390785692395939363 713163586178538593909045)
            ·
              refine ⟨66859086204237993178973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 713163586178538593909045 66859086204237993178973)
              ·
                refine ⟨25072157326589247442115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66859086204237993178973 25072157326589247442115)
                ·
                  rfl

theorem cell19_82397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 3].length) (baseStart_82397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82397 prefixEnd_82397 := by exact prefixLift 82397
  have htrace : WordTrace (prefixWord ++ tailWord_82397) baseStart_82397 baseEnd_82397 := by
    simpa [prefixWord, tailWord_82397, baseEnd_82397] using wordTrace_append hprefix tailTrace_82397
  have hstable : (prefixWord ++ tailWord_82397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82397).length < 2 ^ (prefixWord ++ tailWord_82397).sum := by decide
  have hdescent : baseEnd_82397 < baseStart_82397 := by decide
  rcases family_descends (prefixWord ++ tailWord_82397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82452 : List Nat := [2, 4, 3, 1, 1, 1, 4, 3]
def baseStart_82452 : Nat := 118140960795 + 82452 * 2 ^ 59
def prefixEnd_82452 : Nat := 4983230072969 + 3 ^ 40 * 82452 * 2
def baseEnd_82452 : Nat := 25088892992365416219743

theorem tailTrace_82452 : CollatzResearch.WordTrace tailWord_82452 prefixEnd_82452 25088892992365416219743 := by
  unfold tailWord_82452
  simp only [CollatzResearch.WordTrace]
  refine ⟨1503635748648980262804805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2004847664865307017073073 1503635748648980262804805)
  ·
    refine ⟨281931702871683799275901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1503635748648980262804805 281931702871683799275901)
    ·
      refine ⟨105724388576881424728463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281931702871683799275901 105724388576881424728463)
      ·
        refine ⟨158586582865322137092695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105724388576881424728463 158586582865322137092695)
        ·
          refine ⟨237879874297983205639043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158586582865322137092695 237879874297983205639043)
          ·
            refine ⟨356819811446974808458565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237879874297983205639043 356819811446974808458565)
            ·
              refine ⟨66903714646307776585981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 356819811446974808458565 66903714646307776585981)
              ·
                refine ⟨25088892992365416219743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66903714646307776585981 25088892992365416219743)
                ·
                  rfl

theorem cell19_82452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_82452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82452 prefixEnd_82452 := by exact prefixLift 82452
  have htrace : WordTrace (prefixWord ++ tailWord_82452) baseStart_82452 baseEnd_82452 := by
    simpa [prefixWord, tailWord_82452, baseEnd_82452] using wordTrace_append hprefix tailTrace_82452
  have hstable : (prefixWord ++ tailWord_82452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82452).length < 2 ^ (prefixWord ++ tailWord_82452).sum := by decide
  have hdescent : baseEnd_82452 < baseStart_82452 := by decide
  rcases family_descends (prefixWord ++ tailWord_82452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82456 : List Nat := [2, 1, 2, 3, 3, 2, 1, 5]
def baseStart_82456 : Nat := 118140960795 + 82456 * 2 ^ 59
def prefixEnd_82456 : Nat := 4983230072969 + 3 ^ 40 * 82456 * 2
def baseEnd_82456 : Nat := 25090110131694592130843

theorem tailTrace_82456 : CollatzResearch.WordTrace tailWord_82456 prefixEnd_82456 25090110131694592130843 := by
  unfold tailWord_82456
  simp only [CollatzResearch.WordTrace]
  refine ⟨1503708694641734604377611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2004944926188979472503481 1503708694641734604377611)
  ·
    refine ⟨2255563041962601906566417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1503708694641734604377611 2255563041962601906566417)
    ·
      refine ⟨1691672281471951429924813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2255563041962601906566417 1691672281471951429924813)
      ·
        refine ⟨634377105551981786221805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1691672281471951429924813 634377105551981786221805)
        ·
          refine ⟨237891414581993169833177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 634377105551981786221805 237891414581993169833177)
          ·
            refine ⟨178418560936494877374883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237891414581993169833177 178418560936494877374883)
            ·
              refine ⟨267627841404742316062325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178418560936494877374883 267627841404742316062325)
              ·
                refine ⟨25090110131694592130843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 267627841404742316062325 25090110131694592130843)
                ·
                  rfl

theorem cell19_82456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_82456 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82456 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82456 prefixEnd_82456 := by exact prefixLift 82456
  have htrace : WordTrace (prefixWord ++ tailWord_82456) baseStart_82456 baseEnd_82456 := by
    simpa [prefixWord, tailWord_82456, baseEnd_82456] using wordTrace_append hprefix tailTrace_82456
  have hstable : (prefixWord ++ tailWord_82456).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82456).length < 2 ^ (prefixWord ++ tailWord_82456).sum := by decide
  have hdescent : baseEnd_82456 < baseStart_82456 := by decide
  rcases family_descends (prefixWord ++ tailWord_82456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82471 : List Nat := [1, 1, 7, 2, 1, 2, 5]
def baseStart_82471 : Nat := 118140960795 + 82471 * 2 ^ 59
def prefixEnd_82471 : Nat := 4983230072969 + 3 ^ 40 * 82471 * 2
def baseEnd_82471 : Nat := 8364891468059667265823

theorem tailTrace_82471 : CollatzResearch.WordTrace tailWord_82471 prefixEnd_82471 8364891468059667265823 := by
  unfold tailWord_82471
  simp only [CollatzResearch.WordTrace]
  refine ⟨3007964484229126770551267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2005309656152751180367511 3007964484229126770551267)
  ·
    refine ⟨4511946726343690155826901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3007964484229126770551267 4511946726343690155826901)
    ·
      refine ⟨105748751398680238027193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 4511946726343690155826901 105748751398680238027193)
      ·
        refine ⟨79311563549010178520395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105748751398680238027193 79311563549010178520395)
        ·
          refine ⟨118967345323515267780593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79311563549010178520395 118967345323515267780593)
          ·
            refine ⟨89225508992636450835445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118967345323515267780593 89225508992636450835445)
            ·
              refine ⟨8364891468059667265823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89225508992636450835445 8364891468059667265823)
              ·
                rfl

theorem cell19_82471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 5].length) (baseStart_82471 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82471 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82471 prefixEnd_82471 := by exact prefixLift 82471
  have htrace : WordTrace (prefixWord ++ tailWord_82471) baseStart_82471 baseEnd_82471 := by
    simpa [prefixWord, tailWord_82471, baseEnd_82471] using wordTrace_append hprefix tailTrace_82471
  have hstable : (prefixWord ++ tailWord_82471).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82471).length < 2 ^ (prefixWord ++ tailWord_82471).sum := by decide
  have hdescent : baseEnd_82471 < baseStart_82471 := by decide
  rcases family_descends (prefixWord ++ tailWord_82471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82496 : List Nat := [2, 1, 1, 2, 2, 2, 3, 6]
def baseStart_82496 : Nat := 118140960795 + 82496 * 2 ^ 59
def prefixEnd_82496 : Nat := 4983230072969 + 3 ^ 40 * 82496 * 2
def baseEnd_82496 : Nat := 25102281524986351241845

theorem tailTrace_82496 : CollatzResearch.WordTrace tailWord_82496 prefixEnd_82496 25102281524986351241845 := by
  unfold tailWord_82496
  simp only [CollatzResearch.WordTrace]
  refine ⟨1504438154569278020105671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2005917539425704026807561 1504438154569278020105671)
  ·
    refine ⟨2256657231853917030158507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1504438154569278020105671 2256657231853917030158507)
    ·
      refine ⟨3384985847780875545237761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2256657231853917030158507 3384985847780875545237761)
      ·
        refine ⟨2538739385835656658928321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3384985847780875545237761 2538739385835656658928321)
        ·
          refine ⟨1904054539376742494196241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2538739385835656658928321 1904054539376742494196241)
          ·
            refine ⟨1428040904532556870647181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1904054539376742494196241 1428040904532556870647181)
            ·
              refine ⟨535515339199708826492693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1428040904532556870647181 535515339199708826492693)
              ·
                refine ⟨25102281524986351241845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 535515339199708826492693 25102281524986351241845)
                ·
                  rfl

theorem cell19_82496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_82496 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82496 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82496 prefixEnd_82496 := by exact prefixLift 82496
  have htrace : WordTrace (prefixWord ++ tailWord_82496) baseStart_82496 baseEnd_82496 := by
    simpa [prefixWord, tailWord_82496, baseEnd_82496] using wordTrace_append hprefix tailTrace_82496
  have hstable : (prefixWord ++ tailWord_82496).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82496).length < 2 ^ (prefixWord ++ tailWord_82496).sum := by decide
  have hdescent : baseEnd_82496 < baseStart_82496 := by decide
  rcases family_descends (prefixWord ++ tailWord_82496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82526 : List Nat := [4, 4, 1, 2, 2, 6]
def baseStart_82526 : Nat := 118140960795 + 82526 * 2 ^ 59
def prefixEnd_82526 : Nat := 4983230072969 + 3 ^ 40 * 82526 * 2
def baseEnd_82526 : Nat := 2790156674439463397233

theorem tailTrace_82526 : CollatzResearch.WordTrace tailWord_82526 prefixEnd_82526 2790156674439463397233 := by
  unfold tailWord_82526
  simp only [CollatzResearch.WordTrace]
  refine ⟨376246312378733895475429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2006646999353247442535621 376246312378733895475429)
  ·
    refine ⟨70546183571012605401643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 376246312378733895475429 70546183571012605401643)
    ·
      refine ⟨105819275356518908102465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70546183571012605401643 105819275356518908102465)
      ·
        refine ⟨79364456517389181076849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105819275356518908102465 79364456517389181076849)
        ·
          refine ⟨59523342388041885807637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79364456517389181076849 59523342388041885807637)
          ·
            refine ⟨2790156674439463397233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59523342388041885807637 2790156674439463397233)
            ·
              rfl

theorem cell19_82526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 6].length) (baseStart_82526 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82526 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82526 prefixEnd_82526 := by exact prefixLift 82526
  have htrace : WordTrace (prefixWord ++ tailWord_82526) baseStart_82526 baseEnd_82526 := by
    simpa [prefixWord, tailWord_82526, baseEnd_82526] using wordTrace_append hprefix tailTrace_82526
  have hstable : (prefixWord ++ tailWord_82526).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82526).length < 2 ^ (prefixWord ++ tailWord_82526).sum := by decide
  have hdescent : baseEnd_82526 < baseStart_82526 := by decide
  rcases family_descends (prefixWord ++ tailWord_82526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82530 : List Nat := [3, 3, 2, 3, 1, 7]
def baseStart_82530 : Nat := 118140960795 + 82530 * 2 ^ 59
def prefixEnd_82530 : Nat := 4983230072969 + 3 ^ 40 * 82530 * 2
def baseEnd_82530 : Nat := 2790291912142705165133

theorem tailTrace_82530 : CollatzResearch.WordTrace tailWord_82530 prefixEnd_82530 2790291912142705165133 := by
  unfold tailWord_82530
  simp only [CollatzResearch.WordTrace]
  refine ⟨752529097753844961737261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2006744260676919897966029 752529097753844961737261)
  ·
    refine ⟨282198411657691860651473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 752529097753844961737261 282198411657691860651473)
    ·
      refine ⟨211648808743268895488605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282198411657691860651473 211648808743268895488605)
      ·
        refine ⟨79368303278725835808227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211648808743268895488605 79368303278725835808227)
        ·
          refine ⟨119052454918088753712341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79368303278725835808227 119052454918088753712341)
          ·
            refine ⟨2790291912142705165133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 119052454918088753712341 2790291912142705165133)
            ·
              rfl

theorem cell19_82530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 7].length) (baseStart_82530 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82530 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82530 prefixEnd_82530 := by exact prefixLift 82530
  have htrace : WordTrace (prefixWord ++ tailWord_82530) baseStart_82530 baseEnd_82530 := by
    simpa [prefixWord, tailWord_82530, baseEnd_82530] using wordTrace_append hprefix tailTrace_82530
  have hstable : (prefixWord ++ tailWord_82530).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82530).length < 2 ^ (prefixWord ++ tailWord_82530).sum := by decide
  have hdescent : baseEnd_82530 < baseStart_82530 := by decide
  rcases family_descends (prefixWord ++ tailWord_82530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82562 : List Nat := [3, 4, 3, 1, 1, 1, 3, 3]
def baseStart_82562 : Nat := 118140960795 + 82562 * 2 ^ 59
def prefixEnd_82562 : Nat := 4983230072969 + 3 ^ 40 * 82562 * 2
def baseEnd_82562 : Nat := 25122364323917753774999

theorem tailTrace_82562 : CollatzResearch.WordTrace tailWord_82562 prefixEnd_82562 25122364323917753774999 := by
  unfold tailWord_82562
  simp only [CollatzResearch.WordTrace]
  refine ⟨752820881724862328028485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2007522351266299541409293 752820881724862328028485)
  ·
    refine ⟨141153915323411686505341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 752820881724862328028485 141153915323411686505341)
    ·
      refine ⟨52932718246279382439503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141153915323411686505341 52932718246279382439503)
      ·
        refine ⟨79399077369419073659255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52932718246279382439503 79399077369419073659255)
        ·
          refine ⟨119098616054128610488883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79399077369419073659255 119098616054128610488883)
          ·
            refine ⟨178647924081192915733325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119098616054128610488883 178647924081192915733325)
            ·
              refine ⟨66992971530447343399997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178647924081192915733325 66992971530447343399997)
              ·
                refine ⟨25122364323917753774999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66992971530447343399997 25122364323917753774999)
                ·
                  rfl

theorem cell19_82562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_82562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82562 prefixEnd_82562 := by exact prefixLift 82562
  have htrace : WordTrace (prefixWord ++ tailWord_82562) baseStart_82562 baseEnd_82562 := by
    simpa [prefixWord, tailWord_82562, baseEnd_82562] using wordTrace_append hprefix tailTrace_82562
  have hstable : (prefixWord ++ tailWord_82562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82562).length < 2 ^ (prefixWord ++ tailWord_82562).sum := by decide
  have hdescent : baseEnd_82562 < baseStart_82562 := by decide
  rcases family_descends (prefixWord ++ tailWord_82562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82610 : List Nat := [3, 2, 1, 1, 1, 2, 1, 8]
def baseStart_82610 : Nat := 118140960795 + 82610 * 2 ^ 59
def prefixEnd_82610 : Nat := 4983230072969 + 3 ^ 40 * 82610 * 2
def baseEnd_82610 : Nat := 25136969995867864708201

theorem tailTrace_82610 : CollatzResearch.WordTrace tailWord_82610 prefixEnd_82610 25136969995867864708201 := by
  unfold tailWord_82610
  simp only [CollatzResearch.WordTrace]
  refine ⟨753258557681388377465321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2008689487150369006574189 753258557681388377465321)
  ·
    refine ⟨564943918261041283098991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 753258557681388377465321 564943918261041283098991)
    ·
      refine ⟨847415877391561924648487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 564943918261041283098991 847415877391561924648487)
      ·
        refine ⟨1271123816087342886972731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 847415877391561924648487 1271123816087342886972731)
        ·
          refine ⟨1906685724131014330459097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271123816087342886972731 1906685724131014330459097)
          ·
            refine ⟨1430014293098260747844323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1906685724131014330459097 1430014293098260747844323)
            ·
              refine ⟨2145021439647391121766485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1430014293098260747844323 2145021439647391121766485)
              ·
                refine ⟨25136969995867864708201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2145021439647391121766485 25136969995867864708201)
                ·
                  rfl

theorem cell19_82610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_82610 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82610 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82610 prefixEnd_82610 := by exact prefixLift 82610
  have htrace : WordTrace (prefixWord ++ tailWord_82610) baseStart_82610 baseEnd_82610 := by
    simpa [prefixWord, tailWord_82610, baseEnd_82610] using wordTrace_append hprefix tailTrace_82610
  have hstable : (prefixWord ++ tailWord_82610).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82610).length < 2 ^ (prefixWord ++ tailWord_82610).sum := by decide
  have hdescent : baseEnd_82610 < baseStart_82610 := by decide
  rcases family_descends (prefixWord ++ tailWord_82610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82644 : List Nat := [2, 4, 1, 3, 2, 2, 5]
def baseStart_82644 : Nat := 118140960795 + 82644 * 2 ^ 59
def prefixEnd_82644 : Nat := 4983230072969 + 3 ^ 40 * 82644 * 2
def baseEnd_82644 : Nat := 8382438560055286650851

theorem tailTrace_82644 : CollatzResearch.WordTrace tailWord_82644 prefixEnd_82644 8382438560055286650851 := by
  unfold tailWord_82644
  simp only [CollatzResearch.WordTrace]
  refine ⟨1507137156301188658299493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2009516208401584877732657 1507137156301188658299493)
  ·
    refine ⟨282588216806472873431155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1507137156301188658299493 282588216806472873431155)
    ·
      refine ⟨423882325209709310146733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282588216806472873431155 423882325209709310146733)
      ·
        refine ⟨158955871953640991305025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 423882325209709310146733 158955871953640991305025)
        ·
          refine ⟨119216903965230743478769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158955871953640991305025 119216903965230743478769)
          ·
            refine ⟨89412677973923057609077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119216903965230743478769 89412677973923057609077)
            ·
              refine ⟨8382438560055286650851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89412677973923057609077 8382438560055286650851)
              ·
                rfl

theorem cell19_82644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 5].length) (baseStart_82644 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82644 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82644 prefixEnd_82644 := by exact prefixLift 82644
  have htrace : WordTrace (prefixWord ++ tailWord_82644) baseStart_82644 baseEnd_82644 := by
    simpa [prefixWord, tailWord_82644, baseEnd_82644] using wordTrace_append hprefix tailTrace_82644
  have hstable : (prefixWord ++ tailWord_82644).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82644).length < 2 ^ (prefixWord ++ tailWord_82644).sum := by decide
  have hdescent : baseEnd_82644 < baseStart_82644 := by decide
  rcases family_descends (prefixWord ++ tailWord_82644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82648 : List Nat := [2, 1, 2, 2, 3, 2, 7]
def baseStart_82648 : Nat := 118140960795 + 82648 * 2 ^ 59
def prefixEnd_82648 : Nat := 4983230072969 + 3 ^ 40 * 82648 * 2
def baseEnd_82648 : Nat := 8382844273165011954551

theorem tailTrace_82648 : CollatzResearch.WordTrace tailWord_82648 prefixEnd_82648 8382844273165011954551 := by
  unfold tailWord_82648
  simp only [CollatzResearch.WordTrace]
  refine ⟨1507210102293942999872299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2009613469725257333163065 1507210102293942999872299)
  ·
    refine ⟨2260815153440914499808449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1507210102293942999872299 2260815153440914499808449)
    ·
      refine ⟨1695611365080685874856337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2260815153440914499808449 1695611365080685874856337)
      ·
        refine ⟨1271708523810514406142253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1695611365080685874856337 1271708523810514406142253)
        ·
          refine ⟨476890696428942902303345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1271708523810514406142253 476890696428942902303345)
          ·
            refine ⟨357668022321707176727509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 476890696428942902303345 357668022321707176727509)
            ·
              refine ⟨8382844273165011954551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 357668022321707176727509 8382844273165011954551)
              ·
                rfl

theorem cell19_82648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 7].length) (baseStart_82648 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82648 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82648 prefixEnd_82648 := by exact prefixLift 82648
  have htrace : WordTrace (prefixWord ++ tailWord_82648) baseStart_82648 baseEnd_82648 := by
    simpa [prefixWord, tailWord_82648, baseEnd_82648] using wordTrace_append hprefix tailTrace_82648
  have hstable : (prefixWord ++ tailWord_82648).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82648).length < 2 ^ (prefixWord ++ tailWord_82648).sum := by decide
  have hdescent : baseEnd_82648 < baseStart_82648 := by decide
  rcases family_descends (prefixWord ++ tailWord_82648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82701 : List Nat := [1, 7, 2, 9]
def baseStart_82701 : Nat := 118140960795 + 82701 * 2 ^ 59
def prefixEnd_82701 : Nat := 4983230072969 + 3 ^ 40 * 82701 * 2
def baseEnd_82701 : Nat := 310674813772921193651

theorem tailTrace_82701 : CollatzResearch.WordTrace tailWord_82701 prefixEnd_82701 310674813772921193651 := by
  unfold tailWord_82701
  simp only [CollatzResearch.WordTrace]
  refine ⟨3016353273395876051423957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2010902182263917367615971 3016353273395876051423957)
  ·
    refine ⟨70695779845215844955249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 3016353273395876051423957 70695779845215844955249)
    ·
      refine ⟨53021834883911883716437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70695779845215844955249 53021834883911883716437)
      ·
        refine ⟨310674813772921193651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 53021834883911883716437 310674813772921193651)
        ·
          rfl

theorem cell19_82701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 9].length) (baseStart_82701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82701 prefixEnd_82701 := by exact prefixLift 82701
  have htrace : WordTrace (prefixWord ++ tailWord_82701) baseStart_82701 baseEnd_82701 := by
    simpa [prefixWord, tailWord_82701, baseEnd_82701] using wordTrace_append hprefix tailTrace_82701
  have hstable : (prefixWord ++ tailWord_82701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82701).length < 2 ^ (prefixWord ++ tailWord_82701).sum := by decide
  have hdescent : baseEnd_82701 < baseStart_82701 := by decide
  rcases family_descends (prefixWord ++ tailWord_82701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82722 : List Nat := [3, 3, 1, 1, 2, 2, 3, 4]
def baseStart_82722 : Nat := 118140960795 + 82722 * 2 ^ 59
def prefixEnd_82722 : Nat := 4983230072969 + 3 ^ 40 * 82722 * 2
def baseEnd_82722 : Nat := 25171049897084790219007

theorem tailTrace_82722 : CollatzResearch.WordTrace tailWord_82722 prefixEnd_82722 25171049897084790219007 := by
  unfold tailWord_82722
  simp only [CollatzResearch.WordTrace]
  refine ⟨754279801579949159484605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2011412804213197758625613 754279801579949159484605)
  ·
    refine ⟨282854925592480934806727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 754279801579949159484605 282854925592480934806727)
    ·
      refine ⟨424282388388721402210091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282854925592480934806727 424282388388721402210091)
      ·
        refine ⟨636423582583082103315137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424282388388721402210091 636423582583082103315137)
        ·
          refine ⟨477317686937311577486353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 636423582583082103315137 477317686937311577486353)
          ·
            refine ⟨357988265202983683114765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477317686937311577486353 357988265202983683114765)
            ·
              refine ⟨134245599451118881168037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 357988265202983683114765 134245599451118881168037)
              ·
                refine ⟨25171049897084790219007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134245599451118881168037 25171049897084790219007)
                ·
                  rfl

theorem cell19_82722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_82722 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82722 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82722 prefixEnd_82722 := by exact prefixLift 82722
  have htrace : WordTrace (prefixWord ++ tailWord_82722) baseStart_82722 baseEnd_82722 := by
    simpa [prefixWord, tailWord_82722, baseEnd_82722] using wordTrace_append hprefix tailTrace_82722
  have hstable : (prefixWord ++ tailWord_82722).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82722).length < 2 ^ (prefixWord ++ tailWord_82722).sum := by decide
  have hdescent : baseEnd_82722 < baseStart_82722 := by decide
  rcases family_descends (prefixWord ++ tailWord_82722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82834 : List Nat := [3, 2, 3, 2, 2, 1, 2, 4]
def baseStart_82834 : Nat := 118140960795 + 82834 * 2 ^ 59
def prefixEnd_82834 : Nat := 4983230072969 + 3 ^ 40 * 82834 * 2
def baseEnd_82834 : Nat := 25205129798301715729813

theorem tailTrace_82834 : CollatzResearch.WordTrace tailWord_82834 prefixEnd_82834 25205129798301715729813 := by
  unfold tailWord_82834
  simp only [CollatzResearch.WordTrace]
  refine ⟨755301045478509941503889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2014136121276026510677037 755301045478509941503889)
  ·
    refine ⟨566475784108882456127917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 755301045478509941503889 566475784108882456127917)
    ·
      refine ⟨212428419040830921047969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 566475784108882456127917 212428419040830921047969)
      ·
        refine ⟨159321314280623190785977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212428419040830921047969 159321314280623190785977)
        ·
          refine ⟨119490985710467393089483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159321314280623190785977 119490985710467393089483)
          ·
            refine ⟨179236478565701089634225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119490985710467393089483 179236478565701089634225)
            ·
              refine ⟨134427358924275817225669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179236478565701089634225 134427358924275817225669)
              ·
                refine ⟨25205129798301715729813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134427358924275817225669 25205129798301715729813)
                ·
                  rfl

theorem cell19_82834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_82834 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82834 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82834 prefixEnd_82834 := by exact prefixLift 82834
  have htrace : WordTrace (prefixWord ++ tailWord_82834) baseStart_82834 baseEnd_82834 := by
    simpa [prefixWord, tailWord_82834, baseEnd_82834] using wordTrace_append hprefix tailTrace_82834
  have hstable : (prefixWord ++ tailWord_82834).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82834).length < 2 ^ (prefixWord ++ tailWord_82834).sum := by decide
  have hdescent : baseEnd_82834 < baseStart_82834 := by decide
  rcases family_descends (prefixWord ++ tailWord_82834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82836 : List Nat := [2, 4, 2, 1, 1, 1, 4, 4]
def baseStart_82836 : Nat := 118140960795 + 82836 * 2 ^ 59
def prefixEnd_82836 : Nat := 4983230072969 + 3 ^ 40 * 82836 * 2
def baseEnd_82836 : Nat := 25205738367966303685363

theorem tailTrace_82836 : CollatzResearch.WordTrace tailWord_82836 prefixEnd_82836 25205738367966303685363 := by
  unfold tailWord_82836
  simp only [CollatzResearch.WordTrace]
  refine ⟨1510638563953397053794181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2014184751937862738392241 1510638563953397053794181)
  ·
    refine ⟨283244730741261947586409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1510638563953397053794181 283244730741261947586409)
    ·
      refine ⟨212433548055946460689807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283244730741261947586409 212433548055946460689807)
      ·
        refine ⟨318650322083919691034711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212433548055946460689807 318650322083919691034711)
        ·
          refine ⟨477975483125879536552067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318650322083919691034711 477975483125879536552067)
          ·
            refine ⟨716963224688819304828101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477975483125879536552067 716963224688819304828101)
            ·
              refine ⟨134430604629153619655269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 716963224688819304828101 134430604629153619655269)
              ·
                refine ⟨25205738367966303685363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134430604629153619655269 25205738367966303685363)
                ·
                  rfl

theorem cell19_82836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_82836 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82836 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82836 prefixEnd_82836 := by exact prefixLift 82836
  have htrace : WordTrace (prefixWord ++ tailWord_82836) baseStart_82836 baseEnd_82836 := by
    simpa [prefixWord, tailWord_82836, baseEnd_82836] using wordTrace_append hprefix tailTrace_82836
  have hstable : (prefixWord ++ tailWord_82836).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82836).length < 2 ^ (prefixWord ++ tailWord_82836).sum := by decide
  have hdescent : baseEnd_82836 < baseStart_82836 := by decide
  rcases family_descends (prefixWord ++ tailWord_82836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82870 : List Nat := [5, 1, 4, 1, 1, 7]
def baseStart_82870 : Nat := 118140960795 + 82870 * 2 ^ 59
def prefixEnd_82870 : Nat := 4983230072969 + 3 ^ 40 * 82870 * 2
def baseEnd_82870 : Nat := 2801787116918255436635

theorem tailTrace_82870 : CollatzResearch.WordTrace tailWord_82870 prefixEnd_82870 2801787116918255436635 := by
  unfold tailWord_82870
  simp only [CollatzResearch.WordTrace]
  refine ⟨188907325611476119645379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2015011473189078609550709 188907325611476119645379)
  ·
    refine ⟨283360988417214179468069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188907325611476119645379 283360988417214179468069)
    ·
      refine ⟨53130185328227658650263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283360988417214179468069 53130185328227658650263)
      ·
        refine ⟨79695277992341487975395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53130185328227658650263 79695277992341487975395)
        ·
          refine ⟨119542916988512231963093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79695277992341487975395 119542916988512231963093)
          ·
            refine ⟨2801787116918255436635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 119542916988512231963093 2801787116918255436635)
            ·
              rfl

theorem cell19_82870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 7].length) (baseStart_82870 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82870 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82870 prefixEnd_82870 := by exact prefixLift 82870
  have htrace : WordTrace (prefixWord ++ tailWord_82870) baseStart_82870 baseEnd_82870 := by
    simpa [prefixWord, tailWord_82870, baseEnd_82870] using wordTrace_append hprefix tailTrace_82870
  have hstable : (prefixWord ++ tailWord_82870).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82870).length < 2 ^ (prefixWord ++ tailWord_82870).sum := by decide
  have hdescent : baseEnd_82870 < baseStart_82870 := by decide
  rcases family_descends (prefixWord ++ tailWord_82870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82895 : List Nat := [1, 1, 2, 1, 1, 6, 3, 4]
def baseStart_82895 : Nat := 118140960795 + 82895 * 2 ^ 59
def prefixEnd_82895 : Nat := 4983230072969 + 3 ^ 40 * 82895 * 2
def baseEnd_82895 : Nat := 25223691173071648374091

theorem tailTrace_82895 : CollatzResearch.WordTrace tailWord_82895 prefixEnd_82895 25223691173071648374091 := by
  unfold tailWord_82895
  simp only [CollatzResearch.WordTrace]
  refine ⟨3023429034693047183986139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2015619356462031455990759 3023429034693047183986139)
  ·
    refine ⟨4535143552039570775979209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3023429034693047183986139 4535143552039570775979209)
    ·
      refine ⟨3401357664029678081984407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4535143552039570775979209 3401357664029678081984407)
      ·
        refine ⟨5102036496044517122976611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3401357664029678081984407 5102036496044517122976611)
        ·
          refine ⟨7653054744066775684464917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5102036496044517122976611 7653054744066775684464917)
          ·
            refine ⟨358736941128130110209293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7653054744066775684464917 358736941128130110209293)
            ·
              refine ⟨134526352923048791328485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 358736941128130110209293 134526352923048791328485)
              ·
                refine ⟨25223691173071648374091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134526352923048791328485 25223691173071648374091)
                ·
                  rfl

theorem cell19_82895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_82895 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82895 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82895 prefixEnd_82895 := by exact prefixLift 82895
  have htrace : WordTrace (prefixWord ++ tailWord_82895) baseStart_82895 baseEnd_82895 := by
    simpa [prefixWord, tailWord_82895, baseEnd_82895] using wordTrace_append hprefix tailTrace_82895
  have hstable : (prefixWord ++ tailWord_82895).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82895).length < 2 ^ (prefixWord ++ tailWord_82895).sum := by decide
  have hdescent : baseEnd_82895 < baseStart_82895 := by decide
  rcases family_descends (prefixWord ++ tailWord_82895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82967 : List Nat := [1, 1, 3, 5, 1, 3, 2, 3]
def baseStart_82967 : Nat := 118140960795 + 82967 * 2 ^ 59
def prefixEnd_82967 : Nat := 4983230072969 + 3 ^ 40 * 82967 * 2
def baseEnd_82967 : Nat := 25245599680996814773895

theorem tailTrace_82967 : CollatzResearch.WordTrace tailWord_82967 prefixEnd_82967 25245599680996814773895 := by
  unfold tailWord_82967
  simp only [CollatzResearch.WordTrace]
  refine ⟨3026055090432203480607155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2017370060288135653738103 3026055090432203480607155)
  ·
    refine ⟨4539082635648305220910733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3026055090432203480607155 4539082635648305220910733)
    ·
      refine ⟨1702155988368114457841525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4539082635648305220910733 1702155988368114457841525)
      ·
        refine ⟨159577123909510730422643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1702155988368114457841525 159577123909510730422643)
        ·
          refine ⟨239365685864266095633965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159577123909510730422643 239365685864266095633965)
          ·
            refine ⟨89762132199099785862737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239365685864266095633965 89762132199099785862737)
            ·
              refine ⟨67321599149324839397053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89762132199099785862737 67321599149324839397053)
              ·
                refine ⟨25245599680996814773895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67321599149324839397053 25245599680996814773895)
                ·
                  rfl

theorem cell19_82967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 3].length) (baseStart_82967 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82967 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82967 prefixEnd_82967 := by exact prefixLift 82967
  have htrace : WordTrace (prefixWord ++ tailWord_82967) baseStart_82967 baseEnd_82967 := by
    simpa [prefixWord, tailWord_82967, baseEnd_82967] using wordTrace_append hprefix tailTrace_82967
  have hstable : (prefixWord ++ tailWord_82967).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82967).length < 2 ^ (prefixWord ++ tailWord_82967).sum := by decide
  have hdescent : baseEnd_82967 < baseStart_82967 := by decide
  rcases family_descends (prefixWord ++ tailWord_82967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82986 : List Nat := [3, 1, 4, 1, 4, 1, 5]
def baseStart_82986 : Nat := 118140960795 + 82986 * 2 ^ 59
def prefixEnd_82986 : Nat := 4983230072969 + 3 ^ 40 * 82986 * 2
def baseEnd_82986 : Nat := 8417127030936800117207

theorem tailTrace_82986 : CollatzResearch.WordTrace tailWord_82986 prefixEnd_82986 8417127030936800117207 := by
  unfold tailWord_82986
  simp only [CollatzResearch.WordTrace]
  refine ⟨756687019340842431387203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2017832051575579817032541 756687019340842431387203)
  ·
    refine ⟨1135030529011263647080805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 756687019340842431387203 1135030529011263647080805)
    ·
      refine ⟨212818224189611933827651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1135030529011263647080805 212818224189611933827651)
      ·
        refine ⟨319227336284417900741477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212818224189611933827651 319227336284417900741477)
        ·
          refine ⟨59855125553328356389027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 319227336284417900741477 59855125553328356389027)
          ·
            refine ⟨89782688329992534583541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59855125553328356389027 89782688329992534583541)
            ·
              refine ⟨8417127030936800117207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89782688329992534583541 8417127030936800117207)
              ·
                rfl

theorem cell19_82986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 5].length) (baseStart_82986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_82986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_82986 prefixEnd_82986 := by exact prefixLift 82986
  have htrace : WordTrace (prefixWord ++ tailWord_82986) baseStart_82986 baseEnd_82986 := by
    simpa [prefixWord, tailWord_82986, baseEnd_82986] using wordTrace_append hprefix tailTrace_82986
  have hstable : (prefixWord ++ tailWord_82986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82986).length < 2 ^ (prefixWord ++ tailWord_82986).sum := by decide
  have hdescent : baseEnd_82986 < baseStart_82986 := by decide
  rcases family_descends (prefixWord ++ tailWord_82986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83028 : List Nat := [2, 4, 1, 1, 1, 1, 4, 5]
def baseStart_83028 : Nat := 118140960795 + 83028 * 2 ^ 59
def prefixEnd_83028 : Nat := 4983230072969 + 3 ^ 40 * 83028 * 2
def baseEnd_83028 : Nat := 25264161055766747418173

theorem tailTrace_83028 : CollatzResearch.WordTrace tailWord_83028 prefixEnd_83028 25264161055766747418173 := by
  unfold tailWord_83028
  simp only [CollatzResearch.WordTrace]
  refine ⟨1514139971605605449288869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2018853295474140599051825 1514139971605605449288869)
  ·
    refine ⟨283901244676051021741663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1514139971605605449288869 283901244676051021741663)
    ·
      refine ⟨425851867014076532612495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283901244676051021741663 425851867014076532612495)
      ·
        refine ⟨638777800521114798918743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425851867014076532612495 638777800521114798918743)
        ·
          refine ⟨958166700781672198378115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638777800521114798918743 958166700781672198378115)
          ·
            refine ⟨1437250051172508297567173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958166700781672198378115 1437250051172508297567173)
            ·
              refine ⟨269484384594845305793845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1437250051172508297567173 269484384594845305793845)
              ·
                refine ⟨25264161055766747418173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 269484384594845305793845 25264161055766747418173)
                ·
                  rfl

theorem cell19_83028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_83028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83028 prefixEnd_83028 := by exact prefixLift 83028
  have htrace : WordTrace (prefixWord ++ tailWord_83028) baseStart_83028 baseEnd_83028 := by
    simpa [prefixWord, tailWord_83028, baseEnd_83028] using wordTrace_append hprefix tailTrace_83028
  have hstable : (prefixWord ++ tailWord_83028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83028).length < 2 ^ (prefixWord ++ tailWord_83028).sum := by decide
  have hdescent : baseEnd_83028 < baseStart_83028 := by decide
  rcases family_descends (prefixWord ++ tailWord_83028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83049 : List Nat := [1, 2, 1, 1, 1, 13]
def baseStart_83049 : Nat := 118140960795 + 83049 * 2 ^ 59
def prefixEnd_83049 : Nat := 4983230072969 + 3 ^ 40 * 83049 * 2
def baseEnd_83049 : Nat := 2807839004138324550161

theorem tailTrace_83049 : CollatzResearch.WordTrace tailWord_83049 prefixEnd_83049 2807839004138324550161 := by
  unfold tailWord_83049
  simp only [CollatzResearch.WordTrace]
  refine ⟨3029045876135131485092201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2019363917423420990061467 3029045876135131485092201)
  ·
    refine ⟨2271784407101348613819151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3029045876135131485092201 2271784407101348613819151)
    ·
      refine ⟨3407676610652022920728727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2271784407101348613819151 3407676610652022920728727)
      ·
        refine ⟨5111514915978034381093091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3407676610652022920728727 5111514915978034381093091)
        ·
          refine ⟨7667272373967051571639637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5111514915978034381093091 7667272373967051571639637)
          ·
            refine ⟨2807839004138324550161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 7667272373967051571639637 2807839004138324550161)
            ·
              rfl

theorem cell19_83049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 13].length) (baseStart_83049 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83049 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83049 prefixEnd_83049 := by exact prefixLift 83049
  have htrace : WordTrace (prefixWord ++ tailWord_83049) baseStart_83049 baseEnd_83049 := by
    simpa [prefixWord, tailWord_83049, baseEnd_83049] using wordTrace_append hprefix tailTrace_83049
  have hstable : (prefixWord ++ tailWord_83049).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83049).length < 2 ^ (prefixWord ++ tailWord_83049).sum := by decide
  have hdescent : baseEnd_83049 < baseStart_83049 := by decide
  rcases family_descends (prefixWord ++ tailWord_83049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83102 : List Nat := [4, 3, 1, 1, 2, 2, 6]
def baseStart_83102 : Nat := 118140960795 + 83102 * 2 ^ 59
def prefixEnd_83102 : Nat := 4983230072969 + 3 ^ 40 * 83102 * 2
def baseEnd_83102 : Nat := 8428892711118833924509

theorem tailTrace_83102 : CollatzResearch.WordTrace tailWord_83102 prefixEnd_83102 8428892711118833924509 := by
  unfold tailWord_83102
  simp only [CollatzResearch.WordTrace]
  refine ⟨378872368117890192096445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2020652629962081024514373 378872368117890192096445)
  ·
    refine ⟨142077138044208822036167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 378872368117890192096445 142077138044208822036167)
    ·
      refine ⟨213115707066313233054251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142077138044208822036167 213115707066313233054251)
      ·
        refine ⟨319673560599469849581377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213115707066313233054251 319673560599469849581377)
        ·
          refine ⟨239755170449602387186033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319673560599469849581377 239755170449602387186033)
          ·
            refine ⟨179816377837201790389525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239755170449602387186033 179816377837201790389525)
            ·
              refine ⟨8428892711118833924509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 179816377837201790389525 8428892711118833924509)
              ·
                rfl

theorem cell19_83102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 6].length) (baseStart_83102 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83102 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83102 prefixEnd_83102 := by exact prefixLift 83102
  have htrace : WordTrace (prefixWord ++ tailWord_83102) baseStart_83102 baseEnd_83102 := by
    simpa [prefixWord, tailWord_83102, baseEnd_83102] using wordTrace_append hprefix tailTrace_83102
  have hstable : (prefixWord ++ tailWord_83102).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83102).length < 2 ^ (prefixWord ++ tailWord_83102).sum := by decide
  have hdescent : baseEnd_83102 < baseStart_83102 := by decide
  rcases family_descends (prefixWord ++ tailWord_83102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83140 : List Nat := [2, 3, 3, 1, 3, 1, 1, 5]
def baseStart_83140 : Nat := 118140960795 + 83140 * 2 ^ 59
def prefixEnd_83140 : Nat := 4983230072969 + 3 ^ 40 * 83140 * 2
def baseEnd_83140 : Nat := 25298240956983672928979

theorem tailTrace_83140 : CollatzResearch.WordTrace tailWord_83140 prefixEnd_83140 25298240956983672928979 := by
  unfold tailWord_83140
  simp only [CollatzResearch.WordTrace]
  refine ⟨1516182459402727013327437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2021576612536969351103249 1516182459402727013327437)
  ·
    refine ⟨568568422276022629997789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1516182459402727013327437 568568422276022629997789)
    ·
      refine ⟨213213158353508486249171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 568568422276022629997789 213213158353508486249171)
      ·
        refine ⟨319819737530262729373757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213213158353508486249171 319819737530262729373757)
        ·
          refine ⟨119932401573848523515159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319819737530262729373757 119932401573848523515159)
          ·
            refine ⟨179898602360772785272739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119932401573848523515159 179898602360772785272739)
            ·
              refine ⟨269847903541159177909109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179898602360772785272739 269847903541159177909109)
              ·
                refine ⟨25298240956983672928979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 269847903541159177909109 25298240956983672928979)
                ·
                  rfl

theorem cell19_83140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_83140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83140 prefixEnd_83140 := by exact prefixLift 83140
  have htrace : WordTrace (prefixWord ++ tailWord_83140) baseStart_83140 baseEnd_83140 := by
    simpa [prefixWord, tailWord_83140, baseEnd_83140] using wordTrace_append hprefix tailTrace_83140
  have hstable : (prefixWord ++ tailWord_83140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83140).length < 2 ^ (prefixWord ++ tailWord_83140).sum := by decide
  have hdescent : baseEnd_83140 < baseStart_83140 := by decide
  rcases family_descends (prefixWord ++ tailWord_83140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83180 : List Nat := [2, 2, 1, 1, 2, 5, 2, 4]
def baseStart_83180 : Nat := 118140960795 + 83180 * 2 ^ 59
def prefixEnd_83180 : Nat := 4983230072969 + 3 ^ 40 * 83180 * 2
def baseEnd_83180 : Nat := 25310412350275432039981

theorem tailTrace_83180 : CollatzResearch.WordTrace tailWord_83180 prefixEnd_83180 25310412350275432039981 := by
  unfold tailWord_83180
  simp only [CollatzResearch.WordTrace]
  refine ⟨1516911919330270429055497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2022549225773693905407329 1516911919330270429055497)
  ·
    refine ⟨1137683939497702821791623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1516911919330270429055497 1137683939497702821791623)
    ·
      refine ⟨1706525909246554232687435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1137683939497702821791623 1706525909246554232687435)
      ·
        refine ⟨2559788863869831349031153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1706525909246554232687435 2559788863869831349031153)
        ·
          refine ⟨1919841647902373511773365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2559788863869831349031153 1919841647902373511773365)
          ·
            refine ⟨179985154490847516728753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1919841647902373511773365 179985154490847516728753)
            ·
              refine ⟨134988865868135637546565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179985154490847516728753 134988865868135637546565)
              ·
                refine ⟨25310412350275432039981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134988865868135637546565 25310412350275432039981)
                ·
                  rfl

theorem cell19_83180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_83180 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83180 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83180 prefixEnd_83180 := by exact prefixLift 83180
  have htrace : WordTrace (prefixWord ++ tailWord_83180) baseStart_83180 baseEnd_83180 := by
    simpa [prefixWord, tailWord_83180, baseEnd_83180] using wordTrace_append hprefix tailTrace_83180
  have hstable : (prefixWord ++ tailWord_83180).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83180).length < 2 ^ (prefixWord ++ tailWord_83180).sum := by decide
  have hdescent : baseEnd_83180 < baseStart_83180 := by decide
  rcases family_descends (prefixWord ++ tailWord_83180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83220 : List Nat := [2, 4, 13]
def baseStart_83220 : Nat := 118140960795 + 83220 * 2 ^ 59
def prefixEnd_83220 : Nat := 4983230072969 + 3 ^ 40 * 83220 * 2
def baseEnd_83220 : Nat := 104208163553774449181

theorem tailTrace_83220 : CollatzResearch.WordTrace tailWord_83220 prefixEnd_83220 104208163553774449181 := by
  unfold tailWord_83220
  simp only [CollatzResearch.WordTrace]
  refine ⟨1517641379257813844783557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2023521839010418459711409 1517641379257813844783557)
  ·
    refine ⟨284557758610840095896917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1517641379257813844783557 284557758610840095896917)
    ·
      refine ⟨104208163553774449181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 13 284557758610840095896917 104208163553774449181)
      ·
        rfl

theorem cell19_83220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 13].length) (baseStart_83220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83220 prefixEnd_83220 := by exact prefixLift 83220
  have htrace : WordTrace (prefixWord ++ tailWord_83220) baseStart_83220 baseEnd_83220 := by
    simpa [prefixWord, tailWord_83220, baseEnd_83220] using wordTrace_append hprefix tailTrace_83220
  have hstable : (prefixWord ++ tailWord_83220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83220).length < 2 ^ (prefixWord ++ tailWord_83220).sum := by decide
  have hdescent : baseEnd_83220 < baseStart_83220 := by decide
  rcases family_descends (prefixWord ++ tailWord_83220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83237 : List Nat := [1, 3, 1, 2, 4, 1, 3, 4]
def baseStart_83237 : Nat := 118140960795 + 83237 * 2 ^ 59
def prefixEnd_83237 : Nat := 4983230072969 + 3 ^ 40 * 83237 * 2
def baseEnd_83237 : Nat := 25327756585716188773159

theorem tailTrace_83237 : CollatzResearch.WordTrace tailWord_83237 prefixEnd_83237 25327756585716188773159 := by
  unfold tailWord_83237
  simp only [CollatzResearch.WordTrace]
  refine ⟨3035902799454039592935965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2023935199636026395290643 3035902799454039592935965)
  ·
    refine ⟨1138463549795264847350987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3035902799454039592935965 1138463549795264847350987)
    ·
      refine ⟨1707695324692897271026481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1138463549795264847350987 1707695324692897271026481)
      ·
        refine ⟨1280771493519672953269861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1707695324692897271026481 1280771493519672953269861)
        ·
          refine ⟨240144655034938678738099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1280771493519672953269861 240144655034938678738099)
          ·
            refine ⟨360216982552408018107149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240144655034938678738099 360216982552408018107149)
            ·
              refine ⟨135081368457153006790181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 360216982552408018107149 135081368457153006790181)
              ·
                refine ⟨25327756585716188773159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135081368457153006790181 25327756585716188773159)
                ·
                  rfl

theorem cell19_83237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_83237 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83237 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83237 prefixEnd_83237 := by exact prefixLift 83237
  have htrace : WordTrace (prefixWord ++ tailWord_83237) baseStart_83237 baseEnd_83237 := by
    simpa [prefixWord, tailWord_83237, baseEnd_83237] using wordTrace_append hprefix tailTrace_83237
  have hstable : (prefixWord ++ tailWord_83237).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83237).length < 2 ^ (prefixWord ++ tailWord_83237).sum := by decide
  have hdescent : baseEnd_83237 < baseStart_83237 := by decide
  rcases family_descends (prefixWord ++ tailWord_83237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83313 : List Nat := [1, 2, 2, 2, 1, 2, 6, 3]
def baseStart_83313 : Nat := 118140960795 + 83313 * 2 ^ 59
def prefixEnd_83313 : Nat := 4983230072969 + 3 ^ 40 * 83313 * 2
def baseEnd_83313 : Nat := 25350882232970531084063

theorem tailTrace_83313 : CollatzResearch.WordTrace tailWord_83313 prefixEnd_83313 25350882232970531084063 := by
  unfold tailWord_83313
  simp only [CollatzResearch.WordTrace]
  refine ⟨3038674747178704572702593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2025783164785803048468395 3038674747178704572702593)
  ·
    refine ⟨2279006060384028429526945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3038674747178704572702593 2279006060384028429526945)
    ·
      refine ⟨1709254545288021322145209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2279006060384028429526945 1709254545288021322145209)
      ·
        refine ⟨1281940908966015991608907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1709254545288021322145209 1281940908966015991608907)
        ·
          refine ⟨1922911363449023987413361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1281940908966015991608907 1922911363449023987413361)
          ·
            refine ⟨1442183522586767990560021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1922911363449023987413361 1442183522586767990560021)
            ·
              refine ⟨67602352621254749557501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1442183522586767990560021 67602352621254749557501)
              ·
                refine ⟨25350882232970531084063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67602352621254749557501 25350882232970531084063)
                ·
                  rfl

theorem cell19_83313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 3].length) (baseStart_83313 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83313 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83313 prefixEnd_83313 := by exact prefixLift 83313
  have htrace : WordTrace (prefixWord ++ tailWord_83313) baseStart_83313 baseEnd_83313 := by
    simpa [prefixWord, tailWord_83313, baseEnd_83313] using wordTrace_append hprefix tailTrace_83313
  have hstable : (prefixWord ++ tailWord_83313).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83313).length < 2 ^ (prefixWord ++ tailWord_83313).sum := by decide
  have hdescent : baseEnd_83313 < baseStart_83313 := by decide
  rcases family_descends (prefixWord ++ tailWord_83313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83326 : List Nat := [4, 2, 3, 2, 2, 1, 5]
def baseStart_83326 : Nat := 118140960795 + 83326 * 2 ^ 59
def prefixEnd_83326 : Nat := 4983230072969 + 3 ^ 40 * 83326 * 2
def baseEnd_83326 : Nat := 8451612645263450931713

theorem tailTrace_83326 : CollatzResearch.WordTrace tailWord_83326 prefixEnd_83326 8451612645263450931713 := by
  unfold tailWord_83326
  simp only [CollatzResearch.WordTrace]
  refine ⟨379893612016450974115729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2026099264087738528617221 379893612016450974115729)
  ·
    refine ⟨284920209012338230586797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 379893612016450974115729 284920209012338230586797)
    ·
      refine ⟨106845078379626836470049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284920209012338230586797 106845078379626836470049)
      ·
        refine ⟨80133808784720127352537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106845078379626836470049 80133808784720127352537)
        ·
          refine ⟨60100356588540095514403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80133808784720127352537 60100356588540095514403)
          ·
            refine ⟨90150534882810143271605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60100356588540095514403 90150534882810143271605)
            ·
              refine ⟨8451612645263450931713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90150534882810143271605 8451612645263450931713)
              ·
                rfl

theorem cell19_83326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 5].length) (baseStart_83326 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83326 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83326 prefixEnd_83326 := by exact prefixLift 83326
  have htrace : WordTrace (prefixWord ++ tailWord_83326) baseStart_83326 baseEnd_83326 := by
    simpa [prefixWord, tailWord_83326, baseEnd_83326] using wordTrace_append hprefix tailTrace_83326
  have hstable : (prefixWord ++ tailWord_83326).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83326).length < 2 ^ (prefixWord ++ tailWord_83326).sum := by decide
  have hdescent : baseEnd_83326 < baseStart_83326 := by decide
  rcases family_descends (prefixWord ++ tailWord_83326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83330 : List Nat := [3, 4, 2, 1, 1, 1, 7]
def baseStart_83330 : Nat := 118140960795 + 83330 * 2 ^ 59
def prefixEnd_83330 : Nat := 4983230072969 + 3 ^ 40 * 83330 * 2
def baseEnd_83330 : Nat := 8452018358373176235413

theorem tailTrace_83330 : CollatzResearch.WordTrace tailWord_83330 prefixEnd_83330 8452018358373176235413 := by
  unfold tailWord_83330
  simp only [CollatzResearch.WordTrace]
  refine ⟨759823697029279119017861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2026196525411410984047629 759823697029279119017861)
  ·
    refine ⟨142466943192989834815849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 759823697029279119017861 142466943192989834815849)
    ·
      refine ⟨106850207394742376111887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142466943192989834815849 106850207394742376111887)
      ·
        refine ⟨160275311092113564167831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106850207394742376111887 160275311092113564167831)
        ·
          refine ⟨240412966638170346251747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160275311092113564167831 240412966638170346251747)
          ·
            refine ⟨360619449957255519377621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240412966638170346251747 360619449957255519377621)
            ·
              refine ⟨8452018358373176235413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 360619449957255519377621 8452018358373176235413)
              ·
                rfl

theorem cell19_83330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 7].length) (baseStart_83330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83330 prefixEnd_83330 := by exact prefixLift 83330
  have htrace : WordTrace (prefixWord ++ tailWord_83330) baseStart_83330 baseEnd_83330 := by
    simpa [prefixWord, tailWord_83330, baseEnd_83330] using wordTrace_append hprefix tailTrace_83330
  have hstable : (prefixWord ++ tailWord_83330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83330).length < 2 ^ (prefixWord ++ tailWord_83330).sum := by decide
  have hdescent : baseEnd_83330 < baseStart_83330 := by decide
  rcases family_descends (prefixWord ++ tailWord_83330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83332 : List Nat := [2, 3, 2, 1, 1, 5, 5]
def baseStart_83332 : Nat := 118140960795 + 83332 * 2 ^ 59
def prefixEnd_83332 : Nat := 4983230072969 + 3 ^ 40 * 83332 * 2
def baseEnd_83332 : Nat := 8452221214928038887263

theorem tailTrace_83332 : CollatzResearch.WordTrace tailWord_83332 prefixEnd_83332 8452221214928038887263 := by
  unfold tailWord_83332
  simp only [CollatzResearch.WordTrace]
  refine ⟨1519683867054935408822125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2026245156073247211762833 1519683867054935408822125)
  ·
    refine ⟨569881450145600778308297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1519683867054935408822125 569881450145600778308297)
    ·
      refine ⟨427411087609200583731223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 569881450145600778308297 427411087609200583731223)
      ·
        refine ⟨641116631413800875596835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427411087609200583731223 641116631413800875596835)
        ·
          refine ⟨961674947120701313395253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641116631413800875596835 961674947120701313395253)
          ·
            refine ⟨90157026292565748130805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 961674947120701313395253 90157026292565748130805)
            ·
              refine ⟨8452221214928038887263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90157026292565748130805 8452221214928038887263)
              ·
                rfl

theorem cell19_83332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 5].length) (baseStart_83332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83332 prefixEnd_83332 := by exact prefixLift 83332
  have htrace : WordTrace (prefixWord ++ tailWord_83332) baseStart_83332 baseEnd_83332 := by
    simpa [prefixWord, tailWord_83332, baseEnd_83332] using wordTrace_append hprefix tailTrace_83332
  have hstable : (prefixWord ++ tailWord_83332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83332).length < 2 ^ (prefixWord ++ tailWord_83332).sum := by decide
  have hdescent : baseEnd_83332 < baseStart_83332 := by decide
  rcases family_descends (prefixWord ++ tailWord_83332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83353 : List Nat := [1, 2, 1, 2, 1, 5, 1, 6]
def baseStart_83353 : Nat := 118140960795 + 83353 * 2 ^ 59
def prefixEnd_83353 : Nat := 4983230072969 + 3 ^ 40 * 83353 * 2
def baseEnd_83353 : Nat := 25363053626262290195065

theorem tailTrace_83353 : CollatzResearch.WordTrace tailWord_83353 prefixEnd_83353 25363053626262290195065 := by
  unfold tailWord_83353
  simp only [CollatzResearch.WordTrace]
  refine ⟨3040133667033791404158713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2026755778022527602772475 3040133667033791404158713)
  ·
    refine ⟨2280100250275343553119035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3040133667033791404158713 2280100250275343553119035)
    ·
      refine ⟨3420150375413015329678553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2280100250275343553119035 3420150375413015329678553)
      ·
        refine ⟨2565112781559761497258915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3420150375413015329678553 2565112781559761497258915)
        ·
          refine ⟨3847669172339642245888373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2565112781559761497258915 3847669172339642245888373)
          ·
            refine ⟨360718984906841460552035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3847669172339642245888373 360718984906841460552035)
            ·
              refine ⟨541078477360262190828053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360718984906841460552035 541078477360262190828053)
              ·
                refine ⟨25363053626262290195065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 541078477360262190828053 25363053626262290195065)
                ·
                  rfl

theorem cell19_83353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_83353 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83353 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83353 prefixEnd_83353 := by exact prefixLift 83353
  have htrace : WordTrace (prefixWord ++ tailWord_83353) baseStart_83353 baseEnd_83353 := by
    simpa [prefixWord, tailWord_83353, baseEnd_83353] using wordTrace_append hprefix tailTrace_83353
  have hstable : (prefixWord ++ tailWord_83353).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83353).length < 2 ^ (prefixWord ++ tailWord_83353).sum := by decide
  have hdescent : baseEnd_83353 < baseStart_83353 := by decide
  rcases family_descends (prefixWord ++ tailWord_83353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83372 : List Nat := [2, 2, 1, 1, 1, 1, 6, 5]
def baseStart_83372 : Nat := 118140960795 + 83372 * 2 ^ 59
def prefixEnd_83372 : Nat := 4983230072969 + 3 ^ 40 * 83372 * 2
def baseEnd_83372 : Nat := 25368835038075875772791

theorem tailTrace_83372 : CollatzResearch.WordTrace tailWord_83372 prefixEnd_83372 25368835038075875772791 := by
  unfold tailWord_83372
  simp only [CollatzResearch.WordTrace]
  refine ⟨1520413326982478824550185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2027217769309971766066913 1520413326982478824550185)
  ·
    refine ⟨1140309995236859118412639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1520413326982478824550185 1140309995236859118412639)
    ·
      refine ⟨1710464992855288677618959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1140309995236859118412639 1710464992855288677618959)
      ·
        refine ⟨2565697489282933016428439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1710464992855288677618959 2565697489282933016428439)
        ·
          refine ⟨3848546233924399524642659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2565697489282933016428439 3848546233924399524642659)
          ·
            refine ⟨5772819350886599286963989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3848546233924399524642659 5772819350886599286963989)
            ·
              refine ⟨270600907072809341576437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5772819350886599286963989 270600907072809341576437)
              ·
                refine ⟨25368835038075875772791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270600907072809341576437 25368835038075875772791)
                ·
                  rfl

theorem cell19_83372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_83372 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83372 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83372 prefixEnd_83372 := by exact prefixLift 83372
  have htrace : WordTrace (prefixWord ++ tailWord_83372) baseStart_83372 baseEnd_83372 := by
    simpa [prefixWord, tailWord_83372, baseEnd_83372] using wordTrace_append hprefix tailTrace_83372
  have hstable : (prefixWord ++ tailWord_83372).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83372).length < 2 ^ (prefixWord ++ tailWord_83372).sum := by decide
  have hdescent : baseEnd_83372 < baseStart_83372 := by decide
  rcases family_descends (prefixWord ++ tailWord_83372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83446 : List Nat := [5, 1, 1, 1, 2, 3, 6]
def baseStart_83446 : Nat := 118140960795 + 83446 * 2 ^ 59
def prefixEnd_83446 : Nat := 4983230072969 + 3 ^ 40 * 83446 * 2
def baseEnd_83446 : Nat := 8463784038555210042715

theorem tailTrace_83446 : CollatzResearch.WordTrace tailWord_83446 prefixEnd_83446 8463784038555210042715 := by
  unfold tailWord_83446
  simp only [CollatzResearch.WordTrace]
  refine ⟨190220353481054267955887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2029017103797912191529461 190220353481054267955887)
  ·
    refine ⟨285330530221581401933831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190220353481054267955887 285330530221581401933831)
    ·
      refine ⟨427995795332372102900747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285330530221581401933831 427995795332372102900747)
      ·
        refine ⟨641993692998558154351121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427995795332372102900747 641993692998558154351121)
        ·
          refine ⟨481495269748918615763341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 641993692998558154351121 481495269748918615763341)
          ·
            refine ⟨180560726155844480911253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 481495269748918615763341 180560726155844480911253)
            ·
              refine ⟨8463784038555210042715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 180560726155844480911253 8463784038555210042715)
              ·
                rfl

theorem cell19_83446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 6].length) (baseStart_83446 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83446 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83446 prefixEnd_83446 := by exact prefixLift 83446
  have htrace : WordTrace (prefixWord ++ tailWord_83446) baseStart_83446 baseEnd_83446 := by
    simpa [prefixWord, tailWord_83446, baseEnd_83446] using wordTrace_append hprefix tailTrace_83446
  have hstable : (prefixWord ++ tailWord_83446).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83446).length < 2 ^ (prefixWord ++ tailWord_83446).sum := by decide
  have hdescent : baseEnd_83446 < baseStart_83446 := by decide
  rcases family_descends (prefixWord ++ tailWord_83446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83448 : List Nat := [2, 1, 2, 1, 1, 6, 6]
def baseStart_83448 : Nat := 118140960795 + 83448 * 2 ^ 59
def prefixEnd_83448 : Nat := 4983230072969 + 3 ^ 40 * 83448 * 2
def baseEnd_83448 : Nat := 8463986895110072694565

theorem tailTrace_83448 : CollatzResearch.WordTrace tailWord_83448 prefixEnd_83448 8463986895110072694565 := by
  unfold tailWord_83448
  simp only [CollatzResearch.WordTrace]
  refine ⟨1521799300844811314433499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2029065734459748419244665 1521799300844811314433499)
  ·
    refine ⟨2282698951267216971650249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1521799300844811314433499 2282698951267216971650249)
    ·
      refine ⟨1712024213450412728737687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2282698951267216971650249 1712024213450412728737687)
      ·
        refine ⟨2568036320175619093106531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1712024213450412728737687 2568036320175619093106531)
        ·
          refine ⟨3852054480263428639659797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2568036320175619093106531 3852054480263428639659797)
          ·
            refine ⟨180565053762348217484053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3852054480263428639659797 180565053762348217484053)
            ·
              refine ⟨8463986895110072694565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 180565053762348217484053 8463986895110072694565)
              ·
                rfl

theorem cell19_83448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 6].length) (baseStart_83448 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83448 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83448 prefixEnd_83448 := by exact prefixLift 83448
  have htrace : WordTrace (prefixWord ++ tailWord_83448) baseStart_83448 baseEnd_83448 := by
    simpa [prefixWord, tailWord_83448, baseEnd_83448] using wordTrace_append hprefix tailTrace_83448
  have hstable : (prefixWord ++ tailWord_83448).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83448).length < 2 ^ (prefixWord ++ tailWord_83448).sum := by decide
  have hdescent : baseEnd_83448 < baseStart_83448 := by decide
  rcases family_descends (prefixWord ++ tailWord_83448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83480 : List Nat := [2, 1, 2, 3, 5, 1, 2, 3]
def baseStart_83480 : Nat := 118140960795 + 83480 * 2 ^ 59
def prefixEnd_83480 : Nat := 4983230072969 + 3 ^ 40 * 83480 * 2
def baseEnd_83480 : Nat := 25401697799963625372497

theorem tailTrace_83480 : CollatzResearch.WordTrace tailWord_83480 prefixEnd_83480 25401697799963625372497 := by
  unfold tailWord_83480
  simp only [CollatzResearch.WordTrace]
  refine ⟨1522382868786846047015947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2029843825049128062687929 1522382868786846047015947)
  ·
    refine ⟨2283574303180269070523921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1522382868786846047015947 2283574303180269070523921)
    ·
      refine ⟨1712680727385201802892941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2283574303180269070523921 1712680727385201802892941)
      ·
        refine ⟨642255272769450676084853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1712680727385201802892941 642255272769450676084853)
        ·
          refine ⟨60211431822136000882955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 642255272769450676084853 60211431822136000882955)
          ·
            refine ⟨90317147733204001324433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60211431822136000882955 90317147733204001324433)
            ·
              refine ⟨67737860799903000993325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90317147733204001324433 67737860799903000993325)
              ·
                refine ⟨25401697799963625372497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67737860799903000993325 25401697799963625372497)
                ·
                  rfl

theorem cell19_83480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_83480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83480 prefixEnd_83480 := by exact prefixLift 83480
  have htrace : WordTrace (prefixWord ++ tailWord_83480) baseStart_83480 baseEnd_83480 := by
    simpa [prefixWord, tailWord_83480, baseEnd_83480] using wordTrace_append hprefix tailTrace_83480
  have hstable : (prefixWord ++ tailWord_83480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83480).length < 2 ^ (prefixWord ++ tailWord_83480).sum := by decide
  have hdescent : baseEnd_83480 < baseStart_83480 := by decide
  rcases family_descends (prefixWord ++ tailWord_83480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83543 : List Nat := [1, 1, 3, 2, 2, 3, 2, 5]
def baseStart_83543 : Nat := 118140960795 + 83543 * 2 ^ 59
def prefixEnd_83543 : Nat := 4983230072969 + 3 ^ 40 * 83543 * 2
def baseEnd_83543 : Nat := 25420867744398145972325

theorem tailTrace_83543 : CollatzResearch.WordTrace tailWord_83543 prefixEnd_83543 25420867744398145972325 := by
  unfold tailWord_83543
  simp only [CollatzResearch.WordTrace]
  refine ⟨3047063536345453853575283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2031375690896969235716855 3047063536345453853575283)
  ·
    refine ⟨4570595304518180780362925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3047063536345453853575283 4570595304518180780362925)
    ·
      refine ⟨1713973239194317792636097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4570595304518180780362925 1713973239194317792636097)
      ·
        refine ⟨1285479929395738344477073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1713973239194317792636097 1285479929395738344477073)
        ·
          refine ⟨964109947046803758357805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1285479929395738344477073 964109947046803758357805)
          ·
            refine ⟨361541230142551409384177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 964109947046803758357805 361541230142551409384177)
            ·
              refine ⟨271155922606913557038133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361541230142551409384177 271155922606913557038133)
              ·
                refine ⟨25420867744398145972325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 271155922606913557038133 25420867744398145972325)
                ·
                  rfl

theorem cell19_83543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_83543 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83543 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83543 prefixEnd_83543 := by exact prefixLift 83543
  have htrace : WordTrace (prefixWord ++ tailWord_83543) baseStart_83543 baseEnd_83543 := by
    simpa [prefixWord, tailWord_83543, baseEnd_83543] using wordTrace_append hprefix tailTrace_83543
  have hstable : (prefixWord ++ tailWord_83543).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83543).length < 2 ^ (prefixWord ++ tailWord_83543).sum := by decide
  have hdescent : baseEnd_83543 < baseStart_83543 := by decide
  rcases family_descends (prefixWord ++ tailWord_83543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83562 : List Nat := [3, 1, 3, 2, 1, 9]
def baseStart_83562 : Nat := 118140960795 + 83562 * 2 ^ 59
def prefixEnd_83562 : Nat := 4983230072969 + 3 ^ 40 * 83562 * 2
def baseEnd_83562 : Nat := 2825183239579081283339

theorem tailTrace_83562 : CollatzResearch.WordTrace tailWord_83562 prefixEnd_83562 2825183239579081283339 := by
  unfold tailWord_83562
  simp only [CollatzResearch.WordTrace]
  refine ⟨761939130819155024629235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2031837682184413399011293 761939130819155024629235)
  ·
    refine ⟨1142908696228732536943853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 761939130819155024629235 1142908696228732536943853)
    ·
      refine ⟨428590761085774701353945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1142908696228732536943853 428590761085774701353945)
      ·
        refine ⟨321443070814331026015459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428590761085774701353945 321443070814331026015459)
        ·
          refine ⟨482164606221496539023189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321443070814331026015459 482164606221496539023189)
          ·
            refine ⟨2825183239579081283339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 482164606221496539023189 2825183239579081283339)
            ·
              rfl

theorem cell19_83562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 9].length) (baseStart_83562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83562 prefixEnd_83562 := by exact prefixLift 83562
  have htrace : WordTrace (prefixWord ++ tailWord_83562) baseStart_83562 baseEnd_83562 := by
    simpa [prefixWord, tailWord_83562, baseEnd_83562] using wordTrace_append hprefix tailTrace_83562
  have hstable : (prefixWord ++ tailWord_83562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83562).length < 2 ^ (prefixWord ++ tailWord_83562).sum := by decide
  have hdescent : baseEnd_83562 < baseStart_83562 := by decide
  rcases family_descends (prefixWord ++ tailWord_83562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83670 : List Nat := [5, 2, 1, 3, 1, 2, 5]
def baseStart_83670 : Nat := 118140960795 + 83670 * 2 ^ 59
def prefixEnd_83670 : Nat := 4983230072969 + 3 ^ 40 * 83670 * 2
def baseEnd_83670 : Nat := 8486503972699827049919

theorem tailTrace_83670 : CollatzResearch.WordTrace tailWord_83670 prefixEnd_83670 8486503972699827049919 := by
  unfold tailWord_83670
  simp only [CollatzResearch.WordTrace]
  refine ⟨190730975430334658965529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2034463737923569695632309 190730975430334658965529)
  ·
    refine ⟨143048231572750994224147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190730975430334658965529 143048231572750994224147)
    ·
      refine ⟨214572347359126491336221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143048231572750994224147 214572347359126491336221)
      ·
        refine ⟨80464630259672434251083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214572347359126491336221 80464630259672434251083)
        ·
          refine ⟨120696945389508651376625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80464630259672434251083 120696945389508651376625)
          ·
            refine ⟨90522709042131488532469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120696945389508651376625 90522709042131488532469)
            ·
              refine ⟨8486503972699827049919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90522709042131488532469 8486503972699827049919)
              ·
                rfl

theorem cell19_83670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 5].length) (baseStart_83670 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83670 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83670 prefixEnd_83670 := by exact prefixLift 83670
  have htrace : WordTrace (prefixWord ++ tailWord_83670) baseStart_83670 baseEnd_83670 := by
    simpa [prefixWord, tailWord_83670, baseEnd_83670] using wordTrace_append hprefix tailTrace_83670
  have hstable : (prefixWord ++ tailWord_83670).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83670).length < 2 ^ (prefixWord ++ tailWord_83670).sum := by decide
  have hdescent : baseEnd_83670 < baseStart_83670 := by decide
  rcases family_descends (prefixWord ++ tailWord_83670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83693 : List Nat := [1, 5, 1, 2, 1, 3, 2, 4]
def baseStart_83693 : Nat := 118140960795 + 83693 * 2 ^ 59
def prefixEnd_83693 : Nat := 4983230072969 + 3 ^ 40 * 83693 * 2
def baseEnd_83693 : Nat := 25466510469242242638583

theorem tailTrace_83693 : CollatzResearch.WordTrace tailWord_83693 prefixEnd_83693 25466510469242242638583 := by
  unfold tailWord_83693
  simp only [CollatzResearch.WordTrace]
  refine ⟨3052534485802029471535733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2035022990534686314357155 3052534485802029471535733)
  ·
    refine ⟨286175108043940262956475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3052534485802029471535733 286175108043940262956475)
    ·
      refine ⟨429262662065910394434713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286175108043940262956475 429262662065910394434713)
      ·
        refine ⟨321946996549432795826035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429262662065910394434713 321946996549432795826035)
        ·
          refine ⟨482920494824149193739053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321946996549432795826035 482920494824149193739053)
          ·
            refine ⟨181095185559055947652145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 482920494824149193739053 181095185559055947652145)
            ·
              refine ⟨135821389169291960739109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181095185559055947652145 135821389169291960739109)
              ·
                refine ⟨25466510469242242638583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135821389169291960739109 25466510469242242638583)
                ·
                  rfl

theorem cell19_83693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_83693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83693 prefixEnd_83693 := by exact prefixLift 83693
  have htrace : WordTrace (prefixWord ++ tailWord_83693) baseStart_83693 baseEnd_83693 := by
    simpa [prefixWord, tailWord_83693, baseEnd_83693] using wordTrace_append hprefix tailTrace_83693
  have hstable : (prefixWord ++ tailWord_83693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83693).length < 2 ^ (prefixWord ++ tailWord_83693).sum := by decide
  have hdescent : baseEnd_83693 < baseStart_83693 := by decide
  rcases family_descends (prefixWord ++ tailWord_83693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83695 : List Nat := [1, 1, 2, 1, 5, 1, 4, 4]
def baseStart_83695 : Nat := 118140960795 + 83695 * 2 ^ 59
def prefixEnd_83695 : Nat := 4983230072969 + 3 ^ 40 * 83695 * 2
def baseEnd_83695 : Nat := 25467119038906830594133

theorem tailTrace_83695 : CollatzResearch.WordTrace tailWord_83695 prefixEnd_83695 25467119038906830594133 := by
  unfold tailWord_83695
  simp only [CollatzResearch.WordTrace]
  refine ⟨3052607431794783813108539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2035071621196522542072359 3052607431794783813108539)
  ·
    refine ⟨4578911147692175719662809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3052607431794783813108539 4578911147692175719662809)
    ·
      refine ⟨3434183360769131789747107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4578911147692175719662809 3434183360769131789747107)
      ·
        refine ⟨5151275041153697684620661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3434183360769131789747107 5151275041153697684620661)
        ·
          refine ⟨482932035108159157933187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5151275041153697684620661 482932035108159157933187)
          ·
            refine ⟨724398052662238736899781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482932035108159157933187 724398052662238736899781)
            ·
              refine ⟨135824634874169763168709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 724398052662238736899781 135824634874169763168709)
              ·
                refine ⟨25467119038906830594133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135824634874169763168709 25467119038906830594133)
                ·
                  rfl

theorem cell19_83695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_83695 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83695 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83695 prefixEnd_83695 := by exact prefixLift 83695
  have htrace : WordTrace (prefixWord ++ tailWord_83695) baseStart_83695 baseEnd_83695 := by
    simpa [prefixWord, tailWord_83695, baseEnd_83695] using wordTrace_append hprefix tailTrace_83695
  have hstable : (prefixWord ++ tailWord_83695).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83695).length < 2 ^ (prefixWord ++ tailWord_83695).sum := by decide
  have hdescent : baseEnd_83695 < baseStart_83695 := by decide
  rcases family_descends (prefixWord ++ tailWord_83695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83725 : List Nat := [1, 7, 2, 1, 2, 6]
def baseStart_83725 : Nat := 118140960795 + 83725 * 2 ^ 59
def prefixEnd_83725 : Nat := 4983230072969 + 3 ^ 40 * 83725 * 2
def baseEnd_83725 : Nat := 2830694175986183325265

theorem tailTrace_83725 : CollatzResearch.WordTrace tailWord_83725 prefixEnd_83725 2830694175986183325265 := by
  unfold tailWord_83725
  simp only [CollatzResearch.WordTrace]
  refine ⟨3053701621686098936700629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2035801081124065957800419 3053701621686098936700629)
  ·
    refine ⟨71571131758267943828921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 3053701621686098936700629 71571131758267943828921)
    ·
      refine ⟨53678348818700957871691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71571131758267943828921 53678348818700957871691)
      ·
        refine ⟨80517523228051436807537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53678348818700957871691 80517523228051436807537)
        ·
          refine ⟨60388142421038577605653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80517523228051436807537 60388142421038577605653)
          ·
            refine ⟨2830694175986183325265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60388142421038577605653 2830694175986183325265)
            ·
              rfl

theorem cell19_83725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 6].length) (baseStart_83725 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83725 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83725 prefixEnd_83725 := by exact prefixLift 83725
  have htrace : WordTrace (prefixWord ++ tailWord_83725) baseStart_83725 baseEnd_83725 := by
    simpa [prefixWord, tailWord_83725, baseEnd_83725] using wordTrace_append hprefix tailTrace_83725
  have hstable : (prefixWord ++ tailWord_83725).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83725).length < 2 ^ (prefixWord ++ tailWord_83725).sum := by decide
  have hdescent : baseEnd_83725 < baseStart_83725 := by decide
  rcases family_descends (prefixWord ++ tailWord_83725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83866 : List Nat := [3, 1, 1, 4, 2, 1, 1, 6]
def baseStart_83866 : Nat := 118140960795 + 83866 * 2 ^ 59
def prefixEnd_83866 : Nat := 4983230072969 + 3 ^ 40 * 83866 * 2
def baseEnd_83866 : Nat := 25519151745229100793667

theorem tailTrace_83866 : CollatzResearch.WordTrace tailWord_83866 prefixEnd_83866 25519151745229100793667 := by
  unfold tailWord_83866
  simp only [CollatzResearch.WordTrace]
  refine ⟨764711078543820004395863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2039229542783520011722301 764711078543820004395863)
  ·
    refine ⟨1147066617815730006593795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 764711078543820004395863 1147066617815730006593795)
    ·
      refine ⟨1720599926723595009890693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1147066617815730006593795 1720599926723595009890693)
      ·
        refine ⟨322612486260674064354505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1720599926723595009890693 322612486260674064354505)
        ·
          refine ⟨241959364695505548265879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322612486260674064354505 241959364695505548265879)
          ·
            refine ⟨362939047043258322398819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241959364695505548265879 362939047043258322398819)
            ·
              refine ⟨544408570564887483598229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362939047043258322398819 544408570564887483598229)
              ·
                refine ⟨25519151745229100793667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 544408570564887483598229 25519151745229100793667)
                ·
                  rfl

theorem cell19_83866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_83866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83866 prefixEnd_83866 := by exact prefixLift 83866
  have htrace : WordTrace (prefixWord ++ tailWord_83866) baseStart_83866 baseEnd_83866 := by
    simpa [prefixWord, tailWord_83866, baseEnd_83866] using wordTrace_append hprefix tailTrace_83866
  have hstable : (prefixWord ++ tailWord_83866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83866).length < 2 ^ (prefixWord ++ tailWord_83866).sum := by decide
  have hdescent : baseEnd_83866 < baseStart_83866 := by decide
  rcases family_descends (prefixWord ++ tailWord_83866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83887 : List Nat := [1, 1, 2, 1, 2, 2, 3, 7]
def baseStart_83887 : Nat := 118140960795 + 83887 * 2 ^ 59
def prefixEnd_83887 : Nat := 4983230072969 + 3 ^ 40 * 83887 * 2
def baseEnd_83887 : Nat := 25525541726707274326943

theorem tailTrace_83887 : CollatzResearch.WordTrace tailWord_83887 prefixEnd_83887 25525541726707274326943 := by
  unfold tailWord_83887
  simp only [CollatzResearch.WordTrace]
  refine ⟨3059610247099200604097915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2039740164732800402731943 3059610247099200604097915)
  ·
    refine ⟨4589415370648800906146873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3059610247099200604097915 4589415370648800906146873)
    ·
      refine ⟨3442061527986600679610155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4589415370648800906146873 3442061527986600679610155)
      ·
        refine ⟨5163092291979901019415233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3442061527986600679610155 5163092291979901019415233)
        ·
          refine ⟨3872319218984925764561425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5163092291979901019415233 3872319218984925764561425)
          ·
            refine ⟨2904239414238694323421069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3872319218984925764561425 2904239414238694323421069)
            ·
              refine ⟨1089089780339510371282901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2904239414238694323421069 1089089780339510371282901)
              ·
                refine ⟨25525541726707274326943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1089089780339510371282901 25525541726707274326943)
                ·
                  rfl

theorem cell19_83887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_83887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83887 prefixEnd_83887 := by exact prefixLift 83887
  have htrace : WordTrace (prefixWord ++ tailWord_83887) baseStart_83887 baseEnd_83887 := by
    simpa [prefixWord, tailWord_83887, baseEnd_83887] using wordTrace_append hprefix tailTrace_83887
  have hstable : (prefixWord ++ tailWord_83887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83887).length < 2 ^ (prefixWord ++ tailWord_83887).sum := by decide
  have hdescent : baseEnd_83887 < baseStart_83887 := by decide
  rcases family_descends (prefixWord ++ tailWord_83887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83997 : List Nat := [1, 4, 2, 2, 2, 1, 4, 3]
def baseStart_83997 : Nat := 118140960795 + 83997 * 2 ^ 59
def prefixEnd_83997 : Nat := 4983230072969 + 3 ^ 40 * 83997 * 2
def baseEnd_83997 : Nat := 25559013058259611882199

theorem tailTrace_83997 : CollatzResearch.WordTrace tailWord_83997 prefixEnd_83997 25559013058259611882199 := by
  unfold tailWord_83997
  simp only [CollatzResearch.WordTrace]
  refine ⟨3063622276700689390602245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2042414851133792927068163 3063622276700689390602245)
  ·
    refine ⟨574429176881379260737921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3063622276700689390602245 574429176881379260737921)
    ·
      refine ⟨430821882661034445553441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 574429176881379260737921 430821882661034445553441)
      ·
        refine ⟨323116411995775834165081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430821882661034445553441 323116411995775834165081)
        ·
          refine ⟨242337308996831875623811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323116411995775834165081 242337308996831875623811)
          ·
            refine ⟨363505963495247813435717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242337308996831875623811 363505963495247813435717)
            ·
              refine ⟨68157368155358965019197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 363505963495247813435717 68157368155358965019197)
              ·
                refine ⟨25559013058259611882199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68157368155358965019197 25559013058259611882199)
                ·
                  rfl

theorem cell19_83997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 3].length) (baseStart_83997 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_83997 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_83997 prefixEnd_83997 := by exact prefixLift 83997
  have htrace : WordTrace (prefixWord ++ tailWord_83997) baseStart_83997 baseEnd_83997 := by
    simpa [prefixWord, tailWord_83997, baseEnd_83997] using wordTrace_append hprefix tailTrace_83997
  have hstable : (prefixWord ++ tailWord_83997).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83997).length < 2 ^ (prefixWord ++ tailWord_83997).sum := by decide
  have hdescent : baseEnd_83997 < baseStart_83997 := by decide
  rcases family_descends (prefixWord ++ tailWord_83997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84018 : List Nat := [3, 2, 1, 1, 2, 5, 5]
def baseStart_84018 : Nat := 118140960795 + 84018 * 2 ^ 59
def prefixEnd_84018 : Nat := 4983230072969 + 3 ^ 40 * 84018 * 2
def baseEnd_84018 : Nat := 8521801013245928471825

theorem tailTrace_84018 : CollatzResearch.WordTrace tailWord_84018 prefixEnd_84018 8521801013245928471825 := by
  unfold tailWord_84018
  simp only [CollatzResearch.WordTrace]
  refine ⟨766097052406152494279177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2042925473083073318077805 766097052406152494279177)
  ·
    refine ⟨574572789304614370709383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 766097052406152494279177 574572789304614370709383)
    ·
      refine ⟨861859183956921556064075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 574572789304614370709383 861859183956921556064075)
      ·
        refine ⟨1292788775935382334096113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 861859183956921556064075 1292788775935382334096113)
        ·
          refine ⟨969591581951536750572085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1292788775935382334096113 969591581951536750572085)
          ·
            refine ⟨90899210807956570366133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 969591581951536750572085 90899210807956570366133)
            ·
              refine ⟨8521801013245928471825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90899210807956570366133 8521801013245928471825)
              ·
                rfl

theorem cell19_84018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 5].length) (baseStart_84018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84018 prefixEnd_84018 := by exact prefixLift 84018
  have htrace : WordTrace (prefixWord ++ tailWord_84018) baseStart_84018 baseEnd_84018 := by
    simpa [prefixWord, tailWord_84018, baseEnd_84018] using wordTrace_append hprefix tailTrace_84018
  have hstable : (prefixWord ++ tailWord_84018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84018).length < 2 ^ (prefixWord ++ tailWord_84018).sum := by decide
  have hdescent : baseEnd_84018 < baseStart_84018 := by decide
  rcases family_descends (prefixWord ++ tailWord_84018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84058 : List Nat := [3, 1, 1, 2, 1, 1, 3, 7]
def baseStart_84058 : Nat := 118140960795 + 84058 * 2 ^ 59
def prefixEnd_84058 : Nat := 4983230072969 + 3 ^ 40 * 84058 * 2
def baseEnd_84058 : Nat := 25577574433029544526477

theorem tailTrace_84058 : CollatzResearch.WordTrace tailWord_84058 prefixEnd_84058 25577574433029544526477 := by
  unfold tailWord_84058
  simp only [CollatzResearch.WordTrace]
  refine ⟨766461782369924202143207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2043898086319797872381885 766461782369924202143207)
  ·
    refine ⟨1149692673554886303214811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 766461782369924202143207 1149692673554886303214811)
    ·
      refine ⟨1724539010332329454822217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1149692673554886303214811 1724539010332329454822217)
      ·
        refine ⟨1293404257749247091116663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1724539010332329454822217 1293404257749247091116663)
        ·
          refine ⟨1940106386623870636674995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293404257749247091116663 1940106386623870636674995)
          ·
            refine ⟨2910159579935805955012493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940106386623870636674995 2910159579935805955012493)
            ·
              refine ⟨1091309842475927233129685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2910159579935805955012493 1091309842475927233129685)
              ·
                refine ⟨25577574433029544526477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1091309842475927233129685 25577574433029544526477)
                ·
                  rfl

theorem cell19_84058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_84058 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84058 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84058 prefixEnd_84058 := by exact prefixLift 84058
  have htrace : WordTrace (prefixWord ++ tailWord_84058) baseStart_84058 baseEnd_84058 := by
    simpa [prefixWord, tailWord_84058, baseEnd_84058] using wordTrace_append hprefix tailTrace_84058
  have hstable : (prefixWord ++ tailWord_84058).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84058).length < 2 ^ (prefixWord ++ tailWord_84058).sum := by decide
  have hdescent : baseEnd_84058 < baseStart_84058 := by decide
  rcases family_descends (prefixWord ++ tailWord_84058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84132 : List Nat := [2, 3, 1, 2, 4, 1, 6]
def baseStart_84132 : Nat := 118140960795 + 84132 * 2 ^ 59
def prefixEnd_84132 : Nat := 4983230072969 + 3 ^ 40 * 84132 * 2
def baseEnd_84132 : Nat := 8533363836873099627277

theorem tailTrace_84132 : CollatzResearch.WordTrace tailWord_84132 prefixEnd_84132 8533363836873099627277 := by
  unfold tailWord_84132
  simp only [CollatzResearch.WordTrace]
  refine ⟨1534273065605803723383325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2045697420807738297844433 1534273065605803723383325)
  ·
    refine ⟨575352399602176396268747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1534273065605803723383325 575352399602176396268747)
    ·
      refine ⟨863028599403264594403121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 575352399602176396268747 863028599403264594403121)
      ·
        refine ⟨647271449552448445802341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 863028599403264594403121 647271449552448445802341)
        ·
          refine ⟨121363396791084083587939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 647271449552448445802341 121363396791084083587939)
          ·
            refine ⟨182045095186626125381909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121363396791084083587939 182045095186626125381909)
            ·
              refine ⟨8533363836873099627277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 182045095186626125381909 8533363836873099627277)
              ·
                rfl

theorem cell19_84132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 6].length) (baseStart_84132 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84132 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84132 prefixEnd_84132 := by exact prefixLift 84132
  have htrace : WordTrace (prefixWord ++ tailWord_84132) baseStart_84132 baseEnd_84132 := by
    simpa [prefixWord, tailWord_84132, baseEnd_84132] using wordTrace_append hprefix tailTrace_84132
  have hstable : (prefixWord ++ tailWord_84132).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84132).length < 2 ^ (prefixWord ++ tailWord_84132).sum := by decide
  have hdescent : baseEnd_84132 < baseStart_84132 := by decide
  rcases family_descends (prefixWord ++ tailWord_84132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84153 : List Nat := [1, 2, 1, 4, 1, 2, 2, 6]
def baseStart_84153 : Nat := 118140960795 + 84153 * 2 ^ 59
def prefixEnd_84153 : Nat := 4983230072969 + 3 ^ 40 * 84153 * 2
def baseEnd_84153 : Nat := 25606481492097472415107

theorem tailTrace_84153 : CollatzResearch.WordTrace tailWord_84153 prefixEnd_84153 25606481492097472415107 := by
  unfold tailWord_84153
  simp only [CollatzResearch.WordTrace]
  refine ⟨3069312064135528033281113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2046208042757018688854075 3069312064135528033281113)
  ·
    refine ⟨2301984048101646024960835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3069312064135528033281113 2301984048101646024960835)
    ·
      refine ⟨3452976072152469037441253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2301984048101646024960835 3452976072152469037441253)
      ·
        refine ⟨647433013528587944520235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3452976072152469037441253 647433013528587944520235)
        ·
          refine ⟨971149520292881916780353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647433013528587944520235 971149520292881916780353)
          ·
            refine ⟨728362140219661437585265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 971149520292881916780353 728362140219661437585265)
            ·
              refine ⟨546271605164746078188949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 728362140219661437585265 546271605164746078188949)
              ·
                refine ⟨25606481492097472415107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 546271605164746078188949 25606481492097472415107)
                ·
                  rfl

theorem cell19_84153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_84153 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84153 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84153 prefixEnd_84153 := by exact prefixLift 84153
  have htrace : WordTrace (prefixWord ++ tailWord_84153) baseStart_84153 baseEnd_84153 := by
    simpa [prefixWord, tailWord_84153, baseEnd_84153] using wordTrace_append hprefix tailTrace_84153
  have hstable : (prefixWord ++ tailWord_84153).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84153).length < 2 ^ (prefixWord ++ tailWord_84153).sum := by decide
  have hdescent : baseEnd_84153 < baseStart_84153 := by decide
  rcases family_descends (prefixWord ++ tailWord_84153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84189 : List Nat := [1, 4, 3, 2, 1, 1, 7]
def baseStart_84189 : Nat := 118140960795 + 84189 * 2 ^ 59
def prefixEnd_84189 : Nat := 4983230072969 + 3 ^ 40 * 84189 * 2
def baseEnd_84189 : Nat := 8539145248686685205003

theorem tailTrace_84189 : CollatzResearch.WordTrace tailWord_84189 prefixEnd_84189 8539145248686685205003 := by
  unfold tailWord_84189
  simp only [CollatzResearch.WordTrace]
  refine ⟨3070625092005106181591621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2047083394670070787727747 3070625092005106181591621)
  ·
    refine ⟨575742204750957409048429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3070625092005106181591621 575742204750957409048429)
    ·
      refine ⟨215903326781609028393161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 575742204750957409048429 215903326781609028393161)
      ·
        refine ⟨161927495086206771294871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215903326781609028393161 161927495086206771294871)
        ·
          refine ⟨242891242629310156942307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161927495086206771294871 242891242629310156942307)
          ·
            refine ⟨364336863943965235413461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242891242629310156942307 364336863943965235413461)
            ·
              refine ⟨8539145248686685205003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 364336863943965235413461 8539145248686685205003)
              ·
                rfl

theorem cell19_84189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 7].length) (baseStart_84189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84189 prefixEnd_84189 := by exact prefixLift 84189
  have htrace : WordTrace (prefixWord ++ tailWord_84189) baseStart_84189 baseEnd_84189 := by
    simpa [prefixWord, tailWord_84189, baseEnd_84189] using wordTrace_append hprefix tailTrace_84189
  have hstable : (prefixWord ++ tailWord_84189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84189).length < 2 ^ (prefixWord ++ tailWord_84189).sum := by decide
  have hdescent : baseEnd_84189 < baseStart_84189 := by decide
  rcases family_descends (prefixWord ++ tailWord_84189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84284 : List Nat := [2, 2, 2, 2, 1, 2, 5, 3]
def baseStart_84284 : Nat := 118140960795 + 84284 * 2 ^ 59
def prefixEnd_84284 : Nat := 4983230072969 + 3 ^ 40 * 84284 * 2
def baseEnd_84284 : Nat := 25646342805127983503639

theorem tailTrace_84284 : CollatzResearch.WordTrace tailWord_84284 prefixEnd_84284 25646342805127983503639 := by
  unfold tailWord_84284
  simp only [CollatzResearch.WordTrace]
  refine ⟨1537045013330468703149953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2049393351107291604199937 1537045013330468703149953)
  ·
    refine ⟨1152783759997851527362465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1537045013330468703149953 1152783759997851527362465)
    ·
      refine ⟨864587819998388645521849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1152783759997851527362465 864587819998388645521849)
      ·
        refine ⟨648440864998791484141387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 864587819998388645521849 648440864998791484141387)
        ·
          refine ⟨972661297498187226212081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648440864998791484141387 972661297498187226212081)
          ·
            refine ⟨729495973123640419659061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 972661297498187226212081 729495973123640419659061)
            ·
              refine ⟨68390247480341289343037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 729495973123640419659061 68390247480341289343037)
              ·
                refine ⟨25646342805127983503639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68390247480341289343037 25646342805127983503639)
                ·
                  rfl

theorem cell19_84284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_84284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84284 prefixEnd_84284 := by exact prefixLift 84284
  have htrace : WordTrace (prefixWord ++ tailWord_84284) baseStart_84284 baseEnd_84284 := by
    simpa [prefixWord, tailWord_84284, baseEnd_84284] using wordTrace_append hprefix tailTrace_84284
  have hstable : (prefixWord ++ tailWord_84284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84284).length < 2 ^ (prefixWord ++ tailWord_84284).sum := by decide
  have hdescent : baseEnd_84284 < baseStart_84284 := by decide
  rcases family_descends (prefixWord ++ tailWord_84284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84305 : List Nat := [1, 2, 2, 1, 4, 3, 6]
def baseStart_84305 : Nat := 118140960795 + 84305 * 2 ^ 59
def prefixEnd_84305 : Nat := 4983230072969 + 3 ^ 40 * 84305 * 2
def baseEnd_84305 : Nat := 8550910928868719012305

theorem tailTrace_84305 : CollatzResearch.WordTrace tailWord_84305 prefixEnd_84305 8550910928868719012305 := by
  unfold tailWord_84305
  simp only [CollatzResearch.WordTrace]
  refine ⟨3074855959584857992814369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2049903973056571995209579 3074855959584857992814369)
  ·
    refine ⟨2306141969688643494610777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3074855959584857992814369 2306141969688643494610777)
    ·
      refine ⟨1729606477266482620958083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2306141969688643494610777 1729606477266482620958083)
      ·
        refine ⟨2594409715899723931437125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1729606477266482620958083 2594409715899723931437125)
        ·
          refine ⟨486451821731198237144461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2594409715899723931437125 486451821731198237144461)
          ·
            refine ⟨182419433149199338929173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 486451821731198237144461 182419433149199338929173)
            ·
              refine ⟨8550910928868719012305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 182419433149199338929173 8550910928868719012305)
              ·
                rfl

theorem cell19_84305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 6].length) (baseStart_84305 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84305 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84305 prefixEnd_84305 := by exact prefixLift 84305
  have htrace : WordTrace (prefixWord ++ tailWord_84305) baseStart_84305 baseEnd_84305 := by
    simpa [prefixWord, tailWord_84305, baseEnd_84305] using wordTrace_append hprefix tailTrace_84305
  have hstable : (prefixWord ++ tailWord_84305).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84305).length < 2 ^ (prefixWord ++ tailWord_84305).sum := by decide
  have hdescent : baseEnd_84305 < baseStart_84305 := by decide
  rcases family_descends (prefixWord ++ tailWord_84305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84324 : List Nat := [2, 3, 1, 1, 3, 1, 2, 6]
def baseStart_84324 : Nat := 118140960795 + 84324 * 2 ^ 59
def prefixEnd_84324 : Nat := 4983230072969 + 3 ^ 40 * 84324 * 2
def baseEnd_84324 : Nat := 25658514198419742614641

theorem tailTrace_84324 : CollatzResearch.WordTrace tailWord_84324 prefixEnd_84324 25658514198419742614641 := by
  unfold tailWord_84324
  simp only [CollatzResearch.WordTrace]
  refine ⟨1537774473258012118878013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2050365964344016158504017 1537774473258012118878013)
  ·
    refine ⟨576665427471754544579255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1537774473258012118878013 576665427471754544579255)
    ·
      refine ⟨864998141207631816868883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 576665427471754544579255 864998141207631816868883)
      ·
        refine ⟨1297497211811447725303325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 864998141207631816868883 1297497211811447725303325)
        ·
          refine ⟨486561454429292896988747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1297497211811447725303325 486561454429292896988747)
          ·
            refine ⟨729842181643939345483121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486561454429292896988747 729842181643939345483121)
            ·
              refine ⟨547381636232954509112341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 729842181643939345483121 547381636232954509112341)
              ·
                refine ⟨25658514198419742614641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 547381636232954509112341 25658514198419742614641)
                ·
                  rfl

theorem cell19_84324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_84324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84324 prefixEnd_84324 := by exact prefixLift 84324
  have htrace : WordTrace (prefixWord ++ tailWord_84324) baseStart_84324 baseEnd_84324 := by
    simpa [prefixWord, tailWord_84324, baseEnd_84324] using wordTrace_append hprefix tailTrace_84324
  have hstable : (prefixWord ++ tailWord_84324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84324).length < 2 ^ (prefixWord ++ tailWord_84324).sum := by decide
  have hdescent : baseEnd_84324 < baseStart_84324 := by decide
  rcases family_descends (prefixWord ++ tailWord_84324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84341 : List Nat := [1, 3, 4, 1, 2, 2, 1, 5]
def baseStart_84341 : Nat := 118140960795 + 84341 * 2 ^ 59
def prefixEnd_84341 : Nat := 4983230072969 + 3 ^ 40 * 84341 * 2
def baseEnd_84341 : Nat := 25663687040568740236817

theorem tailTrace_84341 : CollatzResearch.WordTrace tailWord_84341 prefixEnd_84341 25663687040568740236817 := by
  unfold tailWord_84341
  simp only [CollatzResearch.WordTrace]
  refine ⟨3076168987454436141124877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2050779324969624094083251 3076168987454436141124877)
  ·
    refine ⟨1153563370295413552921829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3076168987454436141124877 1153563370295413552921829)
    ·
      refine ⟨216293131930390041172843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1153563370295413552921829 216293131930390041172843)
      ·
        refine ⟨324439697895585061759265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216293131930390041172843 324439697895585061759265)
        ·
          refine ⟨243329773421688796319449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324439697895585061759265 243329773421688796319449)
          ·
            refine ⟨182497330066266597239587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243329773421688796319449 182497330066266597239587)
            ·
              refine ⟨273745995099399895859381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182497330066266597239587 273745995099399895859381)
              ·
                refine ⟨25663687040568740236817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 273745995099399895859381 25663687040568740236817)
                ·
                  rfl

theorem cell19_84341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_84341 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84341 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84341 prefixEnd_84341 := by exact prefixLift 84341
  have htrace : WordTrace (prefixWord ++ tailWord_84341) baseStart_84341 baseEnd_84341 := by
    simpa [prefixWord, tailWord_84341, baseEnd_84341] using wordTrace_append hprefix tailTrace_84341
  have hstable : (prefixWord ++ tailWord_84341).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84341).length < 2 ^ (prefixWord ++ tailWord_84341).sum := by decide
  have hdescent : baseEnd_84341 < baseStart_84341 := by decide
  rcases family_descends (prefixWord ++ tailWord_84341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84436 : List Nat := [2, 4, 1, 2, 2, 1, 3, 4]
def baseStart_84436 : Nat := 118140960795 + 84436 * 2 ^ 59
def prefixEnd_84436 : Nat := 4983230072969 + 3 ^ 40 * 84436 * 2
def baseEnd_84436 : Nat := 25692594099636668125447

theorem tailTrace_84436 : CollatzResearch.WordTrace tailWord_84436 prefixEnd_84436 25692594099636668125447 := by
  unfold tailWord_84436
  simp only [CollatzResearch.WordTrace]
  refine ⟨1539816961055133682916581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2053089281406844910555441 1539816961055133682916581)
  ·
    refine ⟨288715680197837565546859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1539816961055133682916581 288715680197837565546859)
    ·
      refine ⟨433073520296756348320289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288715680197837565546859 433073520296756348320289)
      ·
        refine ⟨324805140222567261240217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433073520296756348320289 324805140222567261240217)
        ·
          refine ⟨243603855166925445930163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324805140222567261240217 243603855166925445930163)
          ·
            refine ⟨365405782750388168895245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243603855166925445930163 365405782750388168895245)
            ·
              refine ⟨137027168531395563335717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 365405782750388168895245 137027168531395563335717)
              ·
                refine ⟨25692594099636668125447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137027168531395563335717 25692594099636668125447)
                ·
                  rfl

theorem cell19_84436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_84436 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84436 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84436 prefixEnd_84436 := by exact prefixLift 84436
  have htrace : WordTrace (prefixWord ++ tailWord_84436) baseStart_84436 baseEnd_84436 := by
    simpa [prefixWord, tailWord_84436, baseEnd_84436] using wordTrace_append hprefix tailTrace_84436
  have hstable : (prefixWord ++ tailWord_84436).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84436).length < 2 ^ (prefixWord ++ tailWord_84436).sum := by decide
  have hdescent : baseEnd_84436 < baseStart_84436 := by decide
  rcases family_descends (prefixWord ++ tailWord_84436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84453 : List Nat := [1, 3, 1, 5, 2, 1, 3, 3]
def baseStart_84453 : Nat := 118140960795 + 84453 * 2 ^ 59
def prefixEnd_84453 : Nat := 4983230072969 + 3 ^ 40 * 84453 * 2
def baseEnd_84453 : Nat := 25697766941785665747623

theorem tailTrace_84453 : CollatzResearch.WordTrace tailWord_84453 prefixEnd_84453 25697766941785665747623 := by
  unfold tailWord_84453
  simp only [CollatzResearch.WordTrace]
  refine ⟨3080253963048679269202013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2053502642032452846134675 3080253963048679269202013)
  ·
    refine ⟨1155095236143254725950755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3080253963048679269202013 1155095236143254725950755)
    ·
      refine ⟨1732642854214882088926133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155095236143254725950755 1732642854214882088926133)
      ·
        refine ⟨162435267582645195836825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1732642854214882088926133 162435267582645195836825)
        ·
          refine ⟨121826450686983896877619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162435267582645195836825 121826450686983896877619)
          ·
            refine ⟨182739676030475845316429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121826450686983896877619 182739676030475845316429)
            ·
              refine ⟨68527378511428441993661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182739676030475845316429 68527378511428441993661)
              ·
                refine ⟨25697766941785665747623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68527378511428441993661 25697766941785665747623)
                ·
                  rfl

theorem cell19_84453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 3].length) (baseStart_84453 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84453 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84453 prefixEnd_84453 := by exact prefixLift 84453
  have htrace : WordTrace (prefixWord ++ tailWord_84453) baseStart_84453 baseEnd_84453 := by
    simpa [prefixWord, tailWord_84453, baseEnd_84453] using wordTrace_append hprefix tailTrace_84453
  have hstable : (prefixWord ++ tailWord_84453).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84453).length < 2 ^ (prefixWord ++ tailWord_84453).sum := by decide
  have hdescent : baseEnd_84453 < baseStart_84453 := by decide
  rcases family_descends (prefixWord ++ tailWord_84453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84455 : List Nat := [1, 1, 5, 2, 1, 1, 5, 3]
def baseStart_84455 : Nat := 118140960795 + 84455 * 2 ^ 59
def prefixEnd_84455 : Nat := 4983230072969 + 3 ^ 40 * 84455 * 2
def baseEnd_84455 : Nat := 25698375511450253703173

theorem tailTrace_84455 : CollatzResearch.WordTrace tailWord_84455 prefixEnd_84455 25698375511450253703173 := by
  unfold tailWord_84455
  simp only [CollatzResearch.WordTrace]
  refine ⟨3080326909041433610774819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2053551272694289073849879 3080326909041433610774819)
  ·
    refine ⟨4620490363562150416162229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3080326909041433610774819 4620490363562150416162229)
    ·
      refine ⟨433170971583951601515209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4620490363562150416162229 433170971583951601515209)
      ·
        refine ⟨324878228687963701136407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433170971583951601515209 324878228687963701136407)
        ·
          refine ⟨487317343031945551704611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324878228687963701136407 487317343031945551704611)
          ·
            refine ⟨730976014547918327556917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487317343031945551704611 730976014547918327556917)
            ·
              refine ⟨68529001363867343208461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 730976014547918327556917 68529001363867343208461)
              ·
                refine ⟨25698375511450253703173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68529001363867343208461 25698375511450253703173)
                ·
                  rfl

theorem cell19_84455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 3].length) (baseStart_84455 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84455 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84455 prefixEnd_84455 := by exact prefixLift 84455
  have htrace : WordTrace (prefixWord ++ tailWord_84455) baseStart_84455 baseEnd_84455 := by
    simpa [prefixWord, tailWord_84455, baseEnd_84455] using wordTrace_append hprefix tailTrace_84455
  have hstable : (prefixWord ++ tailWord_84455).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84455).length < 2 ^ (prefixWord ++ tailWord_84455).sum := by decide
  have hdescent : baseEnd_84455 < baseStart_84455 := by decide
  rcases family_descends (prefixWord ++ tailWord_84455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84512 : List Nat := [2, 1, 1, 6, 2, 1, 1, 5]
def baseStart_84512 : Nat := 118140960795 + 84512 * 2 ^ 59
def prefixEnd_84512 : Nat := 4983230072969 + 3 ^ 40 * 84512 * 2
def baseEnd_84512 : Nat := 25715719746891010436351

theorem tailTrace_84512 : CollatzResearch.WordTrace tailWord_84512 prefixEnd_84512 25715719746891010436351 := by
  unfold tailWord_84512
  simp only [CollatzResearch.WordTrace]
  refine ⟨1541202934917466172799895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2054937246556621563733193 1541202934917466172799895)
  ·
    refine ⟨2311804402376199259199843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1541202934917466172799895 2311804402376199259199843)
    ·
      refine ⟨3467706603564298888799765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2311804402376199259199843 3467706603564298888799765)
      ·
        refine ⟨162548747042076510412489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3467706603564298888799765 162548747042076510412489)
        ·
          refine ⟨121911560281557382809367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162548747042076510412489 121911560281557382809367)
          ·
            refine ⟨182867340422336074214051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121911560281557382809367 182867340422336074214051)
            ·
              refine ⟨274301010633504111321077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182867340422336074214051 274301010633504111321077)
              ·
                refine ⟨25715719746891010436351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 274301010633504111321077 25715719746891010436351)
                ·
                  rfl

theorem cell19_84512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_84512 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84512 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84512 prefixEnd_84512 := by exact prefixLift 84512
  have htrace : WordTrace (prefixWord ++ tailWord_84512) baseStart_84512 baseEnd_84512 := by
    simpa [prefixWord, tailWord_84512, baseEnd_84512] using wordTrace_append hprefix tailTrace_84512
  have hstable : (prefixWord ++ tailWord_84512).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84512).length < 2 ^ (prefixWord ++ tailWord_84512).sum := by decide
  have hdescent : baseEnd_84512 < baseStart_84512 := by decide
  rcases family_descends (prefixWord ++ tailWord_84512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84525 : List Nat := [1, 5, 4, 1, 2, 1, 5]
def baseStart_84525 : Nat := 118140960795 + 84525 * 2 ^ 59
def prefixEnd_84525 : Nat := 4983230072969 + 3 ^ 40 * 84525 * 2
def baseEnd_84525 : Nat := 8573225149903610715809

theorem tailTrace_84525 : CollatzResearch.WordTrace tailWord_84525 prefixEnd_84525 8573225149903610715809 := by
  unfold tailWord_84525
  simp only [CollatzResearch.WordTrace]
  refine ⟨3082880018787835565823029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2055253345858557043882019 3082880018787835565823029)
  ·
    refine ⟨289020001761359584295909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3082880018787835565823029 289020001761359584295909)
    ·
      refine ⟨54191250330254922055483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 289020001761359584295909 54191250330254922055483)
      ·
        refine ⟨81286875495382383083225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54191250330254922055483 81286875495382383083225)
        ·
          refine ⟨60965156621536787312419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81286875495382383083225 60965156621536787312419)
          ·
            refine ⟨91447734932305180968629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60965156621536787312419 91447734932305180968629)
            ·
              refine ⟨8573225149903610715809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91447734932305180968629 8573225149903610715809)
              ·
                rfl

theorem cell19_84525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 5].length) (baseStart_84525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84525 prefixEnd_84525 := by exact prefixLift 84525
  have htrace : WordTrace (prefixWord ++ tailWord_84525) baseStart_84525 baseEnd_84525 := by
    simpa [prefixWord, tailWord_84525, baseEnd_84525] using wordTrace_append hprefix tailTrace_84525
  have hstable : (prefixWord ++ tailWord_84525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84525).length < 2 ^ (prefixWord ++ tailWord_84525).sum := by decide
  have hdescent : baseEnd_84525 < baseStart_84525 := by decide
  rcases family_descends (prefixWord ++ tailWord_84525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84590 : List Nat := [4, 1, 2, 2, 2, 8]
def baseStart_84590 : Nat := 118140960795 + 84590 * 2 ^ 59
def prefixEnd_84590 : Nat := 4983230072969 + 3 ^ 40 * 84590 * 2
def baseEnd_84590 : Nat := 2859939329312215633645

theorem tailTrace_84590 : CollatzResearch.WordTrace tailWord_84590 prefixEnd_84590 2859939329312215633645 := by
  unfold tailWord_84590
  simp only [CollatzResearch.WordTrace]
  refine ⟨385656345444043958367403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2056833842368234444626149 385656345444043958367403)
  ·
    refine ⟨578484518166065937551105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 385656345444043958367403 578484518166065937551105)
    ·
      refine ⟨433863388624549453163329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 578484518166065937551105 433863388624549453163329)
      ·
        refine ⟨325397541468412089872497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433863388624549453163329 325397541468412089872497)
        ·
          refine ⟨244048156101309067404373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325397541468412089872497 244048156101309067404373)
          ·
            refine ⟨2859939329312215633645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 244048156101309067404373 2859939329312215633645)
            ·
              rfl

theorem cell19_84590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 8].length) (baseStart_84590 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84590 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84590 prefixEnd_84590 := by exact prefixLift 84590
  have htrace : WordTrace (prefixWord ++ tailWord_84590) baseStart_84590 baseEnd_84590 := by
    simpa [prefixWord, tailWord_84590, baseEnd_84590] using wordTrace_append hprefix tailTrace_84590
  have hstable : (prefixWord ++ tailWord_84590).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84590).length < 2 ^ (prefixWord ++ tailWord_84590).sum := by decide
  have hdescent : baseEnd_84590 < baseStart_84590 := by decide
  rcases family_descends (prefixWord ++ tailWord_84590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84592 : List Nat := [2, 1, 1, 1, 14]
def baseStart_84592 : Nat := 118140960795 + 84592 * 2 ^ 59
def prefixEnd_84592 : Nat := 4983230072969 + 3 ^ 40 * 84592 * 2
def baseEnd_84592 : Nat := 953335649387945505865

theorem tailTrace_84592 : CollatzResearch.WordTrace tailWord_84592 prefixEnd_84592 953335649387945505865 := by
  unfold tailWord_84592
  simp only [CollatzResearch.WordTrace]
  refine ⟨1542661854772553004256015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2056882473030070672341353 1542661854772553004256015)
  ·
    refine ⟨2313992782158829506384023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1542661854772553004256015 2313992782158829506384023)
    ·
      refine ⟨3470989173238244259576035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2313992782158829506384023 3470989173238244259576035)
      ·
        refine ⟨5206483759857366389364053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3470989173238244259576035 5206483759857366389364053)
        ·
          refine ⟨953335649387945505865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 5206483759857366389364053 953335649387945505865)
          ·
            rfl

theorem cell19_84592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 14].length) (baseStart_84592 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84592 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84592 prefixEnd_84592 := by exact prefixLift 84592
  have htrace : WordTrace (prefixWord ++ tailWord_84592) baseStart_84592 baseEnd_84592 := by
    simpa [prefixWord, tailWord_84592, baseEnd_84592] using wordTrace_append hprefix tailTrace_84592
  have hstable : (prefixWord ++ tailWord_84592).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84592).length < 2 ^ (prefixWord ++ tailWord_84592).sum := by decide
  have hdescent : baseEnd_84592 < baseStart_84592 := by decide
  rcases family_descends (prefixWord ++ tailWord_84592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84605 : List Nat := [1, 4, 1, 1, 6, 1, 1, 4]
def baseStart_84605 : Nat := 118140960795 + 84605 * 2 ^ 59
def prefixEnd_84605 : Nat := 4983230072969 + 3 ^ 40 * 84605 * 2
def baseEnd_84605 : Nat := 25744018236294350369431

theorem tailTrace_84605 : CollatzResearch.WordTrace tailWord_84605 prefixEnd_84605 25744018236294350369431 := by
  unfold tailWord_84605
  simp only [CollatzResearch.WordTrace]
  refine ⟨3085797858498009228735269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2057198572332006152490179 3085797858498009228735269)
  ·
    refine ⟨578587098468376730387863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3085797858498009228735269 578587098468376730387863)
    ·
      refine ⟨867880647702565095581795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 578587098468376730387863 867880647702565095581795)
      ·
        refine ⟨1301820971553847643372693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867880647702565095581795 1301820971553847643372693)
        ·
          refine ⟨61022858041586608283095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1301820971553847643372693 61022858041586608283095)
          ·
            refine ⟨91534287062379912424643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61022858041586608283095 91534287062379912424643)
            ·
              refine ⟨137301430593569868636965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91534287062379912424643 137301430593569868636965)
              ·
                refine ⟨25744018236294350369431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137301430593569868636965 25744018236294350369431)
                ·
                  rfl

theorem cell19_84605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 4].length) (baseStart_84605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84605 prefixEnd_84605 := by exact prefixLift 84605
  have htrace : WordTrace (prefixWord ++ tailWord_84605) baseStart_84605 baseEnd_84605 := by
    simpa [prefixWord, tailWord_84605, baseEnd_84605] using wordTrace_append hprefix tailTrace_84605
  have hstable : (prefixWord ++ tailWord_84605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84605).length < 2 ^ (prefixWord ++ tailWord_84605).sum := by decide
  have hdescent : baseEnd_84605 < baseStart_84605 := by decide
  rcases family_descends (prefixWord ++ tailWord_84605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84854 : List Nat := [5, 1, 1, 3, 1, 2, 1, 5]
def baseStart_84854 : Nat := 118140960795 + 84854 * 2 ^ 59
def prefixEnd_84854 : Nat := 4983230072969 + 3 ^ 40 * 84854 * 2
def baseEnd_84854 : Nat := 25819785159535550835419

theorem tailTrace_84854 : CollatzResearch.WordTrace tailWord_84854 prefixEnd_84854 25819785159535550835419 := by
  unfold tailWord_84854
  simp only [CollatzResearch.WordTrace]
  refine ⟨193429977162245297159351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2063253089730616503033077 193429977162245297159351)
  ·
    refine ⟨290144965743367945739027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193429977162245297159351 290144965743367945739027)
    ·
      refine ⟨435217448615051918608541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290144965743367945739027 435217448615051918608541)
      ·
        refine ⟨163206543230644469478203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 435217448615051918608541 163206543230644469478203)
        ·
          refine ⟨244809814845966704217305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163206543230644469478203 244809814845966704217305)
          ·
            refine ⟨183607361134475028162979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244809814845966704217305 183607361134475028162979)
            ·
              refine ⟨275411041701712542244469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183607361134475028162979 275411041701712542244469)
              ·
                refine ⟨25819785159535550835419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 275411041701712542244469 25819785159535550835419)
                ·
                  rfl

theorem cell19_84854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_84854 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84854 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84854 prefixEnd_84854 := by exact prefixLift 84854
  have htrace : WordTrace (prefixWord ++ tailWord_84854) baseStart_84854 baseEnd_84854 := by
    simpa [prefixWord, tailWord_84854, baseEnd_84854] using wordTrace_append hprefix tailTrace_84854
  have hstable : (prefixWord ++ tailWord_84854).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84854).length < 2 ^ (prefixWord ++ tailWord_84854).sum := by decide
  have hdescent : baseEnd_84854 < baseStart_84854 := by decide
  rcases family_descends (prefixWord ++ tailWord_84854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84892 : List Nat := [2, 2, 3, 3, 2, 1, 2, 4]
def baseStart_84892 : Nat := 118140960795 + 84892 * 2 ^ 59
def prefixEnd_84892 : Nat := 4983230072969 + 3 ^ 40 * 84892 * 2
def baseEnd_84892 : Nat := 25831347983162721990871

theorem tailTrace_84892 : CollatzResearch.WordTrace tailWord_84892 prefixEnd_84892 25831347983162721990871 := by
  unfold tailWord_84892
  simp only [CollatzResearch.WordTrace]
  refine ⟨1548132804229128622216465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2064177072305504829621953 1548132804229128622216465)
  ·
    refine ⟨1161099603171846466662349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1548132804229128622216465 1161099603171846466662349)
    ·
      refine ⟨435412351189442424998381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1161099603171846466662349 435412351189442424998381)
      ·
        refine ⟨163279631696040909374393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 435412351189442424998381 163279631696040909374393)
        ·
          refine ⟨122459723772030682030795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163279631696040909374393 122459723772030682030795)
          ·
            refine ⟨183689585658046023046193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122459723772030682030795 183689585658046023046193)
            ·
              refine ⟨137767189243534517284645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183689585658046023046193 137767189243534517284645)
              ·
                refine ⟨25831347983162721990871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137767189243534517284645 25831347983162721990871)
                ·
                  rfl

theorem cell19_84892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_84892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84892 prefixEnd_84892 := by exact prefixLift 84892
  have htrace : WordTrace (prefixWord ++ tailWord_84892) baseStart_84892 baseEnd_84892 := by
    simpa [prefixWord, tailWord_84892, baseEnd_84892] using wordTrace_append hprefix tailTrace_84892
  have hstable : (prefixWord ++ tailWord_84892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84892).length < 2 ^ (prefixWord ++ tailWord_84892).sum := by decide
  have hdescent : baseEnd_84892 < baseStart_84892 := by decide
  rcases family_descends (prefixWord ++ tailWord_84892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84896 : List Nat := [2, 1, 1, 4, 1, 1, 3, 6]
def baseStart_84896 : Nat := 118140960795 + 84896 * 2 ^ 59
def prefixEnd_84896 : Nat := 4983230072969 + 3 ^ 40 * 84896 * 2
def baseEnd_84896 : Nat := 25832565122491897901971

theorem tailTrace_84896 : CollatzResearch.WordTrace tailWord_84896 prefixEnd_84896 25832565122491897901971 := by
  unfold tailWord_84896
  simp only [CollatzResearch.WordTrace]
  refine ⟨1548205750221882963789271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2064274333629177285052361 1548205750221882963789271)
  ·
    refine ⟨2322308625332824445683907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1548205750221882963789271 2322308625332824445683907)
    ·
      refine ⟨3483462937999236668525861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2322308625332824445683907 3483462937999236668525861)
      ·
        refine ⟨653149300874856875348599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3483462937999236668525861 653149300874856875348599)
        ·
          refine ⟨979723951312285313022899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653149300874856875348599 979723951312285313022899)
          ·
            refine ⟨1469585926968427969534349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979723951312285313022899 1469585926968427969534349)
            ·
              refine ⟨551094722613160488575381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1469585926968427969534349 551094722613160488575381)
              ·
                refine ⟨25832565122491897901971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 551094722613160488575381 25832565122491897901971)
                ·
                  rfl

theorem cell19_84896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_84896 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84896 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84896 prefixEnd_84896 := by exact prefixLift 84896
  have htrace : WordTrace (prefixWord ++ tailWord_84896) baseStart_84896 baseEnd_84896 := by
    simpa [prefixWord, tailWord_84896, baseEnd_84896] using wordTrace_append hprefix tailTrace_84896
  have hstable : (prefixWord ++ tailWord_84896).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84896).length < 2 ^ (prefixWord ++ tailWord_84896).sum := by decide
  have hdescent : baseEnd_84896 < baseStart_84896 := by decide
  rcases family_descends (prefixWord ++ tailWord_84896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84932 : List Nat := [2, 3, 3, 3, 8]
def baseStart_84932 : Nat := 118140960795 + 84932 * 2 ^ 59
def prefixEnd_84932 : Nat := 4983230072969 + 3 ^ 40 * 84932 * 2
def baseEnd_84932 : Nat := 957167384313128929699

theorem tailTrace_84932 : CollatzResearch.WordTrace tailWord_84932 prefixEnd_84932 957167384313128929699 := by
  unfold tailWord_84932
  simp only [CollatzResearch.WordTrace]
  refine ⟨1548862264156672037944525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2065149685542229383926033 1548862264156672037944525)
  ·
    refine ⟨580823349058752014229197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1548862264156672037944525 580823349058752014229197)
    ·
      refine ⟨217808755897032005335949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 580823349058752014229197 217808755897032005335949)
      ·
        refine ⟨81678283461387002000981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217808755897032005335949 81678283461387002000981)
        ·
          refine ⟨957167384313128929699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 81678283461387002000981 957167384313128929699)
          ·
            rfl

theorem cell19_84932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 8].length) (baseStart_84932 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84932 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84932 prefixEnd_84932 := by exact prefixLift 84932
  have htrace : WordTrace (prefixWord ++ tailWord_84932) baseStart_84932 baseEnd_84932 := by
    simpa [prefixWord, tailWord_84932, baseEnd_84932] using wordTrace_append hprefix tailTrace_84932
  have hstable : (prefixWord ++ tailWord_84932).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84932).length < 2 ^ (prefixWord ++ tailWord_84932).sum := by decide
  have hdescent : baseEnd_84932 < baseStart_84932 := by decide
  rcases family_descends (prefixWord ++ tailWord_84932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84949 : List Nat := [1, 3, 2, 3, 3, 2, 1, 4]
def baseStart_84949 : Nat := 118140960795 + 84949 * 2 ^ 59
def prefixEnd_84949 : Nat := 4983230072969 + 3 ^ 40 * 84949 * 2
def baseEnd_84949 : Nat := 25848692218603478724049

theorem tailTrace_84949 : CollatzResearch.WordTrace tailWord_84949 prefixEnd_84949 25848692218603478724049 := by
  unfold tailWord_84949
  simp only [CollatzResearch.WordTrace]
  refine ⟨3098344569251755979257901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2065563046167837319505267 3098344569251755979257901)
  ·
    refine ⟨1161879213469408492221713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3098344569251755979257901 1161879213469408492221713)
    ·
      refine ⟨871409410102056369166285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1161879213469408492221713 871409410102056369166285)
      ·
        refine ⟨326778528788271138437357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 871409410102056369166285 326778528788271138437357)
        ·
          refine ⟨122541948295601676914009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326778528788271138437357 122541948295601676914009)
          ·
            refine ⟨91906461221701257685507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122541948295601676914009 91906461221701257685507)
            ·
              refine ⟨137859691832551886528261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91906461221701257685507 137859691832551886528261)
              ·
                refine ⟨25848692218603478724049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137859691832551886528261 25848692218603478724049)
                ·
                  rfl

theorem cell19_84949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 4].length) (baseStart_84949 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_84949 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_84949 prefixEnd_84949 := by exact prefixLift 84949
  have htrace : WordTrace (prefixWord ++ tailWord_84949) baseStart_84949 baseEnd_84949 := by
    simpa [prefixWord, tailWord_84949, baseEnd_84949] using wordTrace_append hprefix tailTrace_84949
  have hstable : (prefixWord ++ tailWord_84949).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84949).length < 2 ^ (prefixWord ++ tailWord_84949).sum := by decide
  have hdescent : baseEnd_84949 < baseStart_84949 := by decide
  rcases family_descends (prefixWord ++ tailWord_84949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85025 : List Nat := [1, 2, 3, 2, 3, 3, 2, 3]
def baseStart_85025 : Nat := 118140960795 + 85025 * 2 ^ 59
def prefixEnd_85025 : Nat := 4983230072969 + 3 ^ 40 * 85025 * 2
def baseEnd_85025 : Nat := 25871817865857821034953

theorem tailTrace_85025 : CollatzResearch.WordTrace tailWord_85025 prefixEnd_85025 25871817865857821034953 := by
  unfold tailWord_85025
  simp only [CollatzResearch.WordTrace]
  refine ⟨3101116516976420959024529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2067411011317613972683019 3101116516976420959024529)
  ·
    refine ⟨2325837387732315719268397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3101116516976420959024529 2325837387732315719268397)
    ·
      refine ⟨872189020399618394725649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2325837387732315719268397 872189020399618394725649)
      ·
        refine ⟨654141765299713796044237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 872189020399618394725649 654141765299713796044237)
        ·
          refine ⟨245303161987392673516589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 654141765299713796044237 245303161987392673516589)
          ·
            refine ⟨91988685745272252568721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245303161987392673516589 91988685745272252568721)
            ·
              refine ⟨68991514308954189426541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91988685745272252568721 68991514308954189426541)
              ·
                refine ⟨25871817865857821034953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68991514308954189426541 25871817865857821034953)
                ·
                  rfl

theorem cell19_85025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 3].length) (baseStart_85025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85025 prefixEnd_85025 := by exact prefixLift 85025
  have htrace : WordTrace (prefixWord ++ tailWord_85025) baseStart_85025 baseEnd_85025 := by
    simpa [prefixWord, tailWord_85025, baseEnd_85025] using wordTrace_append hprefix tailTrace_85025
  have hstable : (prefixWord ++ tailWord_85025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85025).length < 2 ^ (prefixWord ++ tailWord_85025).sum := by decide
  have hdescent : baseEnd_85025 < baseStart_85025 := by decide
  rcases family_descends (prefixWord ++ tailWord_85025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85027 : List Nat := [1, 1, 1, 4, 3, 2, 4, 3]
def baseStart_85027 : Nat := 118140960795 + 85027 * 2 ^ 59
def prefixEnd_85027 : Nat := 4983230072969 + 3 ^ 40 * 85027 * 2
def baseEnd_85027 : Nat := 25872426435522408990503

theorem tailTrace_85027 : CollatzResearch.WordTrace tailWord_85027 prefixEnd_85027 25872426435522408990503 := by
  unfold tailWord_85027
  simp only [CollatzResearch.WordTrace]
  refine ⟨3101189462969175300597335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2067459641979450200398223 3101189462969175300597335)
  ·
    refine ⟨4651784194453762950896003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3101189462969175300597335 4651784194453762950896003)
    ·
      refine ⟨6977676291680644426344005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4651784194453762950896003 6977676291680644426344005)
      ·
        refine ⟨1308314304690120829939501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6977676291680644426344005 1308314304690120829939501)
        ·
          refine ⟨490617864258795311227313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1308314304690120829939501 490617864258795311227313)
          ·
            refine ⟨367963398194096483420485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490617864258795311227313 367963398194096483420485)
            ·
              refine ⟨68993137161393090641341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 367963398194096483420485 68993137161393090641341)
              ·
                refine ⟨25872426435522408990503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68993137161393090641341 25872426435522408990503)
                ·
                  rfl

theorem cell19_85027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 3].length) (baseStart_85027 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85027 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85027 prefixEnd_85027 := by exact prefixLift 85027
  have htrace : WordTrace (prefixWord ++ tailWord_85027) baseStart_85027 baseEnd_85027 := by
    simpa [prefixWord, tailWord_85027, baseEnd_85027] using wordTrace_append hprefix tailTrace_85027
  have hstable : (prefixWord ++ tailWord_85027).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85027).length < 2 ^ (prefixWord ++ tailWord_85027).sum := by decide
  have hdescent : baseEnd_85027 < baseStart_85027 := by decide
  rcases family_descends (prefixWord ++ tailWord_85027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85029 : List Nat := [1, 3, 1, 2, 2, 2, 3, 5]
def baseStart_85029 : Nat := 118140960795 + 85029 * 2 ^ 59
def prefixEnd_85029 : Nat := 4983230072969 + 3 ^ 40 * 85029 * 2
def baseEnd_85029 : Nat := 25873035005186996946053

theorem tailTrace_85029 : CollatzResearch.WordTrace tailWord_85029 prefixEnd_85029 25873035005186996946053 := by
  unfold tailWord_85029
  simp only [CollatzResearch.WordTrace]
  refine ⟨3101262408961929642170141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2067508272641286428113427 3101262408961929642170141)
  ·
    refine ⟨1162973403360723615813803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3101262408961929642170141 1162973403360723615813803)
    ·
      refine ⟨1744460105041085423720705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1162973403360723615813803 1744460105041085423720705)
      ·
        refine ⟨1308345078780814067790529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1744460105041085423720705 1308345078780814067790529)
        ·
          refine ⟨981258809085610550842897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1308345078780814067790529 981258809085610550842897)
          ·
            refine ⟨735944106814207913132173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 981258809085610550842897 735944106814207913132173)
            ·
              refine ⟨275979040055327967424565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 735944106814207913132173 275979040055327967424565)
              ·
                refine ⟨25873035005186996946053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 275979040055327967424565 25873035005186996946053)
                ·
                  rfl

theorem cell19_85029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_85029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85029 prefixEnd_85029 := by exact prefixLift 85029
  have htrace : WordTrace (prefixWord ++ tailWord_85029) baseStart_85029 baseEnd_85029 := by
    simpa [prefixWord, tailWord_85029, baseEnd_85029] using wordTrace_append hprefix tailTrace_85029
  have hstable : (prefixWord ++ tailWord_85029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85029).length < 2 ^ (prefixWord ++ tailWord_85029).sum := by decide
  have hdescent : baseEnd_85029 < baseStart_85029 := by decide
  rcases family_descends (prefixWord ++ tailWord_85029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85044 : List Nat := [2, 5, 1, 2, 1, 3, 5]
def baseStart_85044 : Nat := 118140960795 + 85044 * 2 ^ 59
def prefixEnd_85044 : Nat := 4983230072969 + 3 ^ 40 * 85044 * 2
def baseEnd_85044 : Nat := 8625866425890468870893

theorem tailTrace_85044 : CollatzResearch.WordTrace tailWord_85044 prefixEnd_85044 8625866425890468870893 := by
  unfold tailWord_85044
  simp only [CollatzResearch.WordTrace]
  refine ⟨1550904751953793601983093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2067873002605058135977457 1550904751953793601983093)
  ·
    refine ⟨145397320495668150185915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1550904751953793601983093 145397320495668150185915)
    ·
      refine ⟨218095980743502225278873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145397320495668150185915 218095980743502225278873)
      ·
        refine ⟨163571985557626668959155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218095980743502225278873 163571985557626668959155)
        ·
          refine ⟨245357978336440003438733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163571985557626668959155 245357978336440003438733)
          ·
            refine ⟨92009241876165001289525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245357978336440003438733 92009241876165001289525)
            ·
              refine ⟨8625866425890468870893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92009241876165001289525 8625866425890468870893)
              ·
                rfl

theorem cell19_85044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 5].length) (baseStart_85044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85044 prefixEnd_85044 := by exact prefixLift 85044
  have htrace : WordTrace (prefixWord ++ tailWord_85044) baseStart_85044 baseEnd_85044 := by
    simpa [prefixWord, tailWord_85044, baseEnd_85044] using wordTrace_append hprefix tailTrace_85044
  have hstable : (prefixWord ++ tailWord_85044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85044).length < 2 ^ (prefixWord ++ tailWord_85044).sum := by decide
  have hdescent : baseEnd_85044 < baseStart_85044 := by decide
  rcases family_descends (prefixWord ++ tailWord_85044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85046 : List Nat := [5, 1, 2, 1, 1, 2, 7]
def baseStart_85046 : Nat := 118140960795 + 85046 * 2 ^ 59
def prefixEnd_85046 : Nat := 4983230072969 + 3 ^ 40 * 85046 * 2
def baseEnd_85046 : Nat := 8626069282445331522743

theorem tailTrace_85046 : CollatzResearch.WordTrace tailWord_85046 prefixEnd_85046 8626069282445331522743 := by
  unfold tailWord_85046
  simp only [CollatzResearch.WordTrace]
  refine ⟨193867653118771346596187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2067921633266894363692661 193867653118771346596187)
  ·
    refine ⟨290801479678157019894281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193867653118771346596187 290801479678157019894281)
    ·
      refine ⟨218101109758617764920711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290801479678157019894281 218101109758617764920711)
      ·
        refine ⟨327151664637926647381067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218101109758617764920711 327151664637926647381067)
        ·
          refine ⟨490727496956889971071601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327151664637926647381067 490727496956889971071601)
          ·
            refine ⟨368045622717667478303701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490727496956889971071601 368045622717667478303701)
            ·
              refine ⟨8626069282445331522743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 368045622717667478303701 8626069282445331522743)
              ·
                rfl

theorem cell19_85046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 7].length) (baseStart_85046 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85046 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85046 prefixEnd_85046 := by exact prefixLift 85046
  have htrace : WordTrace (prefixWord ++ tailWord_85046) baseStart_85046 baseEnd_85046 := by
    simpa [prefixWord, tailWord_85046, baseEnd_85046] using wordTrace_append hprefix tailTrace_85046
  have hstable : (prefixWord ++ tailWord_85046).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85046).length < 2 ^ (prefixWord ++ tailWord_85046).sum := by decide
  have hdescent : baseEnd_85046 < baseStart_85046 := by decide
  rcases family_descends (prefixWord ++ tailWord_85046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85048 : List Nat := [2, 1, 2, 1, 5, 1, 7]
def baseStart_85048 : Nat := 118140960795 + 85048 * 2 ^ 59
def prefixEnd_85048 : Nat := 4983230072969 + 3 ^ 40 * 85048 * 2
def baseEnd_85048 : Nat := 8626272139000194174593

theorem tailTrace_85048 : CollatzResearch.WordTrace tailWord_85048 prefixEnd_85048 8626272139000194174593 := by
  unfold tailWord_85048
  simp only [CollatzResearch.WordTrace]
  refine ⟨1550977697946547943555899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2067970263928730591407865 1550977697946547943555899)
  ·
    refine ⟨2326466546919821915333849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1550977697946547943555899 2326466546919821915333849)
    ·
      refine ⟨1744849910189866436500387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2326466546919821915333849 1744849910189866436500387)
      ·
        refine ⟨2617274865284799654750581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1744849910189866436500387 2617274865284799654750581)
        ·
          refine ⟨245369518620449967632867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2617274865284799654750581 245369518620449967632867)
          ·
            refine ⟨368054277930674951449301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245369518620449967632867 368054277930674951449301)
            ·
              refine ⟨8626272139000194174593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 368054277930674951449301 8626272139000194174593)
              ·
                rfl

theorem cell19_85048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 7].length) (baseStart_85048 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85048 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85048 prefixEnd_85048 := by exact prefixLift 85048
  have htrace : WordTrace (prefixWord ++ tailWord_85048) baseStart_85048 baseEnd_85048 := by
    simpa [prefixWord, tailWord_85048, baseEnd_85048] using wordTrace_append hprefix tailTrace_85048
  have hstable : (prefixWord ++ tailWord_85048).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85048).length < 2 ^ (prefixWord ++ tailWord_85048).sum := by decide
  have hdescent : baseEnd_85048 < baseStart_85048 := by decide
  rcases family_descends (prefixWord ++ tailWord_85048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85190 : List Nat := [6, 1, 2, 2, 1, 2, 2, 3]
def baseStart_85190 : Nat := 118140960795 + 85190 * 2 ^ 59
def prefixEnd_85190 : Nat := 4983230072969 + 3 ^ 40 * 85190 * 2
def baseEnd_85190 : Nat := 25922024863186327367837

theorem tailTrace_85190 : CollatzResearch.WordTrace tailWord_85190 prefixEnd_85190 25922024863186327367837 := by
  unfold tailWord_85190
  simp only [CollatzResearch.WordTrace]
  refine ⟨97097955043082941836907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2071423040919102759187349 97097955043082941836907)
  ·
    refine ⟨145646932564624412755361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97097955043082941836907 145646932564624412755361)
    ·
      refine ⟨109235199423468309566521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145646932564624412755361 109235199423468309566521)
      ·
        refine ⟨81926399567601232174891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109235199423468309566521 81926399567601232174891)
        ·
          refine ⟨122889599351401848262337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81926399567601232174891 122889599351401848262337)
          ·
            refine ⟨92167199513551386196753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122889599351401848262337 92167199513551386196753)
            ·
              refine ⟨69125399635163539647565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92167199513551386196753 69125399635163539647565)
              ·
                refine ⟨25922024863186327367837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69125399635163539647565 25922024863186327367837)
                ·
                  rfl

theorem cell19_85190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_85190 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85190 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85190 prefixEnd_85190 := by exact prefixLift 85190
  have htrace : WordTrace (prefixWord ++ tailWord_85190) baseStart_85190 baseEnd_85190 := by
    simpa [prefixWord, tailWord_85190, baseEnd_85190] using wordTrace_append hprefix tailTrace_85190
  have hstable : (prefixWord ++ tailWord_85190).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85190).length < 2 ^ (prefixWord ++ tailWord_85190).sum := by decide
  have hdescent : baseEnd_85190 < baseStart_85190 := by decide
  rcases family_descends (prefixWord ++ tailWord_85190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85198 : List Nat := [4, 1, 1, 1, 5, 1, 1, 5]
def baseStart_85198 : Nat := 118140960795 + 85198 * 2 ^ 59
def prefixEnd_85198 : Nat := 4983230072969 + 3 ^ 40 * 85198 * 2
def baseEnd_85198 : Nat := 25924459141844679190037

theorem tailTrace_85198 : CollatzResearch.WordTrace tailWord_85198 prefixEnd_85198 25924459141844679190037 := by
  unfold tailWord_85198
  simp only [CollatzResearch.WordTrace]
  refine ⟨388428293168708938134031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2071617563566447670048165 388428293168708938134031)
  ·
    refine ⟨582642439753063407201047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 388428293168708938134031 582642439753063407201047)
    ·
      refine ⟨873963659629595110801571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 582642439753063407201047 873963659629595110801571)
      ·
        refine ⟨1310945489444392666202357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873963659629595110801571 1310945489444392666202357)
        ·
          refine ⟨122901139635411812456471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1310945489444392666202357 122901139635411812456471)
          ·
            refine ⟨184351709453117718684707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122901139635411812456471 184351709453117718684707)
            ·
              refine ⟨276527564179676578027061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184351709453117718684707 276527564179676578027061)
              ·
                refine ⟨25924459141844679190037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 276527564179676578027061 25924459141844679190037)
                ·
                  rfl

theorem cell19_85198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_85198 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85198 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85198 prefixEnd_85198 := by exact prefixLift 85198
  have htrace : WordTrace (prefixWord ++ tailWord_85198) baseStart_85198 baseEnd_85198 := by
    simpa [prefixWord, tailWord_85198, baseEnd_85198] using wordTrace_append hprefix tailTrace_85198
  have hstable : (prefixWord ++ tailWord_85198).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85198).length < 2 ^ (prefixWord ++ tailWord_85198).sum := by decide
  have hdescent : baseEnd_85198 < baseStart_85198 := by decide
  rcases family_descends (prefixWord ++ tailWord_85198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85333 : List Nat := [1, 3, 2, 2, 3, 2, 6]
def baseStart_85333 : Nat := 118140960795 + 85333 * 2 ^ 59
def prefixEnd_85333 : Nat := 4983230072969 + 3 ^ 40 * 85333 * 2
def baseEnd_85333 : Nat := 8655179198068122063223

theorem tailTrace_85333 : CollatzResearch.WordTrace tailWord_85333 prefixEnd_85333 8655179198068122063223 := by
  unfold tailWord_85333
  simp only [CollatzResearch.WordTrace]
  refine ⟨3112350199860589561236653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2074900133240393040824435 3112350199860589561236653)
  ·
    refine ⟨1167131324947721085463745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3112350199860589561236653 1167131324947721085463745)
    ·
      refine ⟨875348493710790814097809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1167131324947721085463745 875348493710790814097809)
      ·
        refine ⟨656511370283093110573357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 875348493710790814097809 656511370283093110573357)
        ·
          refine ⟨246191763856159916465009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 656511370283093110573357 246191763856159916465009)
          ·
            refine ⟨184643822892119937348757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246191763856159916465009 184643822892119937348757)
            ·
              refine ⟨8655179198068122063223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 184643822892119937348757 8655179198068122063223)
              ·
                rfl

theorem cell19_85333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 6].length) (baseStart_85333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85333 prefixEnd_85333 := by exact prefixLift 85333
  have htrace : WordTrace (prefixWord ++ tailWord_85333) baseStart_85333 baseEnd_85333 := by
    simpa [prefixWord, tailWord_85333, baseEnd_85333] using wordTrace_append hprefix tailTrace_85333
  have hstable : (prefixWord ++ tailWord_85333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85333).length < 2 ^ (prefixWord ++ tailWord_85333).sum := by decide
  have hdescent : baseEnd_85333 < baseStart_85333 := by decide
  rcases family_descends (prefixWord ++ tailWord_85333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85365 : List Nat := [1, 3, 4, 1, 4, 1, 2, 3]
def baseStart_85365 : Nat := 118140960795 + 85365 * 2 ^ 59
def prefixEnd_85365 : Nat := 4983230072969 + 3 ^ 40 * 85365 * 2
def baseEnd_85365 : Nat := 25975274708837773478471

theorem tailTrace_85365 : CollatzResearch.WordTrace tailWord_85365 prefixEnd_85365 25975274708837773478471 := by
  unfold tailWord_85365
  simp only [CollatzResearch.WordTrace]
  refine ⟨3113517335744659026401549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2075678223829772684267699 3113517335744659026401549)
  ·
    refine ⟨1167569000904247134900581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3113517335744659026401549 1167569000904247134900581)
    ·
      refine ⟨218919187669546337793859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1167569000904247134900581 218919187669546337793859)
      ·
        refine ⟨328378781504319506690789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218919187669546337793859 328378781504319506690789)
        ·
          refine ⟨61571021532059907504523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 328378781504319506690789 61571021532059907504523)
          ·
            refine ⟨92356532298089861256785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61571021532059907504523 92356532298089861256785)
            ·
              refine ⟨69267399223567395942589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92356532298089861256785 69267399223567395942589)
              ·
                refine ⟨25975274708837773478471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69267399223567395942589 25975274708837773478471)
                ·
                  rfl

theorem cell19_85365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 3].length) (baseStart_85365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85365 prefixEnd_85365 := by exact prefixLift 85365
  have htrace : WordTrace (prefixWord ++ tailWord_85365) baseStart_85365 baseEnd_85365 := by
    simpa [prefixWord, tailWord_85365, baseEnd_85365] using wordTrace_append hprefix tailTrace_85365
  have hstable : (prefixWord ++ tailWord_85365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85365).length < 2 ^ (prefixWord ++ tailWord_85365).sum := by decide
  have hdescent : baseEnd_85365 < baseStart_85365 := by decide
  rcases family_descends (prefixWord ++ tailWord_85365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85462 : List Nat := [5, 2, 1, 1, 1, 4, 1, 4]
def baseStart_85462 : Nat := 118140960795 + 85462 * 2 ^ 59
def prefixEnd_85462 : Nat := 4983230072969 + 3 ^ 40 * 85462 * 2
def baseEnd_85462 : Nat := 26004790337570289322651

theorem tailTrace_85462 : CollatzResearch.WordTrace tailWord_85462 prefixEnd_85462 26004790337570289322651 := by
  unfold tailWord_85462
  simp only [CollatzResearch.WordTrace]
  refine ⟨194815951024577787042665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2078036810928829728455093 194815951024577787042665)
  ·
    refine ⟨146111963268433340281999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194815951024577787042665 146111963268433340281999)
    ·
      refine ⟨219167944902650010422999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146111963268433340281999 219167944902650010422999)
      ·
        refine ⟨328751917353975015634499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219167944902650010422999 328751917353975015634499)
        ·
          refine ⟨493127876030962523451749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328751917353975015634499 493127876030962523451749)
          ·
            refine ⟨92461476755805473147203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 493127876030962523451749 92461476755805473147203)
            ·
              refine ⟨138692215133708209720805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92461476755805473147203 138692215133708209720805)
              ·
                refine ⟨26004790337570289322651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138692215133708209720805 26004790337570289322651)
                ·
                  rfl

theorem cell19_85462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_85462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85462 prefixEnd_85462 := by exact prefixLift 85462
  have htrace : WordTrace (prefixWord ++ tailWord_85462) baseStart_85462 baseEnd_85462 := by
    simpa [prefixWord, tailWord_85462, baseEnd_85462] using wordTrace_append hprefix tailTrace_85462
  have hstable : (prefixWord ++ tailWord_85462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85462).length < 2 ^ (prefixWord ++ tailWord_85462).sum := by decide
  have hdescent : baseEnd_85462 < baseStart_85462 := by decide
  rcases family_descends (prefixWord ++ tailWord_85462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85466 : List Nat := [3, 1, 1, 2, 3, 2, 3, 4]
def baseStart_85466 : Nat := 118140960795 + 85466 * 2 ^ 59
def prefixEnd_85466 : Nat := 4983230072969 + 3 ^ 40 * 85466 * 2
def baseEnd_85466 : Nat := 26006007476899465233751

theorem tailTrace_85466 : CollatzResearch.WordTrace tailWord_85466 prefixEnd_85466 26006007476899465233751 := by
  unfold tailWord_85466
  simp only [CollatzResearch.WordTrace]
  refine ⟨779300277094688318957063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2078134072252502183885501 779300277094688318957063)
  ·
    refine ⟨1168950415642032478435595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 779300277094688318957063 1168950415642032478435595)
    ·
      refine ⟨1753425623463048717653393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1168950415642032478435595 1753425623463048717653393)
      ·
        refine ⟨1315069217597286538240045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1753425623463048717653393 1315069217597286538240045)
        ·
          refine ⟨493150956598982451840017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1315069217597286538240045 493150956598982451840017)
          ·
            refine ⟨369863217449236838880013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493150956598982451840017 369863217449236838880013)
            ·
              refine ⟨138698706543463814580005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 369863217449236838880013 138698706543463814580005)
              ·
                refine ⟨26006007476899465233751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138698706543463814580005 26006007476899465233751)
                ·
                  rfl

theorem cell19_85466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_85466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85466 prefixEnd_85466 := by exact prefixLift 85466
  have htrace : WordTrace (prefixWord ++ tailWord_85466) baseStart_85466 baseEnd_85466 := by
    simpa [prefixWord, tailWord_85466, baseEnd_85466] using wordTrace_append hprefix tailTrace_85466
  have hstable : (prefixWord ++ tailWord_85466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85466).length < 2 ^ (prefixWord ++ tailWord_85466).sum := by decide
  have hdescent : baseEnd_85466 < baseStart_85466 := by decide
  rcases family_descends (prefixWord ++ tailWord_85466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85487 : List Nat := [1, 1, 2, 1, 4, 1, 2, 7]
def baseStart_85487 : Nat := 118140960795 + 85487 * 2 ^ 59
def prefixEnd_85487 : Nat := 4983230072969 + 3 ^ 40 * 85487 * 2
def baseEnd_85487 : Nat := 26012397458377638767027

theorem tailTrace_85487 : CollatzResearch.WordTrace tailWord_85487 prefixEnd_85487 26012397458377638767027 := by
  unfold tailWord_85487
  simp only [CollatzResearch.WordTrace]
  refine ⟨3117967041302673862342715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2078644694201782574895143 3117967041302673862342715)
  ·
    refine ⟨4676950561954010793514073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3117967041302673862342715 4676950561954010793514073)
    ·
      refine ⟨3507712921465508095135555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4676950561954010793514073 3507712921465508095135555)
      ·
        refine ⟨5261569382198262142703333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3507712921465508095135555 5261569382198262142703333)
        ·
          refine ⟨986544259162174151756875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5261569382198262142703333 986544259162174151756875)
          ·
            refine ⟨1479816388743261227635313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 986544259162174151756875 1479816388743261227635313)
            ·
              refine ⟨1109862291557445920726485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1479816388743261227635313 1109862291557445920726485)
              ·
                refine ⟨26012397458377638767027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1109862291557445920726485 26012397458377638767027)
                ·
                  rfl

theorem cell19_85487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_85487 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85487 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85487 prefixEnd_85487 := by exact prefixLift 85487
  have htrace : WordTrace (prefixWord ++ tailWord_85487) baseStart_85487 baseEnd_85487 := by
    simpa [prefixWord, tailWord_85487, baseEnd_85487] using wordTrace_append hprefix tailTrace_85487
  have hstable : (prefixWord ++ tailWord_85487).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85487).length < 2 ^ (prefixWord ++ tailWord_85487).sum := by decide
  have hdescent : baseEnd_85487 < baseStart_85487 := by decide
  rcases family_descends (prefixWord ++ tailWord_85487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85561 : List Nat := [1, 2, 1, 5, 1, 4, 5]
def baseStart_85561 : Nat := 118140960795 + 85561 * 2 ^ 59
def prefixEnd_85561 : Nat := 4983230072969 + 3 ^ 40 * 85561 * 2
def baseEnd_85561 : Nat := 8678304845322464374127

theorem tailTrace_85561 : CollatzResearch.WordTrace tailWord_85561 prefixEnd_85561 8678304845322464374127 := by
  unfold tailWord_85561
  simp only [CollatzResearch.WordTrace]
  refine ⟨3120666043034584500536537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2080444028689723000357691 3120666043034584500536537)
  ·
    refine ⟨2340499532275938375402403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3120666043034584500536537 2340499532275938375402403)
    ·
      refine ⟨3510749298413907563103605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2340499532275938375402403 3510749298413907563103605)
      ·
        refine ⟨329132746726303834040963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3510749298413907563103605 329132746726303834040963)
        ·
          refine ⟨493699120089455751061445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329132746726303834040963 493699120089455751061445)
          ·
            refine ⟨92568585016772953324021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 493699120089455751061445 92568585016772953324021)
            ·
              refine ⟨8678304845322464374127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92568585016772953324021 8678304845322464374127)
              ·
                rfl

theorem cell19_85561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 5].length) (baseStart_85561 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85561 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85561 prefixEnd_85561 := by exact prefixLift 85561
  have htrace : WordTrace (prefixWord ++ tailWord_85561) baseStart_85561 baseEnd_85561 := by
    simpa [prefixWord, tailWord_85561, baseEnd_85561] using wordTrace_append hprefix tailTrace_85561
  have hstable : (prefixWord ++ tailWord_85561).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85561).length < 2 ^ (prefixWord ++ tailWord_85561).sum := by decide
  have hdescent : baseEnd_85561 < baseStart_85561 := by decide
  rcases family_descends (prefixWord ++ tailWord_85561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85580 : List Nat := [2, 2, 1, 3, 1, 4, 2, 4]
def baseStart_85580 : Nat := 118140960795 + 85580 * 2 ^ 59
def prefixEnd_85580 : Nat := 4983230072969 + 3 ^ 40 * 85580 * 2
def baseEnd_85580 : Nat := 26040695947780978700107

theorem tailTrace_85580 : CollatzResearch.WordTrace tailWord_85580 prefixEnd_85580 26040695947780978700107 := by
  unfold tailWord_85580
  simp only [CollatzResearch.WordTrace]
  refine ⟨1560679514982875372739097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2080906019977167163652129 1560679514982875372739097)
  ·
    refine ⟨1170509636237156529554323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1560679514982875372739097 1170509636237156529554323)
    ·
      refine ⟨1755764454355734794331485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1170509636237156529554323 1755764454355734794331485)
      ·
        refine ⟨658411670383400547874307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1755764454355734794331485 658411670383400547874307)
        ·
          refine ⟨987617505575100821811461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658411670383400547874307 987617505575100821811461)
          ·
            refine ⟨185178282295331404089649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 987617505575100821811461 185178282295331404089649)
            ·
              refine ⟨138883711721498553067237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185178282295331404089649 138883711721498553067237)
              ·
                refine ⟨26040695947780978700107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138883711721498553067237 26040695947780978700107)
                ·
                  rfl

theorem cell19_85580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_85580 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85580 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85580 prefixEnd_85580 := by exact prefixLift 85580
  have htrace : WordTrace (prefixWord ++ tailWord_85580) baseStart_85580 baseEnd_85580 := by
    simpa [prefixWord, tailWord_85580, baseEnd_85580] using wordTrace_append hprefix tailTrace_85580
  have hstable : (prefixWord ++ tailWord_85580).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85580).length < 2 ^ (prefixWord ++ tailWord_85580).sum := by decide
  have hdescent : baseEnd_85580 < baseStart_85580 := by decide
  rcases family_descends (prefixWord ++ tailWord_85580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85601 : List Nat := [1, 2, 3, 1, 1, 3, 1, 7]
def baseStart_85601 : Nat := 118140960795 + 85601 * 2 ^ 59
def prefixEnd_85601 : Nat := 4983230072969 + 3 ^ 40 * 85601 * 2
def baseEnd_85601 : Nat := 26047085929259152233383

theorem tailTrace_85601 : CollatzResearch.WordTrace tailWord_85601 prefixEnd_85601 26047085929259152233383 := by
  unfold tailWord_85601
  simp only [CollatzResearch.WordTrace]
  refine ⟨3122124962889671331992657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2081416641926447554661771 3122124962889671331992657)
  ·
    refine ⟨2341593722167253498994493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3122124962889671331992657 2341593722167253498994493)
    ·
      refine ⟨878097645812720062122935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2341593722167253498994493 878097645812720062122935)
      ·
        refine ⟨1317146468719080093184403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 878097645812720062122935 1317146468719080093184403)
        ·
          refine ⟨1975719703078620139776605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317146468719080093184403 1975719703078620139776605)
          ·
            refine ⟨740894888654482552416227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1975719703078620139776605 740894888654482552416227)
            ·
              refine ⟨1111342332981723828624341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740894888654482552416227 1111342332981723828624341)
              ·
                refine ⟨26047085929259152233383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1111342332981723828624341 26047085929259152233383)
                ·
                  rfl

theorem cell19_85601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_85601 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85601 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85601 prefixEnd_85601 := by exact prefixLift 85601
  have htrace : WordTrace (prefixWord ++ tailWord_85601) baseStart_85601 baseEnd_85601 := by
    simpa [prefixWord, tailWord_85601, baseEnd_85601] using wordTrace_append hprefix tailTrace_85601
  have hstable : (prefixWord ++ tailWord_85601).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85601).length < 2 ^ (prefixWord ++ tailWord_85601).sum := by decide
  have hdescent : baseEnd_85601 < baseStart_85601 := by decide
  rcases family_descends (prefixWord ++ tailWord_85601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85652 : List Nat := [2, 4, 2, 2, 2, 1, 3, 3]
def baseStart_85652 : Nat := 118140960795 + 85652 * 2 ^ 59
def prefixEnd_85652 : Nat := 4983230072969 + 3 ^ 40 * 85652 * 2
def baseEnd_85652 : Nat := 26062604455706145099911

theorem tailTrace_85652 : CollatzResearch.WordTrace tailWord_85652 prefixEnd_85652 26062604455706145099911 := by
  unfold tailWord_85652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1561992542852453521049605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2082656723803271361399473 1561992542852453521049605)
  ·
    refine ⟨292873601784835035196801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1561992542852453521049605 292873601784835035196801)
    ·
      refine ⟨219655201338626276397601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292873601784835035196801 219655201338626276397601)
      ·
        refine ⟨164741401003969707298201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219655201338626276397601 164741401003969707298201)
        ·
          refine ⟨123556050752977280473651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164741401003969707298201 123556050752977280473651)
          ·
            refine ⟨185334076129465920710477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123556050752977280473651 185334076129465920710477)
            ·
              refine ⟨69500278548549720266429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185334076129465920710477 69500278548549720266429)
              ·
                refine ⟨26062604455706145099911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69500278548549720266429 26062604455706145099911)
                ·
                  rfl

theorem cell19_85652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_85652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85652 prefixEnd_85652 := by exact prefixLift 85652
  have htrace : WordTrace (prefixWord ++ tailWord_85652) baseStart_85652 baseEnd_85652 := by
    simpa [prefixWord, tailWord_85652, baseEnd_85652] using wordTrace_append hprefix tailTrace_85652
  have hstable : (prefixWord ++ tailWord_85652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85652).length < 2 ^ (prefixWord ++ tailWord_85652).sum := by decide
  have hdescent : baseEnd_85652 < baseStart_85652 := by decide
  rcases family_descends (prefixWord ++ tailWord_85652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85696 : List Nat := [2, 1, 1, 2, 4, 1, 2, 6]
def baseStart_85696 : Nat := 118140960795 + 85696 * 2 ^ 59
def prefixEnd_85696 : Nat := 4983230072969 + 3 ^ 40 * 85696 * 2
def baseEnd_85696 : Nat := 26075992988327080122013

theorem tailTrace_85696 : CollatzResearch.WordTrace tailWord_85696 prefixEnd_85696 26075992988327080122013 := by
  unfold tailWord_85696
  simp only [CollatzResearch.WordTrace]
  refine ⟨1562794948772751278350471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2083726598363668371133961 1562794948772751278350471)
  ·
    refine ⟨2344192423159126917525707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1562794948772751278350471 2344192423159126917525707)
    ·
      refine ⟨3516288634738690376288561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2344192423159126917525707 3516288634738690376288561)
      ·
        refine ⟨2637216476054017782216421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3516288634738690376288561 2637216476054017782216421)
        ·
          refine ⟨494478089260128334165579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2637216476054017782216421 494478089260128334165579)
          ·
            refine ⟨741717133890192501248369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494478089260128334165579 741717133890192501248369)
            ·
              refine ⟨556287850417644375936277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 741717133890192501248369 556287850417644375936277)
              ·
                refine ⟨26075992988327080122013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 556287850417644375936277 26075992988327080122013)
                ·
                  rfl

theorem cell19_85696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_85696 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85696 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85696 prefixEnd_85696 := by exact prefixLift 85696
  have htrace : WordTrace (prefixWord ++ tailWord_85696) baseStart_85696 baseEnd_85696 := by
    simpa [prefixWord, tailWord_85696, baseEnd_85696] using wordTrace_append hprefix tailTrace_85696
  have hstable : (prefixWord ++ tailWord_85696).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85696).length < 2 ^ (prefixWord ++ tailWord_85696).sum := by decide
  have hdescent : baseEnd_85696 < baseStart_85696 := by decide
  rcases family_descends (prefixWord ++ tailWord_85696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85709 : List Nat := [1, 6, 2, 1, 1, 1, 4, 3]
def baseStart_85709 : Nat := 118140960795 + 85709 * 2 ^ 59
def prefixEnd_85709 : Nat := 4983230072969 + 3 ^ 40 * 85709 * 2
def baseEnd_85709 : Nat := 26079948691146901833089

theorem tailTrace_85709 : CollatzResearch.WordTrace tailWord_85709 prefixEnd_85709 26079948691146901833089 := by
  unfold tailWord_85709
  simp only [CollatzResearch.WordTrace]
  refine ⟨3126064046498405776924181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2084042697665603851282787 3126064046498405776924181)
  ·
    refine ⟨146534252179612770793321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3126064046498405776924181 146534252179612770793321)
    ·
      refine ⟨109900689134709578094991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146534252179612770793321 109900689134709578094991)
      ·
        refine ⟨164851033702064367142487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109900689134709578094991 164851033702064367142487)
        ·
          refine ⟨247276550553096550713731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164851033702064367142487 247276550553096550713731)
          ·
            refine ⟨370914825829644826070597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247276550553096550713731 370914825829644826070597)
            ·
              refine ⟨69546529843058404888237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 370914825829644826070597 69546529843058404888237)
              ·
                refine ⟨26079948691146901833089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69546529843058404888237 26079948691146901833089)
                ·
                  rfl

theorem cell19_85709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 3].length) (baseStart_85709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85709 prefixEnd_85709 := by exact prefixLift 85709
  have htrace : WordTrace (prefixWord ++ tailWord_85709) baseStart_85709 baseEnd_85709 := by
    simpa [prefixWord, tailWord_85709, baseEnd_85709] using wordTrace_append hprefix tailTrace_85709
  have hstable : (prefixWord ++ tailWord_85709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85709).length < 2 ^ (prefixWord ++ tailWord_85709).sum := by decide
  have hdescent : baseEnd_85709 < baseStart_85709 := by decide
  rcases family_descends (prefixWord ++ tailWord_85709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85713 : List Nat := [1, 2, 2, 1, 2, 4, 4, 3]
def baseStart_85713 : Nat := 118140960795 + 85713 * 2 ^ 59
def prefixEnd_85713 : Nat := 4983230072969 + 3 ^ 40 * 85713 * 2
def baseEnd_85713 : Nat := 26081165830476077744189

theorem tailTrace_85713 : CollatzResearch.WordTrace tailWord_85713 prefixEnd_85713 26081165830476077744189 := by
  unfold tailWord_85713
  simp only [CollatzResearch.WordTrace]
  refine ⟨3126209938483914460069793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2084139958989276306713195 3126209938483914460069793)
  ·
    refine ⟨2344657453862935845052345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3126209938483914460069793 2344657453862935845052345)
    ·
      refine ⟨1758493090397201883789259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2344657453862935845052345 1758493090397201883789259)
      ·
        refine ⟨2637739635595802825683889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1758493090397201883789259 2637739635595802825683889)
        ·
          refine ⟨1978304726696852119262917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2637739635595802825683889 1978304726696852119262917)
          ·
            refine ⟨370932136255659772361797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1978304726696852119262917 370932136255659772361797)
            ·
              refine ⟨69549775547936207317837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 370932136255659772361797 69549775547936207317837)
              ·
                refine ⟨26081165830476077744189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69549775547936207317837 26081165830476077744189)
                ·
                  rfl

theorem cell19_85713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 3].length) (baseStart_85713 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85713 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85713 prefixEnd_85713 := by exact prefixLift 85713
  have htrace : WordTrace (prefixWord ++ tailWord_85713) baseStart_85713 baseEnd_85713 := by
    simpa [prefixWord, tailWord_85713, baseEnd_85713] using wordTrace_append hprefix tailTrace_85713
  have hstable : (prefixWord ++ tailWord_85713).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85713).length < 2 ^ (prefixWord ++ tailWord_85713).sum := by decide
  have hdescent : baseEnd_85713 < baseStart_85713 := by decide
  rcases family_descends (prefixWord ++ tailWord_85713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85772 : List Nat := [2, 2, 1, 2, 2, 1, 4, 5]
def baseStart_85772 : Nat := 118140960795 + 85772 * 2 ^ 59
def prefixEnd_85772 : Nat := 4983230072969 + 3 ^ 40 * 85772 * 2
def baseEnd_85772 : Nat := 26099118635581422432917

theorem tailTrace_85772 : CollatzResearch.WordTrace tailWord_85772 prefixEnd_85772 26099118635581422432917 := by
  unfold tailWord_85772
  simp only [CollatzResearch.WordTrace]
  refine ⟨1564180922635083768233785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2085574563513445024311713 1564180922635083768233785)
  ·
    refine ⟨1173135691976312826175339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1564180922635083768233785 1173135691976312826175339)
    ·
      refine ⟨1759703537964469239263009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1173135691976312826175339 1759703537964469239263009)
      ·
        refine ⟨1319777653473351929447257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1759703537964469239263009 1319777653473351929447257)
        ·
          refine ⟨989833240105013947085443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1319777653473351929447257 989833240105013947085443)
          ·
            refine ⟨1484749860157520920628165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989833240105013947085443 1484749860157520920628165)
            ·
              refine ⟨278390598779535172617781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1484749860157520920628165 278390598779535172617781)
              ·
                refine ⟨26099118635581422432917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 278390598779535172617781 26099118635581422432917)
                ·
                  rfl

theorem cell19_85772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_85772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85772 prefixEnd_85772 := by exact prefixLift 85772
  have htrace : WordTrace (prefixWord ++ tailWord_85772) baseStart_85772 baseEnd_85772 := by
    simpa [prefixWord, tailWord_85772, baseEnd_85772] using wordTrace_append hprefix tailTrace_85772
  have hstable : (prefixWord ++ tailWord_85772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85772).length < 2 ^ (prefixWord ++ tailWord_85772).sum := by decide
  have hdescent : baseEnd_85772 < baseStart_85772 := by decide
  rcases family_descends (prefixWord ++ tailWord_85772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85827 : List Nat := [1, 1, 1, 3, 1, 6, 3, 3]
def baseStart_85827 : Nat := 118140960795 + 85827 * 2 ^ 59
def prefixEnd_85827 : Nat := 4983230072969 + 3 ^ 40 * 85827 * 2
def baseEnd_85827 : Nat := 26115854301357591210545

theorem tailTrace_85827 : CollatzResearch.WordTrace tailWord_85827 prefixEnd_85827 26115854301357591210545 := by
  unfold tailWord_85827
  simp only [CollatzResearch.WordTrace]
  refine ⟨3130367860070911929719735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2086911906713941286479823 3130367860070911929719735)
  ·
    refine ⟨4695551790106367894579603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3130367860070911929719735 4695551790106367894579603)
    ·
      refine ⟨7043327685159551841869405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4695551790106367894579603 7043327685159551841869405)
      ·
        refine ⟨2641247881934831940701027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7043327685159551841869405 2641247881934831940701027)
        ·
          refine ⟨3961871822902247911051541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2641247881934831940701027 3961871822902247911051541)
          ·
            refine ⟨185712741698542870830541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3961871822902247911051541 185712741698542870830541)
            ·
              refine ⟨69642278136953576561453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185712741698542870830541 69642278136953576561453)
              ·
                refine ⟨26115854301357591210545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69642278136953576561453 26115854301357591210545)
                ·
                  rfl

theorem cell19_85827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 3].length) (baseStart_85827 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85827 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85827 prefixEnd_85827 := by exact prefixLift 85827
  have htrace : WordTrace (prefixWord ++ tailWord_85827) baseStart_85827 baseEnd_85827 := by
    simpa [prefixWord, tailWord_85827, baseEnd_85827] using wordTrace_append hprefix tailTrace_85827
  have hstable : (prefixWord ++ tailWord_85827).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85827).length < 2 ^ (prefixWord ++ tailWord_85827).sum := by decide
  have hdescent : baseEnd_85827 < baseStart_85827 := by decide
  rcases family_descends (prefixWord ++ tailWord_85827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85878 : List Nat := [5, 1, 1, 3, 3, 1, 2, 3]
def baseStart_85878 : Nat := 118140960795 + 85878 * 2 ^ 59
def prefixEnd_85878 : Nat := 4983230072969 + 3 ^ 40 * 85878 * 2
def baseEnd_85878 : Nat := 26131372827804584077073

theorem tailTrace_85878 : CollatzResearch.WordTrace tailWord_85878 prefixEnd_85878 26131372827804584077073 := by
  unfold tailWord_85878
  simp only [CollatzResearch.WordTrace]
  refine ⟨195764248930384227489143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2088151988590765093217525 195764248930384227489143)
  ·
    refine ⟨293646373395576341233715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195764248930384227489143 293646373395576341233715)
    ·
      refine ⟨440469560093364511850573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293646373395576341233715 440469560093364511850573)
      ·
        refine ⟨165176085035011691943965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 440469560093364511850573 165176085035011691943965)
        ·
          refine ⟨61941031888129384478987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165176085035011691943965 61941031888129384478987)
          ·
            refine ⟨92911547832194076718481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61941031888129384478987 92911547832194076718481)
            ·
              refine ⟨69683660874145557538861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92911547832194076718481 69683660874145557538861)
              ·
                refine ⟨26131372827804584077073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69683660874145557538861 26131372827804584077073)
                ·
                  rfl

theorem cell19_85878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_85878 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85878 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85878 prefixEnd_85878 := by exact prefixLift 85878
  have htrace : WordTrace (prefixWord ++ tailWord_85878) baseStart_85878 baseEnd_85878 := by
    simpa [prefixWord, tailWord_85878, baseEnd_85878] using wordTrace_append hprefix tailTrace_85878
  have hstable : (prefixWord ++ tailWord_85878).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85878).length < 2 ^ (prefixWord ++ tailWord_85878).sum := by decide
  have hdescent : baseEnd_85878 < baseStart_85878 := by decide
  rcases family_descends (prefixWord ++ tailWord_85878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85918 : List Nat := [4, 3, 1, 3, 1, 1, 2, 4]
def baseStart_85918 : Nat := 118140960795 + 85918 * 2 ^ 59
def prefixEnd_85918 : Nat := 4983230072969 + 3 ^ 40 * 85918 * 2
def baseEnd_85918 : Nat := 26143544221096343188075

theorem tailTrace_85918 : CollatzResearch.WordTrace tailWord_85918 prefixEnd_85918 26143544221096343188075 := by
  unfold tailWord_85918
  simp only [CollatzResearch.WordTrace]
  refine ⟨391710862842654308910301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2089124601827489647521605 391710862842654308910301)
  ·
    refine ⟨146891573565995365841363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 391710862842654308910301 146891573565995365841363)
    ·
      refine ⟨220337360348993048762045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146891573565995365841363 220337360348993048762045)
      ·
        refine ⟨82626510130872393285767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220337360348993048762045 82626510130872393285767)
        ·
          refine ⟨123939765196308589928651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82626510130872393285767 123939765196308589928651)
          ·
            refine ⟨185909647794462884892977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123939765196308589928651 185909647794462884892977)
            ·
              refine ⟨139432235845847163669733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185909647794462884892977 139432235845847163669733)
              ·
                refine ⟨26143544221096343188075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139432235845847163669733 26143544221096343188075)
                ·
                  rfl

theorem cell19_85918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_85918 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85918 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85918 prefixEnd_85918 := by exact prefixLift 85918
  have htrace : WordTrace (prefixWord ++ tailWord_85918) baseStart_85918 baseEnd_85918 := by
    simpa [prefixWord, tailWord_85918, baseEnd_85918] using wordTrace_append hprefix tailTrace_85918
  have hstable : (prefixWord ++ tailWord_85918).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85918).length < 2 ^ (prefixWord ++ tailWord_85918).sum := by decide
  have hdescent : baseEnd_85918 < baseStart_85918 := by decide
  rcases family_descends (prefixWord ++ tailWord_85918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85924 : List Nat := [2, 3, 1, 2, 1, 3, 1, 6]
def baseStart_85924 : Nat := 118140960795 + 85924 * 2 ^ 59
def prefixEnd_85924 : Nat := 4983230072969 + 3 ^ 40 * 85924 * 2
def baseEnd_85924 : Nat := 26145369930090107054725

theorem tailTrace_85924 : CollatzResearch.WordTrace tailWord_85924 prefixEnd_85924 26145369930090107054725 := by
  unfold tailWord_85924
  simp only [CollatzResearch.WordTrace]
  refine ⟨1566952870359748748000413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2089270493812998330667217 1566952870359748748000413)
  ·
    refine ⟨587607326384905780500155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1566952870359748748000413 587607326384905780500155)
    ·
      refine ⟨881410989577358670750233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 587607326384905780500155 881410989577358670750233)
      ·
        refine ⟨661058242183019003062675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 881410989577358670750233 661058242183019003062675)
        ·
          refine ⟨991587363274528504594013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 661058242183019003062675 991587363274528504594013)
          ·
            refine ⟨371845261227948189222755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 991587363274528504594013 371845261227948189222755)
            ·
              refine ⟨557767891841922283834133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371845261227948189222755 557767891841922283834133)
              ·
                refine ⟨26145369930090107054725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 557767891841922283834133 26145369930090107054725)
                ·
                  rfl

theorem cell19_85924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_85924 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85924 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85924 prefixEnd_85924 := by exact prefixLift 85924
  have htrace : WordTrace (prefixWord ++ tailWord_85924) baseStart_85924 baseEnd_85924 := by
    simpa [prefixWord, tailWord_85924, baseEnd_85924] using wordTrace_append hprefix tailTrace_85924
  have hstable : (prefixWord ++ tailWord_85924).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85924).length < 2 ^ (prefixWord ++ tailWord_85924).sum := by decide
  have hdescent : baseEnd_85924 < baseStart_85924 := by decide
  rcases family_descends (prefixWord ++ tailWord_85924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85958 : List Nat := [6, 1, 3, 9]
def baseStart_85958 : Nat := 118140960795 + 85958 * 2 ^ 59
def prefixEnd_85958 : Nat := 4983230072969 + 3 ^ 40 * 85958 * 2
def baseEnd_85958 : Nat := 322910069313433361717

theorem tailTrace_85958 : CollatzResearch.WordTrace tailWord_85958 prefixEnd_85958 322910069313433361717 := by
  unfold tailWord_85958
  simp only [CollatzResearch.WordTrace]
  refine ⟨97973306956135040710579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2090097215064214201825685 97973306956135040710579)
  ·
    refine ⟨146959960434202561065869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97973306956135040710579 146959960434202561065869)
    ·
      refine ⟨55109985162825960399701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146959960434202561065869 55109985162825960399701)
      ·
        refine ⟨322910069313433361717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 55109985162825960399701 322910069313433361717)
        ·
          rfl

theorem cell19_85958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 9].length) (baseStart_85958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85958 prefixEnd_85958 := by exact prefixLift 85958
  have htrace : WordTrace (prefixWord ++ tailWord_85958) baseStart_85958 baseEnd_85958 := by
    simpa [prefixWord, tailWord_85958, baseEnd_85958] using wordTrace_append hprefix tailTrace_85958
  have hstable : (prefixWord ++ tailWord_85958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85958).length < 2 ^ (prefixWord ++ tailWord_85958).sum := by decide
  have hdescent : baseEnd_85958 < baseStart_85958 := by decide
  rcases family_descends (prefixWord ++ tailWord_85958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85977 : List Nat := [1, 2, 1, 2, 7, 1, 1, 4]
def baseStart_85977 : Nat := 118140960795 + 85977 * 2 ^ 59
def prefixEnd_85977 : Nat := 4983230072969 + 3 ^ 40 * 85977 * 2
def baseEnd_85977 : Nat := 26161497026201687876803

theorem tailTrace_85977 : CollatzResearch.WordTrace tailWord_85977 prefixEnd_85977 26161497026201687876803 := by
  unfold tailWord_85977
  simp only [CollatzResearch.WordTrace]
  refine ⟨3135838809527487547680185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2090559206351658365120123 3135838809527487547680185)
  ·
    refine ⟨2351879107145615660760139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3135838809527487547680185 2351879107145615660760139)
    ·
      refine ⟨3527818660718423491140209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2351879107145615660760139 3527818660718423491140209)
      ·
        refine ⟨2645863995538817618355157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3527818660718423491140209 2645863995538817618355157)
        ·
          refine ⟨62012437395441037930199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 2645863995538817618355157 62012437395441037930199)
          ·
            refine ⟨93018656093161556895299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62012437395441037930199 93018656093161556895299)
            ·
              refine ⟨139527984139742335342949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93018656093161556895299 139527984139742335342949)
              ·
                refine ⟨26161497026201687876803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139527984139742335342949 26161497026201687876803)
                ·
                  rfl

theorem cell19_85977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 4].length) (baseStart_85977 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_85977 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_85977 prefixEnd_85977 := by exact prefixLift 85977
  have htrace : WordTrace (prefixWord ++ tailWord_85977) baseStart_85977 baseEnd_85977 := by
    simpa [prefixWord, tailWord_85977, baseEnd_85977] using wordTrace_append hprefix tailTrace_85977
  have hstable : (prefixWord ++ tailWord_85977).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85977).length < 2 ^ (prefixWord ++ tailWord_85977).sum := by decide
  have hdescent : baseEnd_85977 < baseStart_85977 := by decide
  rcases family_descends (prefixWord ++ tailWord_85977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86093 : List Nat := [1, 6, 1, 1, 1, 1, 4, 4]
def baseStart_86093 : Nat := 118140960795 + 86093 * 2 ^ 59
def prefixEnd_86093 : Nat := 4983230072969 + 3 ^ 40 * 86093 * 2
def baseEnd_86093 : Nat := 26196794066747789298709

theorem tailTrace_86093 : CollatzResearch.WordTrace tailWord_86093 prefixEnd_86093 26196794066747789298709 := by
  unfold tailWord_86093
  simp only [CollatzResearch.WordTrace]
  refine ⟨3140069677107239358902933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2093379784738159572601955 3140069677107239358902933)
  ·
    refine ⟨147190766114401844948575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3140069677107239358902933 147190766114401844948575)
    ·
      refine ⟨220786149171602767422863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147190766114401844948575 220786149171602767422863)
      ·
        refine ⟨331179223757404151134295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220786149171602767422863 331179223757404151134295)
        ·
          refine ⟨496768835636106226701443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331179223757404151134295 496768835636106226701443)
          ·
            refine ⟨745153253454159340052165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496768835636106226701443 745153253454159340052165)
            ·
              refine ⟨139716235022654876259781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 745153253454159340052165 139716235022654876259781)
              ·
                refine ⟨26196794066747789298709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139716235022654876259781 26196794066747789298709)
                ·
                  rfl

theorem cell19_86093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_86093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86093 prefixEnd_86093 := by exact prefixLift 86093
  have htrace : WordTrace (prefixWord ++ tailWord_86093) baseStart_86093 baseEnd_86093 := by
    simpa [prefixWord, tailWord_86093, baseEnd_86093] using wordTrace_append hprefix tailTrace_86093
  have hstable : (prefixWord ++ tailWord_86093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86093).length < 2 ^ (prefixWord ++ tailWord_86093).sum := by decide
  have hdescent : baseEnd_86093 < baseStart_86093 := by decide
  rcases family_descends (prefixWord ++ tailWord_86093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86135 : List Nat := [1, 1, 3, 1, 1, 12]
def baseStart_86135 : Nat := 118140960795 + 86135 * 2 ^ 59
def prefixEnd_86135 : Nat := 4983230072969 + 3 ^ 40 * 86135 * 2
def baseEnd_86135 : Nat := 2912174892189348485029

theorem tailTrace_86135 : CollatzResearch.WordTrace tailWord_86135 prefixEnd_86135 2912174892189348485029 := by
  unfold tailWord_86135
  simp only [CollatzResearch.WordTrace]
  refine ⟨3141601542955080531931859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2094401028636720354621239 3141601542955080531931859)
  ·
    refine ⟨4712402314432620797897789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3141601542955080531931859 4712402314432620797897789)
    ·
      refine ⟨1767150867912232799211671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4712402314432620797897789 1767150867912232799211671)
      ·
        refine ⟨2650726301868349198817507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1767150867912232799211671 2650726301868349198817507)
        ·
          refine ⟨3976089452802523798226261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2650726301868349198817507 3976089452802523798226261)
          ·
            refine ⟨2912174892189348485029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3976089452802523798226261 2912174892189348485029)
            ·
              rfl

theorem cell19_86135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 12].length) (baseStart_86135 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86135 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86135 prefixEnd_86135 := by exact prefixLift 86135
  have htrace : WordTrace (prefixWord ++ tailWord_86135) baseStart_86135 baseEnd_86135 := by
    simpa [prefixWord, tailWord_86135, baseEnd_86135] using wordTrace_append hprefix tailTrace_86135
  have hstable : (prefixWord ++ tailWord_86135).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86135).length < 2 ^ (prefixWord ++ tailWord_86135).sum := by decide
  have hdescent : baseEnd_86135 < baseStart_86135 := by decide
  rcases family_descends (prefixWord ++ tailWord_86135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86226 : List Nat := [3, 2, 2, 2, 1, 2, 4, 3]
def baseStart_86226 : Nat := 118140960795 + 86226 * 2 ^ 59
def prefixEnd_86226 : Nat := 4983230072969 + 3 ^ 40 * 86226 * 2
def baseEnd_86226 : Nat := 26237263949442888342791

theorem tailTrace_86226 : CollatzResearch.WordTrace tailWord_86226 prefixEnd_86226 26237263949442888342791 := by
  unfold tailWord_86226
  simp only [CollatzResearch.WordTrace]
  refine ⟨786230146406350768373633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2096613723750268715663021 786230146406350768373633)
  ·
    refine ⟨589672609804763076280225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 786230146406350768373633 589672609804763076280225)
    ·
      refine ⟨442254457353572307210169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 589672609804763076280225 442254457353572307210169)
      ·
        refine ⟨331690843015179230407627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 442254457353572307210169 331690843015179230407627)
        ·
          refine ⟨497536264522768845611441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331690843015179230407627 497536264522768845611441)
          ·
            refine ⟨373152198392076634208581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497536264522768845611441 373152198392076634208581)
            ·
              refine ⟨69966037198514368914109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 373152198392076634208581 69966037198514368914109)
              ·
                refine ⟨26237263949442888342791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69966037198514368914109 26237263949442888342791)
                ·
                  rfl

theorem cell19_86226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_86226 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86226 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86226 prefixEnd_86226 := by exact prefixLift 86226
  have htrace : WordTrace (prefixWord ++ tailWord_86226) baseStart_86226 baseEnd_86226 := by
    simpa [prefixWord, tailWord_86226, baseEnd_86226] using wordTrace_append hprefix tailTrace_86226
  have hstable : (prefixWord ++ tailWord_86226).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86226).length < 2 ^ (prefixWord ++ tailWord_86226).sum := by decide
  have hdescent : baseEnd_86226 < baseStart_86226 := by decide
  rcases family_descends (prefixWord ++ tailWord_86226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86243 : List Nat := [1, 1, 1, 8, 2, 1, 5]
def baseStart_86243 : Nat := 118140960795 + 86243 * 2 ^ 59
def prefixEnd_86243 : Nat := 4983230072969 + 3 ^ 40 * 86243 * 2
def baseEnd_86243 : Nat := 8747478930530628654989

theorem tailTrace_86243 : CollatzResearch.WordTrace tailWord_86243 prefixEnd_86243 8747478930530628654989 := by
  unfold tailWord_86243
  simp only [CollatzResearch.WordTrace]
  refine ⟨3145540626563814976863383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2097027084375876651242255 3145540626563814976863383)
  ·
    refine ⟨4718310939845722465295075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3145540626563814976863383 4718310939845722465295075)
    ·
      refine ⟨7077466409768583697942613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4718310939845722465295075 7077466409768583697942613)
      ·
        refine ⟨82939059489475590210265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 7077466409768583697942613 82939059489475590210265)
        ·
          refine ⟨62204294617106692657699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82939059489475590210265 62204294617106692657699)
          ·
            refine ⟨93306441925660038986549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62204294617106692657699 93306441925660038986549)
            ·
              refine ⟨8747478930530628654989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93306441925660038986549 8747478930530628654989)
              ·
                rfl

theorem cell19_86243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 5].length) (baseStart_86243 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86243 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86243 prefixEnd_86243 := by exact prefixLift 86243
  have htrace : WordTrace (prefixWord ++ tailWord_86243) baseStart_86243 baseEnd_86243 := by
    simpa [prefixWord, tailWord_86243, baseEnd_86243] using wordTrace_append hprefix tailTrace_86243
  have hstable : (prefixWord ++ tailWord_86243).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86243).length < 2 ^ (prefixWord ++ tailWord_86243).sum := by decide
  have hdescent : baseEnd_86243 < baseStart_86243 := by decide
  rcases family_descends (prefixWord ++ tailWord_86243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86247 : List Nat := [1, 1, 5, 3, 1, 1, 7]
def baseStart_86247 : Nat := 118140960795 + 86247 * 2 ^ 59
def prefixEnd_86247 : Nat := 4983230072969 + 3 ^ 40 * 86247 * 2
def baseEnd_86247 : Nat := 8747884643640353958689

theorem tailTrace_86247 : CollatzResearch.WordTrace tailWord_86247 prefixEnd_86247 8747884643640353958689 := by
  unfold tailWord_86247
  simp only [CollatzResearch.WordTrace]
  refine ⟨3145686518549323660008995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2097124345699549106672663 3145686518549323660008995)
  ·
    refine ⟨4718529777823985490013493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3145686518549323660008995 4718529777823985490013493)
    ·
      refine ⟨442362166670998639688765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4718529777823985490013493 442362166670998639688765)
      ·
        refine ⟨165885812501624489883287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 442362166670998639688765 165885812501624489883287)
        ·
          refine ⟨248828718752436734824931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165885812501624489883287 248828718752436734824931)
          ·
            refine ⟨373243078128655102237397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248828718752436734824931 373243078128655102237397)
            ·
              refine ⟨8747884643640353958689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 373243078128655102237397 8747884643640353958689)
              ·
                rfl

theorem cell19_86247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 7].length) (baseStart_86247 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86247 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86247 prefixEnd_86247 := by exact prefixLift 86247
  have htrace : WordTrace (prefixWord ++ tailWord_86247) baseStart_86247 baseEnd_86247 := by
    simpa [prefixWord, tailWord_86247, baseEnd_86247] using wordTrace_append hprefix tailTrace_86247
  have hstable : (prefixWord ++ tailWord_86247).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86247).length < 2 ^ (prefixWord ++ tailWord_86247).sum := by decide
  have hdescent : baseEnd_86247 < baseStart_86247 := by decide
  rcases family_descends (prefixWord ++ tailWord_86247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86266 : List Nat := [3, 1, 1, 1, 1, 6, 2, 4]
def baseStart_86266 : Nat := 118140960795 + 86266 * 2 ^ 59
def prefixEnd_86266 : Nat := 4983230072969 + 3 ^ 40 * 86266 * 2
def baseEnd_86266 : Nat := 26249435342734647453793

theorem tailTrace_86266 : CollatzResearch.WordTrace tailWord_86266 prefixEnd_86266 26249435342734647453793 := by
  unfold tailWord_86266
  simp only [CollatzResearch.WordTrace]
  refine ⟨786594876370122476237663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2097586336986993269967101 786594876370122476237663)
  ·
    refine ⟨1179892314555183714356495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 786594876370122476237663 1179892314555183714356495)
    ·
      refine ⟨1769838471832775571534743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1179892314555183714356495 1769838471832775571534743)
      ·
        refine ⟨2654757707749163357302115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1769838471832775571534743 2654757707749163357302115)
        ·
          refine ⟨3982136561623745035953173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2654757707749163357302115 3982136561623745035953173)
          ·
            refine ⟨186662651326113048560305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3982136561623745035953173 186662651326113048560305)
            ·
              refine ⟨139996988494584786420229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186662651326113048560305 139996988494584786420229)
              ·
                refine ⟨26249435342734647453793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139996988494584786420229 26249435342734647453793)
                ·
                  rfl

theorem cell19_86266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_86266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86266 prefixEnd_86266 := by exact prefixLift 86266
  have htrace : WordTrace (prefixWord ++ tailWord_86266) baseStart_86266 baseEnd_86266 := by
    simpa [prefixWord, tailWord_86266, baseEnd_86266] using wordTrace_append hprefix tailTrace_86266
  have hstable : (prefixWord ++ tailWord_86266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86266).length < 2 ^ (prefixWord ++ tailWord_86266).sum := by decide
  have hdescent : baseEnd_86266 < baseStart_86266 := by decide
  rcases family_descends (prefixWord ++ tailWord_86266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86302 : List Nat := [4, 3, 2, 1, 1, 8]
def baseStart_86302 : Nat := 118140960795 + 86302 * 2 ^ 59
def prefixEnd_86302 : Nat := 4983230072969 + 3 ^ 40 * 86302 * 2
def baseEnd_86302 : Nat := 2917821066299692294855

theorem tailTrace_86302 : CollatzResearch.WordTrace tailWord_86302 prefixEnd_86302 2917821066299692294855 := by
  unfold tailWord_86302
  simp only [CollatzResearch.WordTrace]
  refine ⟨393461566668758506657645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2098461688900045368840773 393461566668758506657645)
  ·
    refine ⟨147548087500784439996617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 393461566668758506657645 147548087500784439996617)
    ·
      refine ⟨110661065625588329997463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147548087500784439996617 110661065625588329997463)
      ·
        refine ⟨165991598438382494996195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110661065625588329997463 165991598438382494996195)
        ·
          refine ⟨248987397657573742494293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165991598438382494996195 248987397657573742494293)
          ·
            refine ⟨2917821066299692294855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 248987397657573742494293 2917821066299692294855)
            ·
              rfl

theorem cell19_86302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 8].length) (baseStart_86302 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86302 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86302 prefixEnd_86302 := by exact prefixLift 86302
  have htrace : WordTrace (prefixWord ++ tailWord_86302) baseStart_86302 baseEnd_86302 := by
    simpa [prefixWord, tailWord_86302, baseEnd_86302] using wordTrace_append hprefix tailTrace_86302
  have hstable : (prefixWord ++ tailWord_86302).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86302).length < 2 ^ (prefixWord ++ tailWord_86302).sum := by decide
  have hdescent : baseEnd_86302 < baseStart_86302 := by decide
  rcases family_descends (prefixWord ++ tailWord_86302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86317 : List Nat := [1, 5, 3, 1, 3, 1, 1, 4]
def baseStart_86317 : Nat := 118140960795 + 86317 * 2 ^ 59
def prefixEnd_86317 : Nat := 4983230072969 + 3 ^ 40 * 86317 * 2
def baseEnd_86317 : Nat := 26264953869181640320321

theorem tailTrace_86317 : CollatzResearch.WordTrace tailWord_86317 prefixEnd_86317 26264953869181640320321 := by
  unfold tailWord_86317
  simp only [CollatzResearch.WordTrace]
  refine ⟨3148239628295725615057205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2098826418863817076704803 3148239628295725615057205)
  ·
    refine ⟨295147465152724276411613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3148239628295725615057205 295147465152724276411613)
    ·
      refine ⟨110680299432271603654355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295147465152724276411613 110680299432271603654355)
      ·
        refine ⟨166020449148407405481533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110680299432271603654355 166020449148407405481533)
        ·
          refine ⟨62257668430652777055575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166020449148407405481533 62257668430652777055575)
          ·
            refine ⟨93386502645979165583363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62257668430652777055575 93386502645979165583363)
            ·
              refine ⟨140079753968968748375045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93386502645979165583363 140079753968968748375045)
              ·
                refine ⟨26264953869181640320321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140079753968968748375045 26264953869181640320321)
                ·
                  rfl

theorem cell19_86317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 4].length) (baseStart_86317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86317 prefixEnd_86317 := by exact prefixLift 86317
  have htrace : WordTrace (prefixWord ++ tailWord_86317) baseStart_86317 baseEnd_86317 := by
    simpa [prefixWord, tailWord_86317, baseEnd_86317] using wordTrace_append hprefix tailTrace_86317
  have hstable : (prefixWord ++ tailWord_86317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86317).length < 2 ^ (prefixWord ++ tailWord_86317).sum := by decide
  have hdescent : baseEnd_86317 < baseStart_86317 := by decide
  rcases family_descends (prefixWord ++ tailWord_86317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86321 : List Nat := [1, 2, 2, 3, 4, 2, 1, 4]
def baseStart_86321 : Nat := 118140960795 + 86321 * 2 ^ 59
def prefixEnd_86321 : Nat := 4983230072969 + 3 ^ 40 * 86321 * 2
def baseEnd_86321 : Nat := 26266171008510816231421

theorem tailTrace_86321 : CollatzResearch.WordTrace tailWord_86321 prefixEnd_86321 26266171008510816231421 := by
  unfold tailWord_86321
  simp only [CollatzResearch.WordTrace]
  refine ⟨3148385520281234298202817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2098923680187489532135211 3148385520281234298202817)
  ·
    refine ⟨2361289140210925723652113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3148385520281234298202817 2361289140210925723652113)
    ·
      refine ⟨1770966855158194292739085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2361289140210925723652113 1770966855158194292739085)
      ·
        refine ⟨664112570684322859777157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1770966855158194292739085 664112570684322859777157)
        ·
          refine ⟨124521107003310536208217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 664112570684322859777157 124521107003310536208217)
          ·
            refine ⟨93390830252482902156163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124521107003310536208217 93390830252482902156163)
            ·
              refine ⟨140086245378724353234245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93390830252482902156163 140086245378724353234245)
              ·
                refine ⟨26266171008510816231421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140086245378724353234245 26266171008510816231421)
                ·
                  rfl

theorem cell19_86321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 4].length) (baseStart_86321 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86321 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86321 prefixEnd_86321 := by exact prefixLift 86321
  have htrace : WordTrace (prefixWord ++ tailWord_86321) baseStart_86321 baseEnd_86321 := by
    simpa [prefixWord, tailWord_86321, baseEnd_86321] using wordTrace_append hprefix tailTrace_86321
  have hstable : (prefixWord ++ tailWord_86321).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86321).length < 2 ^ (prefixWord ++ tailWord_86321).sum := by decide
  have hdescent : baseEnd_86321 < baseStart_86321 := by decide
  rcases family_descends (prefixWord ++ tailWord_86321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86344 : List Nat := [2, 1, 3, 1, 1, 2, 2, 7]
def baseStart_86344 : Nat := 118140960795 + 86344 * 2 ^ 59
def prefixEnd_86344 : Nat := 4983230072969 + 3 ^ 40 * 86344 * 2
def baseEnd_86344 : Nat := 26273169559653577720247

theorem tailTrace_86344 : CollatzResearch.WordTrace tailWord_86344 prefixEnd_86344 26273169559653577720247 := by
  unfold tailWord_86344
  simp only [CollatzResearch.WordTrace]
  refine ⟨1574612199598954613145043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2099482932798606150860057 1574612199598954613145043)
  ·
    refine ⟨2361918299398431919717565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1574612199598954613145043 2361918299398431919717565)
    ·
      refine ⟨885719362274411969894087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2361918299398431919717565 885719362274411969894087)
      ·
        refine ⟨1328579043411617954841131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 885719362274411969894087 1328579043411617954841131)
        ·
          refine ⟨1992868565117426932261697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328579043411617954841131 1992868565117426932261697)
          ·
            refine ⟨1494651423838070199196273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1992868565117426932261697 1494651423838070199196273)
            ·
              refine ⟨1120988567878552649397205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1494651423838070199196273 1120988567878552649397205)
              ·
                refine ⟨26273169559653577720247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1120988567878552649397205 26273169559653577720247)
                ·
                  rfl

theorem cell19_86344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_86344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86344 prefixEnd_86344 := by exact prefixLift 86344
  have htrace : WordTrace (prefixWord ++ tailWord_86344) baseStart_86344 baseEnd_86344 := by
    simpa [prefixWord, tailWord_86344, baseEnd_86344] using wordTrace_append hprefix tailTrace_86344
  have hstable : (prefixWord ++ tailWord_86344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86344).length < 2 ^ (prefixWord ++ tailWord_86344).sum := by decide
  have hdescent : baseEnd_86344 < baseStart_86344 := by decide
  rcases family_descends (prefixWord ++ tailWord_86344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86397 : List Nat := [1, 4, 1, 1, 2, 5, 2, 3]
def baseStart_86397 : Nat := 118140960795 + 86397 * 2 ^ 59
def prefixEnd_86397 : Nat := 4983230072969 + 3 ^ 40 * 86397 * 2
def baseEnd_86397 : Nat := 26289296655765158542325

theorem tailTrace_86397 : CollatzResearch.WordTrace tailWord_86397 prefixEnd_86397 26289296655765158542325 := by
  unfold tailWord_86397
  simp only [CollatzResearch.WordTrace]
  refine ⟨3151157468005899277969445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2100771645337266185312963 3151157468005899277969445)
  ·
    refine ⟨590842025251106114619271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3151157468005899277969445 590842025251106114619271)
    ·
      refine ⟨886263037876659171928907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 590842025251106114619271 886263037876659171928907)
      ·
        refine ⟨1329394556814988757893361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886263037876659171928907 1329394556814988757893361)
        ·
          refine ⟨997045917611241568420021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1329394556814988757893361 997045917611241568420021)
          ·
            refine ⟨93473054776053897039377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 997045917611241568420021 93473054776053897039377)
            ·
              refine ⟨70104791082040422779533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93473054776053897039377 70104791082040422779533)
              ·
                refine ⟨26289296655765158542325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70104791082040422779533 26289296655765158542325)
                ·
                  rfl

theorem cell19_86397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 3].length) (baseStart_86397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86397 prefixEnd_86397 := by exact prefixLift 86397
  have htrace : WordTrace (prefixWord ++ tailWord_86397) baseStart_86397 baseEnd_86397 := by
    simpa [prefixWord, tailWord_86397, baseEnd_86397] using wordTrace_append hprefix tailTrace_86397
  have hstable : (prefixWord ++ tailWord_86397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86397).length < 2 ^ (prefixWord ++ tailWord_86397).sum := by decide
  have hdescent : baseEnd_86397 < baseStart_86397 := by decide
  rcases family_descends (prefixWord ++ tailWord_86397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86477 : List Nat := [1, 6, 12]
def baseStart_86477 : Nat := 118140960795 + 86477 * 2 ^ 59
def prefixEnd_86477 : Nat := 4983230072969 + 3 ^ 40 * 86477 * 2
def baseEnd_86477 : Nat := 108286582067278505203

theorem tailTrace_86477 : CollatzResearch.WordTrace tailWord_86477 prefixEnd_86477 108286582067278505203 := by
  unfold tailWord_86477
  simp only [CollatzResearch.WordTrace]
  refine ⟨3154075307716072940881685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2102716871810715293921123 3154075307716072940881685)
  ·
    refine ⟨147847280049190919103829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3154075307716072940881685 147847280049190919103829)
    ·
      refine ⟨108286582067278505203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 12 147847280049190919103829 108286582067278505203)
      ·
        rfl

theorem cell19_86477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 12].length) (baseStart_86477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86477 prefixEnd_86477 := by exact prefixLift 86477
  have htrace : WordTrace (prefixWord ++ tailWord_86477) baseStart_86477 baseEnd_86477 := by
    simpa [prefixWord, tailWord_86477, baseEnd_86477] using wordTrace_append hprefix tailTrace_86477
  have hstable : (prefixWord ++ tailWord_86477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86477).length < 2 ^ (prefixWord ++ tailWord_86477).sum := by decide
  have hdescent : baseEnd_86477 < baseStart_86477 := by decide
  rcases family_descends (prefixWord ++ tailWord_86477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86513 : List Nat := [1, 2, 2, 2, 3, 1, 5, 3]
def baseStart_86513 : Nat := 118140960795 + 86513 * 2 ^ 59
def prefixEnd_86513 : Nat := 4983230072969 + 3 ^ 40 * 86513 * 2
def baseEnd_86513 : Nat := 26324593696311259964231

theorem tailTrace_86513 : CollatzResearch.WordTrace tailWord_86513 prefixEnd_86513 26324593696311259964231 := by
  unfold tailWord_86513
  simp only [CollatzResearch.WordTrace]
  refine ⟨3155388335585651089192193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2103592223723767392794795 3155388335585651089192193)
  ·
    refine ⟨2366541251689238316894145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3155388335585651089192193 2366541251689238316894145)
    ·
      refine ⟨1774905938766928737670609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2366541251689238316894145 1774905938766928737670609)
      ·
        refine ⟨1331179454075196553252957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1774905938766928737670609 1331179454075196553252957)
        ·
          refine ⟨499192295278198707469859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1331179454075196553252957 499192295278198707469859)
          ·
            refine ⟨748788442917298061204789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499192295278198707469859 748788442917298061204789)
            ·
              refine ⟨70198916523496693237949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 748788442917298061204789 70198916523496693237949)
              ·
                refine ⟨26324593696311259964231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70198916523496693237949 26324593696311259964231)
                ·
                  rfl

theorem cell19_86513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 3].length) (baseStart_86513 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86513 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86513 prefixEnd_86513 := by exact prefixLift 86513
  have htrace : WordTrace (prefixWord ++ tailWord_86513) baseStart_86513 baseEnd_86513 := by
    simpa [prefixWord, tailWord_86513, baseEnd_86513] using wordTrace_append hprefix tailTrace_86513
  have hstable : (prefixWord ++ tailWord_86513).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86513).length < 2 ^ (prefixWord ++ tailWord_86513).sum := by decide
  have hdescent : baseEnd_86513 < baseStart_86513 := by decide
  rcases family_descends (prefixWord ++ tailWord_86513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86530 : List Nat := [3, 4, 1, 2, 2, 1, 6]
def baseStart_86530 : Nat := 118140960795 + 86530 * 2 ^ 59
def prefixEnd_86530 : Nat := 4983230072969 + 3 ^ 40 * 86530 * 2
def baseEnd_86530 : Nat := 8776588846153419195469

theorem tailTrace_86530 : CollatzResearch.WordTrace tailWord_86530 prefixEnd_86530 8776588846153419195469 := by
  unfold tailWord_86530
  simp only [CollatzResearch.WordTrace]
  refine ⟨789002094131015748140261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2104005584349375328374029 789002094131015748140261)
  ·
    refine ⟨147937892649565452776299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 789002094131015748140261 147937892649565452776299)
    ·
      refine ⟨221906838974348179164449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147937892649565452776299 221906838974348179164449)
      ·
        refine ⟨166430129230761134373337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221906838974348179164449 166430129230761134373337)
        ·
          refine ⟨124822596923070850780003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166430129230761134373337 124822596923070850780003)
          ·
            refine ⟨187233895384606276170005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124822596923070850780003 187233895384606276170005)
            ·
              refine ⟨8776588846153419195469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 187233895384606276170005 8776588846153419195469)
              ·
                rfl

theorem cell19_86530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 6].length) (baseStart_86530 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86530 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86530 prefixEnd_86530 := by exact prefixLift 86530
  have htrace : WordTrace (prefixWord ++ tailWord_86530) baseStart_86530 baseEnd_86530 := by
    simpa [prefixWord, tailWord_86530, baseEnd_86530] using wordTrace_append hprefix tailTrace_86530
  have hstable : (prefixWord ++ tailWord_86530).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86530).length < 2 ^ (prefixWord ++ tailWord_86530).sum := by decide
  have hdescent : baseEnd_86530 < baseStart_86530 := by decide
  rcases family_descends (prefixWord ++ tailWord_86530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86532 : List Nat := [2, 3, 2, 3, 1, 2, 6]
def baseStart_86532 : Nat := 118140960795 + 86532 * 2 ^ 59
def prefixEnd_86532 : Nat := 4983230072969 + 3 ^ 40 * 86532 * 2
def baseEnd_86532 : Nat := 8776791702708281847319

theorem tailTrace_86532 : CollatzResearch.WordTrace tailWord_86532 prefixEnd_86532 8776791702708281847319 := by
  unfold tailWord_86532
  simp only [CollatzResearch.WordTrace]
  refine ⟨1578040661258408667066925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2104054215011211556089233 1578040661258408667066925)
  ·
    refine ⟨591765247971903250150097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1578040661258408667066925 591765247971903250150097)
    ·
      refine ⟨443823935978927437612573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 591765247971903250150097 443823935978927437612573)
      ·
        refine ⟨166433975992097789104715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 443823935978927437612573 166433975992097789104715)
        ·
          refine ⟨249650963988146683657073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166433975992097789104715 249650963988146683657073)
          ·
            refine ⟨187238222991110012742805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249650963988146683657073 187238222991110012742805)
            ·
              refine ⟨8776791702708281847319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 187238222991110012742805 8776791702708281847319)
              ·
                rfl

theorem cell19_86532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 6].length) (baseStart_86532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86532 prefixEnd_86532 := by exact prefixLift 86532
  have htrace : WordTrace (prefixWord ++ tailWord_86532) baseStart_86532 baseEnd_86532 := by
    simpa [prefixWord, tailWord_86532, baseEnd_86532] using wordTrace_append hprefix tailTrace_86532
  have hstable : (prefixWord ++ tailWord_86532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86532).length < 2 ^ (prefixWord ++ tailWord_86532).sum := by decide
  have hdescent : baseEnd_86532 < baseStart_86532 := by decide
  rcases family_descends (prefixWord ++ tailWord_86532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86564 : List Nat := [2, 3, 1, 5, 2, 1, 2, 3]
def baseStart_86564 : Nat := 118140960795 + 86564 * 2 ^ 59
def prefixEnd_86564 : Nat := 4983230072969 + 3 ^ 40 * 86564 * 2
def baseEnd_86564 : Nat := 26340112222758252830759

theorem tailTrace_86564 : CollatzResearch.WordTrace tailWord_86564 prefixEnd_86564 26340112222758252830759 := by
  unfold tailWord_86564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1578624229200443399649373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2104832305600591199532497 1578624229200443399649373)
  ·
    refine ⟨591984085950166274868515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1578624229200443399649373 591984085950166274868515)
    ·
      refine ⟨887976128925249412302773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 591984085950166274868515 887976128925249412302773)
      ·
        refine ⟨83247762086742132403385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 887976128925249412302773 83247762086742132403385)
        ·
          refine ⟨62435821565056599302539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83247762086742132403385 62435821565056599302539)
          ·
            refine ⟨93653732347584898953809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62435821565056599302539 93653732347584898953809)
            ·
              refine ⟨70240299260688674215357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93653732347584898953809 70240299260688674215357)
              ·
                refine ⟨26340112222758252830759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70240299260688674215357 26340112222758252830759)
                ·
                  rfl

theorem cell19_86564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_86564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86564 prefixEnd_86564 := by exact prefixLift 86564
  have htrace : WordTrace (prefixWord ++ tailWord_86564) baseStart_86564 baseEnd_86564 := by
    simpa [prefixWord, tailWord_86564, baseEnd_86564] using wordTrace_append hprefix tailTrace_86564
  have hstable : (prefixWord ++ tailWord_86564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86564).length < 2 ^ (prefixWord ++ tailWord_86564).sum := by decide
  have hdescent : baseEnd_86564 < baseStart_86564 := by decide
  rcases family_descends (prefixWord ++ tailWord_86564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86568 : List Nat := [2, 1, 5, 2, 1, 1, 4, 3]
def baseStart_86568 : Nat := 118140960795 + 86568 * 2 ^ 59
def prefixEnd_86568 : Nat := 4983230072969 + 3 ^ 40 * 86568 * 2
def baseEnd_86568 : Nat := 26341329362087428741859

theorem tailTrace_86568 : CollatzResearch.WordTrace tailWord_86568 prefixEnd_86568 26341329362087428741859 := by
  unfold tailWord_86568
  simp only [CollatzResearch.WordTrace]
  refine ⟨1578697175193197741222179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2104929566924263654962905 1578697175193197741222179)
  ·
    refine ⟨2368045762789796611833269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1578697175193197741222179 2368045762789796611833269)
    ·
      refine ⟨222004290261543432359369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2368045762789796611833269 222004290261543432359369)
      ·
        refine ⟨166503217696157574269527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222004290261543432359369 166503217696157574269527)
        ·
          refine ⟨249754826544236361404291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166503217696157574269527 249754826544236361404291)
          ·
            refine ⟨374632239816354542106437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249754826544236361404291 374632239816354542106437)
            ·
              refine ⟨70243544965566476644957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 374632239816354542106437 70243544965566476644957)
              ·
                refine ⟨26341329362087428741859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70243544965566476644957 26341329362087428741859)
                ·
                  rfl

theorem cell19_86568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_86568 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86568 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86568 prefixEnd_86568 := by exact prefixLift 86568
  have htrace : WordTrace (prefixWord ++ tailWord_86568) baseStart_86568 baseEnd_86568 := by
    simpa [prefixWord, tailWord_86568, baseEnd_86568] using wordTrace_append hprefix tailTrace_86568
  have hstable : (prefixWord ++ tailWord_86568).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86568).length < 2 ^ (prefixWord ++ tailWord_86568).sum := by decide
  have hdescent : baseEnd_86568 < baseStart_86568 := by decide
  rcases family_descends (prefixWord ++ tailWord_86568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86570 : List Nat := [3, 1, 4, 1, 1, 3, 1, 5]
def baseStart_86570 : Nat := 118140960795 + 86570 * 2 ^ 59
def prefixEnd_86570 : Nat := 4983230072969 + 3 ^ 40 * 86570 * 2
def baseEnd_86570 : Nat := 26341937931752016697409

theorem tailTrace_86570 : CollatzResearch.WordTrace tailWord_86570 prefixEnd_86570 26341937931752016697409 := by
  unfold tailWord_86570
  simp only [CollatzResearch.WordTrace]
  refine ⟨789366824094787456004291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2104978197586099882678109 789366824094787456004291)
  ·
    refine ⟨1184050236142181184006437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 789366824094787456004291 1184050236142181184006437)
    ·
      refine ⟨222009419276658972001207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1184050236142181184006437 222009419276658972001207)
      ·
        refine ⟨333014128914988458001811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222009419276658972001207 333014128914988458001811)
        ·
          refine ⟨499521193372482687002717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333014128914988458001811 499521193372482687002717)
          ·
            refine ⟨187320447514681007626019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 499521193372482687002717 187320447514681007626019)
            ·
              refine ⟨280980671272021511439029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187320447514681007626019 280980671272021511439029)
              ·
                refine ⟨26341937931752016697409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 280980671272021511439029 26341937931752016697409)
                ·
                  rfl

theorem cell19_86570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_86570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86570 prefixEnd_86570 := by exact prefixLift 86570
  have htrace : WordTrace (prefixWord ++ tailWord_86570) baseStart_86570 baseEnd_86570 := by
    simpa [prefixWord, tailWord_86570, baseEnd_86570] using wordTrace_append hprefix tailTrace_86570
  have hstable : (prefixWord ++ tailWord_86570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86570).length < 2 ^ (prefixWord ++ tailWord_86570).sum := by decide
  have hdescent : baseEnd_86570 < baseStart_86570 := by decide
  rcases family_descends (prefixWord ++ tailWord_86570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86589 : List Nat := [1, 4, 1, 3, 2, 3, 5]
def baseStart_86589 : Nat := 118140960795 + 86589 * 2 ^ 59
def prefixEnd_86589 : Nat := 4983230072969 + 3 ^ 40 * 86589 * 2
def baseEnd_86589 : Nat := 8782573114521867425045

theorem tailTrace_86589 : CollatzResearch.WordTrace tailWord_86589 prefixEnd_86589 8782573114521867425045 := by
  unfold tailWord_86589
  simp only [CollatzResearch.WordTrace]
  refine ⟨3158160283310316068958821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2105440188873544045972547 3158160283310316068958821)
  ·
    refine ⟨592155053120684262929779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3158160283310316068958821 592155053120684262929779)
    ·
      refine ⟨888232579681026394394669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 592155053120684262929779 888232579681026394394669)
      ·
        refine ⟨333087217380384897898001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 888232579681026394394669 333087217380384897898001)
        ·
          refine ⟨249815413035288673423501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333087217380384897898001 249815413035288673423501)
          ·
            refine ⟨93680779888233252533813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249815413035288673423501 93680779888233252533813)
            ·
              refine ⟨8782573114521867425045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93680779888233252533813 8782573114521867425045)
              ·
                rfl

theorem cell19_86589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 5].length) (baseStart_86589 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86589 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86589 prefixEnd_86589 := by exact prefixLift 86589
  have htrace : WordTrace (prefixWord ++ tailWord_86589) baseStart_86589 baseEnd_86589 := by
    simpa [prefixWord, tailWord_86589, baseEnd_86589] using wordTrace_append hprefix tailTrace_86589
  have hstable : (prefixWord ++ tailWord_86589).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86589).length < 2 ^ (prefixWord ++ tailWord_86589).sum := by decide
  have hdescent : baseEnd_86589 < baseStart_86589 := by decide
  rcases family_descends (prefixWord ++ tailWord_86589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86646 : List Nat := [5, 1, 1, 2, 3, 7]
def baseStart_86646 : Nat := 118140960795 + 86646 * 2 ^ 59
def prefixEnd_86646 : Nat := 4983230072969 + 3 ^ 40 * 86646 * 2
def baseEnd_86646 : Nat := 2929451508778484334257

theorem tailTrace_86646 : CollatzResearch.WordTrace tailWord_86646 prefixEnd_86646 2929451508778484334257 := by
  unfold tailWord_86646
  simp only [CollatzResearch.WordTrace]
  refine ⟨197514952756488425236487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2106826162735876535855861 197514952756488425236487)
  ·
    refine ⟨296272429134732637854731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197514952756488425236487 296272429134732637854731)
    ·
      refine ⟨444408643702098956782097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296272429134732637854731 444408643702098956782097)
      ·
        refine ⟨333306482776574217586573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444408643702098956782097 333306482776574217586573)
        ·
          refine ⟨124989931041215331594965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 333306482776574217586573 124989931041215331594965)
          ·
            refine ⟨2929451508778484334257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 124989931041215331594965 2929451508778484334257)
            ·
              rfl

theorem cell19_86646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 7].length) (baseStart_86646 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86646 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86646 prefixEnd_86646 := by exact prefixLift 86646
  have htrace : WordTrace (prefixWord ++ tailWord_86646) baseStart_86646 baseEnd_86646 := by
    simpa [prefixWord, tailWord_86646, baseEnd_86646] using wordTrace_append hprefix tailTrace_86646
  have hstable : (prefixWord ++ tailWord_86646).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86646).length < 2 ^ (prefixWord ++ tailWord_86646).sum := by decide
  have hdescent : baseEnd_86646 < baseStart_86646 := by decide
  rcases family_descends (prefixWord ++ tailWord_86646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86743 : List Nat := [1, 1, 3, 2, 1, 5, 1, 5]
def baseStart_86743 : Nat := 118140960795 + 86743 * 2 ^ 59
def prefixEnd_86743 : Nat := 4983230072969 + 3 ^ 40 * 86743 * 2
def baseEnd_86743 : Nat := 26394579207738874852493

theorem tailTrace_86743 : CollatzResearch.WordTrace tailWord_86743 prefixEnd_86743 26394579207738874852493 := by
  unfold tailWord_86743
  simp only [CollatzResearch.WordTrace]
  refine ⟨3163777124752400370064883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2109184749834933580043255 3163777124752400370064883)
  ·
    refine ⟨4745665687128600555097325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3163777124752400370064883 4745665687128600555097325)
    ·
      refine ⟨1779624632673225208161497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4745665687128600555097325 1779624632673225208161497)
      ·
        refine ⟨1334718474504918906121123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1779624632673225208161497 1334718474504918906121123)
        ·
          refine ⟨2002077711757378359181685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1334718474504918906121123 2002077711757378359181685)
          ·
            refine ⟨187694785477254221173283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2002077711757378359181685 187694785477254221173283)
            ·
              refine ⟨281542178215881331759925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187694785477254221173283 281542178215881331759925)
              ·
                refine ⟨26394579207738874852493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 281542178215881331759925 26394579207738874852493)
                ·
                  rfl

theorem cell19_86743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_86743 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86743 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86743 prefixEnd_86743 := by exact prefixLift 86743
  have htrace : WordTrace (prefixWord ++ tailWord_86743) baseStart_86743 baseEnd_86743 := by
    simpa [prefixWord, tailWord_86743, baseEnd_86743] using wordTrace_append hprefix tailTrace_86743
  have hstable : (prefixWord ++ tailWord_86743).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86743).length < 2 ^ (prefixWord ++ tailWord_86743).sum := by decide
  have hdescent : baseEnd_86743 < baseStart_86743 := by decide
  rcases family_descends (prefixWord ++ tailWord_86743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86760 : List Nat := [2, 1, 4, 1, 4, 2, 5]
def baseStart_86760 : Nat := 118140960795 + 86760 * 2 ^ 59
def prefixEnd_86760 : Nat := 4983230072969 + 3 ^ 40 * 86760 * 2
def baseEnd_86760 : Nat := 8799917349962624158223

theorem tailTrace_86760 : CollatzResearch.WordTrace tailWord_86760 prefixEnd_86760 8799917349962624158223 := by
  unfold tailWord_86760
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582198582845406136716867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2109598110460541515622489 1582198582845406136716867)
  ·
    refine ⟨2373297874268109205075301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1582198582845406136716867 2373297874268109205075301)
    ·
      refine ⟨444993351425270475951619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2373297874268109205075301 444993351425270475951619)
      ·
        refine ⟨667490027137905713927429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444993351425270475951619 667490027137905713927429)
        ·
          refine ⟨125154380088357321361393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 667490027137905713927429 125154380088357321361393)
          ·
            refine ⟨93865785066267991021045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125154380088357321361393 93865785066267991021045)
            ·
              refine ⟨8799917349962624158223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93865785066267991021045 8799917349962624158223)
              ·
                rfl

theorem cell19_86760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 5].length) (baseStart_86760 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86760 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86760 prefixEnd_86760 := by exact prefixLift 86760
  have htrace : WordTrace (prefixWord ++ tailWord_86760) baseStart_86760 baseEnd_86760 := by
    simpa [prefixWord, tailWord_86760, baseEnd_86760] using wordTrace_append hprefix tailTrace_86760
  have hstable : (prefixWord ++ tailWord_86760).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86760).length < 2 ^ (prefixWord ++ tailWord_86760).sum := by decide
  have hdescent : baseEnd_86760 < baseStart_86760 := by decide
  rcases family_descends (prefixWord ++ tailWord_86760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86781 : List Nat := [1, 4, 1, 1, 1, 1, 6, 4]
def baseStart_86781 : Nat := 118140960795 + 86781 * 2 ^ 59
def prefixEnd_86781 : Nat := 4983230072969 + 3 ^ 40 * 86781 * 2
def baseEnd_86781 : Nat := 26406142031366046007945

theorem tailTrace_86781 : CollatzResearch.WordTrace tailWord_86781 prefixEnd_86781 26406142031366046007945 := by
  unfold tailWord_86781
  simp only [CollatzResearch.WordTrace]
  refine ⟨3165163098614732859948197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2110108732409821906632131 3165163098614732859948197)
  ·
    refine ⟨593468080990262411240287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3165163098614732859948197 593468080990262411240287)
    ·
      refine ⟨890202121485393616860431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 593468080990262411240287 890202121485393616860431)
      ·
        refine ⟨1335303182228090425290647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 890202121485393616860431 1335303182228090425290647)
        ·
          refine ⟨2002954773342135637935971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1335303182228090425290647 2002954773342135637935971)
          ·
            refine ⟨3004432160013203456903957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2002954773342135637935971 3004432160013203456903957)
            ·
              refine ⟨140832757500618912042373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3004432160013203456903957 140832757500618912042373)
              ·
                refine ⟨26406142031366046007945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140832757500618912042373 26406142031366046007945)
                ·
                  rfl

theorem cell19_86781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_86781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86781 prefixEnd_86781 := by exact prefixLift 86781
  have htrace : WordTrace (prefixWord ++ tailWord_86781) baseStart_86781 baseEnd_86781 := by
    simpa [prefixWord, tailWord_86781, baseEnd_86781] using wordTrace_append hprefix tailTrace_86781
  have hstable : (prefixWord ++ tailWord_86781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86781).length < 2 ^ (prefixWord ++ tailWord_86781).sum := by decide
  have hdescent : baseEnd_86781 < baseStart_86781 := by decide
  rcases family_descends (prefixWord ++ tailWord_86781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86910 : List Nat := [4, 2, 3, 1, 2, 1, 1, 5]
def baseStart_86910 : Nat := 118140960795 + 86910 * 2 ^ 59
def prefixEnd_86910 : Nat := 4983230072969 + 3 ^ 40 * 86910 * 2
def baseEnd_86910 : Nat := 26445394774731969140927

theorem tailTrace_86910 : CollatzResearch.WordTrace tailWord_86910 prefixEnd_86910 26445394774731969140927 := by
  unfold tailWord_86910
  simp only [CollatzResearch.WordTrace]
  refine ⟨396233514393423486424273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2113245410098258594262789 396233514393423486424273)
  ·
    refine ⟨297175135795067614818205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 396233514393423486424273 297175135795067614818205)
    ·
      refine ⟨111440675923150355556827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297175135795067614818205 111440675923150355556827)
      ·
        refine ⟨167161013884725533335241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111440675923150355556827 167161013884725533335241)
        ·
          refine ⟨125370760413544150001431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167161013884725533335241 125370760413544150001431)
          ·
            refine ⟨188056140620316225002147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125370760413544150001431 188056140620316225002147)
            ·
              refine ⟨282084210930474337503221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188056140620316225002147 282084210930474337503221)
              ·
                refine ⟨26445394774731969140927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 282084210930474337503221 26445394774731969140927)
                ·
                  rfl

theorem cell19_86910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_86910 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86910 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86910 prefixEnd_86910 := by exact prefixLift 86910
  have htrace : WordTrace (prefixWord ++ tailWord_86910) baseStart_86910 baseEnd_86910 := by
    simpa [prefixWord, tailWord_86910, baseEnd_86910] using wordTrace_append hprefix tailTrace_86910
  have hstable : (prefixWord ++ tailWord_86910).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86910).length < 2 ^ (prefixWord ++ tailWord_86910).sum := by decide
  have hdescent : baseEnd_86910 < baseStart_86910 := by decide
  rcases family_descends (prefixWord ++ tailWord_86910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86933 : List Nat := [1, 3, 2, 1, 1, 6, 5]
def baseStart_86933 : Nat := 118140960795 + 86933 * 2 ^ 59
def prefixEnd_86933 : Nat := 4983230072969 + 3 ^ 40 * 86933 * 2
def baseEnd_86933 : Nat := 8817464441958243543251

theorem tailTrace_86933 : CollatzResearch.WordTrace tailWord_86933 prefixEnd_86933 8817464441958243543251 := by
  unfold tailWord_86933
  simp only [CollatzResearch.WordTrace]
  refine ⟨3170706994064062819481453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2113804662709375212987635 3170706994064062819481453)
  ·
    refine ⟨1189015122774023557305545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3170706994064062819481453 1189015122774023557305545)
    ·
      refine ⟨891761342080517667979159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1189015122774023557305545 891761342080517667979159)
      ·
        refine ⟨1337642013120776501968739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891761342080517667979159 1337642013120776501968739)
        ·
          refine ⟨2006463019681164752953109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337642013120776501968739 2006463019681164752953109)
          ·
            refine ⟨94052954047554597794677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2006463019681164752953109 94052954047554597794677)
            ·
              refine ⟨8817464441958243543251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94052954047554597794677 8817464441958243543251)
              ·
                rfl

theorem cell19_86933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 5].length) (baseStart_86933 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86933 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86933 prefixEnd_86933 := by exact prefixLift 86933
  have htrace : WordTrace (prefixWord ++ tailWord_86933) baseStart_86933 baseEnd_86933 := by
    simpa [prefixWord, tailWord_86933, baseEnd_86933] using wordTrace_append hprefix tailTrace_86933
  have hstable : (prefixWord ++ tailWord_86933).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86933).length < 2 ^ (prefixWord ++ tailWord_86933).sum := by decide
  have hdescent : baseEnd_86933 < baseStart_86933 := by decide
  rcases family_descends (prefixWord ++ tailWord_86933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86982 : List Nat := [6, 1, 3, 1, 2, 6]
def baseStart_86982 : Nat := 118140960795 + 86982 * 2 ^ 59
def prefixEnd_86982 : Nat := 4983230072969 + 3 ^ 40 * 86982 * 2
def baseEnd_86982 : Nat := 2940811475850792837859

theorem tailTrace_86982 : CollatzResearch.WordTrace tailWord_86982 prefixEnd_86982 2940811475850792837859 := by
  unfold tailWord_86982
  simp only [CollatzResearch.WordTrace]
  refine ⟨99140442840204505875475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2114996113924362792010133 99140442840204505875475)
  ·
    refine ⟨148710664260306758813213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99140442840204505875475 148710664260306758813213)
    ·
      refine ⟨55766499097615034554955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148710664260306758813213 55766499097615034554955)
      ·
        refine ⟨83649748646422551832433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55766499097615034554955 83649748646422551832433)
        ·
          refine ⟨62737311484816913874325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83649748646422551832433 62737311484816913874325)
          ·
            refine ⟨2940811475850792837859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62737311484816913874325 2940811475850792837859)
            ·
              rfl

theorem cell19_86982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 6].length) (baseStart_86982 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_86982 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_86982 prefixEnd_86982 := by exact prefixLift 86982
  have htrace : WordTrace (prefixWord ++ tailWord_86982) baseStart_86982 baseEnd_86982 := by
    simpa [prefixWord, tailWord_86982, baseEnd_86982] using wordTrace_append hprefix tailTrace_86982
  have hstable : (prefixWord ++ tailWord_86982).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86982).length < 2 ^ (prefixWord ++ tailWord_86982).sum := by decide
  have hdescent : baseEnd_86982 < baseStart_86982 := by decide
  rcases family_descends (prefixWord ++ tailWord_86982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87007 : List Nat := [1, 1, 2, 3, 5, 2, 1, 4]
def baseStart_87007 : Nat := 118140960795 + 87007 * 2 ^ 59
def prefixEnd_87007 : Nat := 4983230072969 + 3 ^ 40 * 87007 * 2
def baseEnd_87007 : Nat := 26474910403464484985107

theorem tailTrace_87007 : CollatzResearch.WordTrace tailWord_87007 prefixEnd_87007 26474910403464484985107 := by
  unfold tailWord_87007
  simp only [CollatzResearch.WordTrace]
  refine ⟨3173405995795973457675275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2115603997197315638450183 3173405995795973457675275)
  ·
    refine ⟨4760108993693960186512913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3173405995795973457675275 4760108993693960186512913)
    ·
      refine ⟨3570081745270470139884685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4760108993693960186512913 3570081745270470139884685)
      ·
        refine ⟨1338780654476426302456757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3570081745270470139884685 1338780654476426302456757)
        ·
          refine ⟨125510686357164965855321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1338780654476426302456757 125510686357164965855321)
          ·
            refine ⟨94133014767873724391491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125510686357164965855321 94133014767873724391491)
            ·
              refine ⟨141199522151810586587237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94133014767873724391491 141199522151810586587237)
              ·
                refine ⟨26474910403464484985107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141199522151810586587237 26474910403464484985107)
                ·
                  rfl

theorem cell19_87007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 4].length) (baseStart_87007 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87007 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87007 prefixEnd_87007 := by exact prefixLift 87007
  have htrace : WordTrace (prefixWord ++ tailWord_87007) baseStart_87007 baseEnd_87007 := by
    simpa [prefixWord, tailWord_87007, baseEnd_87007] using wordTrace_append hprefix tailTrace_87007
  have hstable : (prefixWord ++ tailWord_87007).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87007).length < 2 ^ (prefixWord ++ tailWord_87007).sum := by decide
  have hdescent : baseEnd_87007 < baseStart_87007 := by decide
  rcases family_descends (prefixWord ++ tailWord_87007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87102 : List Nat := [4, 2, 1, 3, 1, 3, 5]
def baseStart_87102 : Nat := 118140960795 + 87102 * 2 ^ 59
def prefixEnd_87102 : Nat := 4983230072969 + 3 ^ 40 * 87102 * 2
def baseEnd_87102 : Nat := 8834605820844137624579

theorem tailTrace_87102 : CollatzResearch.WordTrace tailWord_87102 prefixEnd_87102 8834605820844137624579 := by
  unfold tailWord_87102
  simp only [CollatzResearch.WordTrace]
  refine ⟨397108866306475585297945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2117913953634536454922373 397108866306475585297945)
  ·
    refine ⟨297831649729856688973459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 397108866306475585297945 297831649729856688973459)
    ·
      refine ⟨446747474594785033460189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297831649729856688973459 446747474594785033460189)
      ·
        refine ⟨167530302973044387547571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 446747474594785033460189 167530302973044387547571)
        ·
          refine ⟨251295454459566581321357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167530302973044387547571 251295454459566581321357)
          ·
            refine ⟨94235795422337467995509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251295454459566581321357 94235795422337467995509)
            ·
              refine ⟨8834605820844137624579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94235795422337467995509 8834605820844137624579)
              ·
                rfl

theorem cell19_87102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 5].length) (baseStart_87102 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87102 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87102 prefixEnd_87102 := by exact prefixLift 87102
  have htrace : WordTrace (prefixWord ++ tailWord_87102) baseStart_87102 baseEnd_87102 := by
    simpa [prefixWord, tailWord_87102, baseEnd_87102] using wordTrace_append hprefix tailTrace_87102
  have hstable : (prefixWord ++ tailWord_87102).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87102).length < 2 ^ (prefixWord ++ tailWord_87102).sum := by decide
  have hdescent : baseEnd_87102 < baseStart_87102 := by decide
  rcases family_descends (prefixWord ++ tailWord_87102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87161 : List Nat := [1, 2, 1, 3, 6, 6]
def baseStart_87161 : Nat := 118140960795 + 87161 * 2 ^ 59
def prefixEnd_87161 : Nat := 4983230072969 + 3 ^ 40 * 87161 * 2
def baseEnd_87161 : Nat := 2946863363070861951385

theorem tailTrace_87161 : CollatzResearch.WordTrace tailWord_87161 prefixEnd_87161 2946863363070861951385 := by
  unfold tailWord_87161
  simp only [CollatzResearch.WordTrace]
  refine ⟨3179022837238057758781337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2119348558158705172520891 3179022837238057758781337)
  ·
    refine ⟨2384267127928543319086003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3179022837238057758781337 2384267127928543319086003)
    ·
      refine ⟨3576400691892814978629005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2384267127928543319086003 3576400691892814978629005)
      ·
        refine ⟨1341150259459805616985877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3576400691892814978629005 1341150259459805616985877)
        ·
          refine ⟨62866418412178388296213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1341150259459805616985877 62866418412178388296213)
          ·
            refine ⟨2946863363070861951385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62866418412178388296213 2946863363070861951385)
            ·
              rfl

theorem cell19_87161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 6].length) (baseStart_87161 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87161 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87161 prefixEnd_87161 := by exact prefixLift 87161
  have htrace : WordTrace (prefixWord ++ tailWord_87161) baseStart_87161 baseEnd_87161 := by
    simpa [prefixWord, tailWord_87161, baseEnd_87161] using wordTrace_append hprefix tailTrace_87161
  have hstable : (prefixWord ++ tailWord_87161).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87161).length < 2 ^ (prefixWord ++ tailWord_87161).sum := by decide
  have hdescent : baseEnd_87161 < baseStart_87161 := by decide
  rcases family_descends (prefixWord ++ tailWord_87161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87176 : List Nat := [2, 1, 3, 4, 3, 1, 1, 4]
def baseStart_87176 : Nat := 118140960795 + 87176 * 2 ^ 59
def prefixEnd_87176 : Nat := 4983230072969 + 3 ^ 40 * 87176 * 2
def baseEnd_87176 : Nat := 26526334540122167229091

theorem tailTrace_87176 : CollatzResearch.WordTrace tailWord_87176 prefixEnd_87176 26526334540122167229091 := by
  unfold tailWord_87176
  simp only [CollatzResearch.WordTrace]
  refine ⟨1589784966091857660288691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2119713288122476880384921 1589784966091857660288691)
  ·
    refine ⟨2384677449137786490433037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1589784966091857660288691 2384677449137786490433037)
    ·
      refine ⟨894254043426669933912389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2384677449137786490433037 894254043426669933912389)
      ·
        refine ⟨167672633142500612608573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 894254043426669933912389 167672633142500612608573)
        ·
          refine ⟨62877237428437729728215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167672633142500612608573 62877237428437729728215)
          ·
            refine ⟨94315856142656594592323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62877237428437729728215 94315856142656594592323)
            ·
              refine ⟨141473784213984891888485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94315856142656594592323 141473784213984891888485)
              ·
                refine ⟨26526334540122167229091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141473784213984891888485 26526334540122167229091)
                ·
                  rfl

theorem cell19_87176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_87176 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87176 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87176 prefixEnd_87176 := by exact prefixLift 87176
  have htrace : WordTrace (prefixWord ++ tailWord_87176) baseStart_87176 baseEnd_87176 := by
    simpa [prefixWord, tailWord_87176, baseEnd_87176] using wordTrace_append hprefix tailTrace_87176
  have hstable : (prefixWord ++ tailWord_87176).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87176).length < 2 ^ (prefixWord ++ tailWord_87176).sum := by decide
  have hdescent : baseEnd_87176 < baseStart_87176 := by decide
  rcases family_descends (prefixWord ++ tailWord_87176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87256 : List Nat := [2, 1, 2, 2, 5, 1, 1, 5]
def baseStart_87256 : Nat := 118140960795 + 87256 * 2 ^ 59
def prefixEnd_87256 : Nat := 4983230072969 + 3 ^ 40 * 87256 * 2
def baseEnd_87256 : Nat := 26550677326705685451095

theorem tailTrace_87256 : CollatzResearch.WordTrace tailWord_87256 prefixEnd_87256 26550677326705685451095 := by
  unfold tailWord_87256
  simp only [CollatzResearch.WordTrace]
  refine ⟨1591243885946944491744811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2121658514595925988993081 1591243885946944491744811)
  ·
    refine ⟨2386865828920416737617217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1591243885946944491744811 2386865828920416737617217)
    ·
      refine ⟨1790149371690312553212913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2386865828920416737617217 1790149371690312553212913)
      ·
        refine ⟨1342612028767734414909685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1790149371690312553212913 1342612028767734414909685)
        ·
          refine ⟨125869877696975101397783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1342612028767734414909685 125869877696975101397783)
          ·
            refine ⟨188804816545462652096675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125869877696975101397783 188804816545462652096675)
            ·
              refine ⟨283207224818193978145013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188804816545462652096675 283207224818193978145013)
              ·
                refine ⟨26550677326705685451095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 283207224818193978145013 26550677326705685451095)
                ·
                  rfl

theorem cell19_87256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_87256 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87256 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87256 prefixEnd_87256 := by exact prefixLift 87256
  have htrace : WordTrace (prefixWord ++ tailWord_87256) baseStart_87256 baseEnd_87256 := by
    simpa [prefixWord, tailWord_87256, baseEnd_87256] using wordTrace_append hprefix tailTrace_87256
  have hstable : (prefixWord ++ tailWord_87256).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87256).length < 2 ^ (prefixWord ++ tailWord_87256).sum := by decide
  have hdescent : baseEnd_87256 < baseStart_87256 := by decide
  rcases family_descends (prefixWord ++ tailWord_87256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87294 : List Nat := [4, 2, 2, 1, 1, 2, 1, 6]
def baseStart_87294 : Nat := 118140960795 + 87294 * 2 ^ 59
def prefixEnd_87294 : Nat := 4983230072969 + 3 ^ 40 * 87294 * 2
def baseEnd_87294 : Nat := 26562240150332856606547

theorem tailTrace_87294 : CollatzResearch.WordTrace tailWord_87294 prefixEnd_87294 26562240150332856606547 := by
  unfold tailWord_87294
  simp only [CollatzResearch.WordTrace]
  refine ⟨397984218219527684171617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2122582497170814315581957 397984218219527684171617)
  ·
    refine ⟨298488163664645763128713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 397984218219527684171617 298488163664645763128713)
    ·
      refine ⟨223866122748484322346535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298488163664645763128713 223866122748484322346535)
      ·
        refine ⟨335799184122726483519803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223866122748484322346535 335799184122726483519803)
        ·
          refine ⟨503698776184089725279705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335799184122726483519803 503698776184089725279705)
          ·
            refine ⟨377774082138067293959779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503698776184089725279705 377774082138067293959779)
            ·
              refine ⟨566661123207100940939669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377774082138067293959779 566661123207100940939669)
              ·
                refine ⟨26562240150332856606547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 566661123207100940939669 26562240150332856606547)
                ·
                  rfl

theorem cell19_87294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_87294 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87294 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87294 prefixEnd_87294 := by exact prefixLift 87294
  have htrace : WordTrace (prefixWord ++ tailWord_87294) baseStart_87294 baseEnd_87294 := by
    simpa [prefixWord, tailWord_87294, baseEnd_87294] using wordTrace_append hprefix tailTrace_87294
  have hstable : (prefixWord ++ tailWord_87294).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87294).length < 2 ^ (prefixWord ++ tailWord_87294).sum := by decide
  have hdescent : baseEnd_87294 < baseStart_87294 := by decide
  rcases family_descends (prefixWord ++ tailWord_87294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87410 : List Nat := [3, 2, 1, 2, 1, 2, 2, 6]
def baseStart_87410 : Nat := 118140960795 + 87410 * 2 ^ 59
def prefixEnd_87410 : Nat := 4983230072969 + 3 ^ 40 * 87410 * 2
def baseEnd_87410 : Nat := 26597537190878958028453

theorem tailTrace_87410 : CollatzResearch.WordTrace tailWord_87410 prefixEnd_87410 26597537190878958028453 := by
  unfold tailWord_87410
  simp only [CollatzResearch.WordTrace]
  refine ⟨797026153333993321148921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2125403075557315523063789 797026153333993321148921)
  ·
    refine ⟨597769615000494990861691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 797026153333993321148921 597769615000494990861691)
    ·
      refine ⟨896654422500742486292537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 597769615000494990861691 896654422500742486292537)
      ·
        refine ⟨672490816875556864719403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 896654422500742486292537 672490816875556864719403)
        ·
          refine ⟨1008736225313335297079105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672490816875556864719403 1008736225313335297079105)
          ·
            refine ⟨756552168985001472809329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1008736225313335297079105 756552168985001472809329)
            ·
              refine ⟨567414126738751104606997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 756552168985001472809329 567414126738751104606997)
              ·
                refine ⟨26597537190878958028453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 567414126738751104606997 26597537190878958028453)
                ·
                  rfl

theorem cell19_87410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_87410 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87410 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87410 prefixEnd_87410 := by exact prefixLift 87410
  have htrace : WordTrace (prefixWord ++ tailWord_87410) baseStart_87410 baseEnd_87410 := by
    simpa [prefixWord, tailWord_87410, baseEnd_87410] using wordTrace_append hprefix tailTrace_87410
  have hstable : (prefixWord ++ tailWord_87410).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87410).length < 2 ^ (prefixWord ++ tailWord_87410).sum := by decide
  have hdescent : baseEnd_87410 < baseStart_87410 := by decide
  rcases family_descends (prefixWord ++ tailWord_87410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87427 : List Nat := [1, 1, 1, 3, 5, 1, 4, 3]
def baseStart_87427 : Nat := 118140960795 + 87427 * 2 ^ 59
def prefixEnd_87427 : Nat := 4983230072969 + 3 ^ 40 * 87427 * 2
def baseEnd_87427 : Nat := 26602710033027955650629

theorem tailTrace_87427 : CollatzResearch.WordTrace tailWord_87427 prefixEnd_87427 26602710033027955650629 := by
  unfold tailWord_87427
  simp only [CollatzResearch.WordTrace]
  refine ⟨3188724654274385187964535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2125816436182923458643023 3188724654274385187964535)
  ·
    refine ⟨4783086981411577781946803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3188724654274385187964535 4783086981411577781946803)
    ·
      refine ⟨7174630472117366672920205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4783086981411577781946803 7174630472117366672920205)
      ·
        refine ⟨2690486427044012502345077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7174630472117366672920205 2690486427044012502345077)
        ·
          refine ⟨252233102535376172094851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2690486427044012502345077 252233102535376172094851)
          ·
            refine ⟨378349653803064258142277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252233102535376172094851 378349653803064258142277)
            ·
              refine ⟨70940560088074548401677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 378349653803064258142277 70940560088074548401677)
              ·
                refine ⟨26602710033027955650629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70940560088074548401677 26602710033027955650629)
                ·
                  rfl

theorem cell19_87427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 3].length) (baseStart_87427 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87427 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87427 prefixEnd_87427 := by exact prefixLift 87427
  have htrace : WordTrace (prefixWord ++ tailWord_87427) baseStart_87427 baseEnd_87427 := by
    simpa [prefixWord, tailWord_87427, baseEnd_87427] using wordTrace_append hprefix tailTrace_87427
  have hstable : (prefixWord ++ tailWord_87427).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87427).length < 2 ^ (prefixWord ++ tailWord_87427).sum := by decide
  have hdescent : baseEnd_87427 < baseStart_87427 := by decide
  rcases family_descends (prefixWord ++ tailWord_87427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87442 : List Nat := [3, 2, 3, 3, 2, 1, 5]
def baseStart_87442 : Nat := 118140960795 + 87442 * 2 ^ 59
def prefixEnd_87442 : Nat := 4983230072969 + 3 ^ 40 * 87442 * 2
def baseEnd_87442 : Nat := 8869091435170788439085

theorem tailTrace_87442 : CollatzResearch.WordTrace tailWord_87442 prefixEnd_87442 8869091435170788439085 := by
  unfold tailWord_87442
  simp only [CollatzResearch.WordTrace]
  refine ⟨797317937305010687440145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2126181166146695166507053 797317937305010687440145)
  ·
    refine ⟨597988452978758015580109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 797317937305010687440145 597988452978758015580109)
    ·
      refine ⟨224245669867034255842541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 597988452978758015580109 224245669867034255842541)
      ·
        refine ⟨84092126200137845940953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224245669867034255842541 84092126200137845940953)
        ·
          refine ⟨63069094650103384455715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84092126200137845940953 63069094650103384455715)
          ·
            refine ⟨94603641975155076683573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63069094650103384455715 94603641975155076683573)
            ·
              refine ⟨8869091435170788439085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94603641975155076683573 8869091435170788439085)
              ·
                rfl

theorem cell19_87442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 5].length) (baseStart_87442 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87442 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87442 prefixEnd_87442 := by exact prefixLift 87442
  have htrace : WordTrace (prefixWord ++ tailWord_87442) baseStart_87442 baseEnd_87442 := by
    simpa [prefixWord, tailWord_87442, baseEnd_87442] using wordTrace_append hprefix tailTrace_87442
  have hstable : (prefixWord ++ tailWord_87442).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87442).length < 2 ^ (prefixWord ++ tailWord_87442).sum := by decide
  have hdescent : baseEnd_87442 < baseStart_87442 := by decide
  rcases family_descends (prefixWord ++ tailWord_87442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87562 : List Nat := [3, 1, 2, 2, 2, 3, 6]
def baseStart_87562 : Nat := 118140960795 + 87562 * 2 ^ 59
def prefixEnd_87562 : Nat := 4983230072969 + 3 ^ 40 * 87562 * 2
def baseEnd_87562 : Nat := 8881262828462547550087

theorem tailTrace_87562 : CollatzResearch.WordTrace tailWord_87562 prefixEnd_87562 8881262828462547550087 := by
  unfold tailWord_87562
  simp only [CollatzResearch.WordTrace]
  refine ⟨798412127196325811032235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2129099005856868829419293 798412127196325811032235)
  ·
    refine ⟨1197618190794488716548353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 798412127196325811032235 1197618190794488716548353)
    ·
      refine ⟨898213643095866537411265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1197618190794488716548353 898213643095866537411265)
      ·
        refine ⟨673660232321899903058449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 898213643095866537411265 673660232321899903058449)
        ·
          refine ⟨505245174241424927293837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 673660232321899903058449 505245174241424927293837)
          ·
            refine ⟨189466940340534347735189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 505245174241424927293837 189466940340534347735189)
            ·
              refine ⟨8881262828462547550087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 189466940340534347735189 8881262828462547550087)
              ·
                rfl

theorem cell19_87562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 6].length) (baseStart_87562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87562 prefixEnd_87562 := by exact prefixLift 87562
  have htrace : WordTrace (prefixWord ++ tailWord_87562) baseStart_87562 baseEnd_87562 := by
    simpa [prefixWord, tailWord_87562, baseEnd_87562] using wordTrace_append hprefix tailTrace_87562
  have hstable : (prefixWord ++ tailWord_87562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87562).length < 2 ^ (prefixWord ++ tailWord_87562).sum := by decide
  have hdescent : baseEnd_87562 < baseStart_87562 := by decide
  rcases family_descends (prefixWord ++ tailWord_87562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87581 : List Nat := [1, 4, 2, 2, 1, 1, 2, 6]
def baseStart_87581 : Nat := 118140960795 + 87581 * 2 ^ 59
def prefixEnd_87581 : Nat := 4983230072969 + 3 ^ 40 * 87581 * 2
def baseEnd_87581 : Nat := 26649569897201228227987

theorem tailTrace_87581 : CollatzResearch.WordTrace tailWord_87581 prefixEnd_87581 26649569897201228227987 := by
  unfold tailWord_87581
  simp only [CollatzResearch.WordTrace]
  refine ⟨3194341495716469489070597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2129560997144312992713731 3194341495716469489070597)
  ·
    refine ⟨598939030446838029200737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3194341495716469489070597 598939030446838029200737)
    ·
      refine ⟨449204272835128521900553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 598939030446838029200737 449204272835128521900553)
      ·
        refine ⟨336903204626346391425415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449204272835128521900553 336903204626346391425415)
        ·
          refine ⟨505354806939519587138123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336903204626346391425415 505354806939519587138123)
          ·
            refine ⟨758032210409279380707185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505354806939519587138123 758032210409279380707185)
            ·
              refine ⟨568524157806959535530389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 758032210409279380707185 568524157806959535530389)
              ·
                refine ⟨26649569897201228227987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 568524157806959535530389 26649569897201228227987)
                ·
                  rfl

theorem cell19_87581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_87581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87581 prefixEnd_87581 := by exact prefixLift 87581
  have htrace : WordTrace (prefixWord ++ tailWord_87581) baseStart_87581 baseEnd_87581 := by
    simpa [prefixWord, tailWord_87581, baseEnd_87581] using wordTrace_append hprefix tailTrace_87581
  have hstable : (prefixWord ++ tailWord_87581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87581).length < 2 ^ (prefixWord ++ tailWord_87581).sum := by decide
  have hdescent : baseEnd_87581 < baseStart_87581 := by decide
  rcases family_descends (prefixWord ++ tailWord_87581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87598 : List Nat := [4, 1, 3, 1, 2, 2, 1, 5]
def baseStart_87598 : Nat := 118140960795 + 87598 * 2 ^ 59
def prefixEnd_87598 : Nat := 4983230072969 + 3 ^ 40 * 87598 * 2
def baseEnd_87598 : Nat := 26654742739350225850163

theorem tailTrace_87598 : CollatzResearch.WordTrace tailWord_87598 prefixEnd_87598 26654742739350225850163 := by
  unfold tailWord_87598
  simp only [CollatzResearch.WordTrace]
  refine ⟨399370192081860174054931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2129974357769920928292965 399370192081860174054931)
  ·
    refine ⟨599055288122790261082397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 399370192081860174054931 599055288122790261082397)
    ·
      refine ⟨224645733046046347905899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 599055288122790261082397 224645733046046347905899)
      ·
        refine ⟨336968599569069521858849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224645733046046347905899 336968599569069521858849)
        ·
          refine ⟨252726449676802141394137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336968599569069521858849 252726449676802141394137)
          ·
            refine ⟨189544837257601606045603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252726449676802141394137 189544837257601606045603)
            ·
              refine ⟨284317255886402409068405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189544837257601606045603 284317255886402409068405)
              ·
                refine ⟨26654742739350225850163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 284317255886402409068405 26654742739350225850163)
                ·
                  rfl

theorem cell19_87598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_87598 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87598 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87598 prefixEnd_87598 := by exact prefixLift 87598
  have htrace : WordTrace (prefixWord ++ tailWord_87598) baseStart_87598 baseEnd_87598 := by
    simpa [prefixWord, tailWord_87598, baseEnd_87598] using wordTrace_append hprefix tailTrace_87598
  have hstable : (prefixWord ++ tailWord_87598).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87598).length < 2 ^ (prefixWord ++ tailWord_87598).sum := by decide
  have hdescent : baseEnd_87598 < baseStart_87598 := by decide
  rcases family_descends (prefixWord ++ tailWord_87598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87697 : List Nat := [1, 2, 2, 1, 1, 1, 1, 10]
def baseStart_87697 : Nat := 118140960795 + 87697 * 2 ^ 59
def prefixEnd_87697 : Nat := 4983230072969 + 3 ^ 40 * 87697 * 2
def baseEnd_87697 : Nat := 26684866937747329649893

theorem tailTrace_87697 : CollatzResearch.WordTrace tailWord_87697 prefixEnd_87697 26684866937747329649893 := by
  unfold tailWord_87697
  simp only [CollatzResearch.WordTrace]
  refine ⟨3198572363296221300293345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2132381575530814200195563 3198572363296221300293345)
  ·
    refine ⟨2398929272472165975220009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3198572363296221300293345 2398929272472165975220009)
    ·
      refine ⟨1799196954354124481415007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2398929272472165975220009 1799196954354124481415007)
      ·
        refine ⟨2698795431531186722122511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1799196954354124481415007 2698795431531186722122511)
        ·
          refine ⟨4048193147296780083183767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2698795431531186722122511 4048193147296780083183767)
          ·
            refine ⟨6072289720945170124775651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4048193147296780083183767 6072289720945170124775651)
            ·
              refine ⟨9108434581417755187163477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6072289720945170124775651 9108434581417755187163477)
              ·
                refine ⟨26684866937747329649893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9108434581417755187163477 26684866937747329649893)
                ·
                  rfl

theorem cell19_87697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_87697 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87697 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87697 prefixEnd_87697 := by exact prefixLift 87697
  have htrace : WordTrace (prefixWord ++ tailWord_87697) baseStart_87697 baseEnd_87697 := by
    simpa [prefixWord, tailWord_87697, baseEnd_87697] using wordTrace_append hprefix tailTrace_87697
  have hstable : (prefixWord ++ tailWord_87697).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87697).length < 2 ^ (prefixWord ++ tailWord_87697).sum := by decide
  have hdescent : baseEnd_87697 < baseStart_87697 := by decide
  rcases family_descends (prefixWord ++ tailWord_87697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87710 : List Nat := [4, 3, 1, 1, 1, 3, 3, 3]
def baseStart_87710 : Nat := 118140960795 + 87710 * 2 ^ 59
def prefixEnd_87710 : Nat := 4983230072969 + 3 ^ 40 * 87710 * 2
def baseEnd_87710 : Nat := 26688822640567151360969

theorem tailTrace_87710 : CollatzResearch.WordTrace tailWord_87710 prefixEnd_87710 26688822640567151360969 := by
  unfold tailWord_87710
  simp only [CollatzResearch.WordTrace]
  refine ⟨399880814031140565064573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2132697674832749680344389 399880814031140565064573)
  ·
    refine ⟨149955305261677711899215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 399880814031140565064573 149955305261677711899215)
    ·
      refine ⟨224932957892516567848823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149955305261677711899215 224932957892516567848823)
      ·
        refine ⟨337399436838774851773235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224932957892516567848823 337399436838774851773235)
        ·
          refine ⟨506099155258162277659853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337399436838774851773235 506099155258162277659853)
          ·
            refine ⟨189787183221810854122445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 506099155258162277659853 189787183221810854122445)
            ·
              refine ⟨71170193708179070295917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189787183221810854122445 71170193708179070295917)
              ·
                refine ⟨26688822640567151360969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71170193708179070295917 26688822640567151360969)
                ·
                  rfl

theorem cell19_87710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_87710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87710 prefixEnd_87710 := by exact prefixLift 87710
  have htrace : WordTrace (prefixWord ++ tailWord_87710) baseStart_87710 baseEnd_87710 := by
    simpa [prefixWord, tailWord_87710, baseEnd_87710] using wordTrace_append hprefix tailTrace_87710
  have hstable : (prefixWord ++ tailWord_87710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87710).length < 2 ^ (prefixWord ++ tailWord_87710).sum := by decide
  have hdescent : baseEnd_87710 < baseStart_87710 := by decide
  rcases family_descends (prefixWord ++ tailWord_87710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87712 : List Nat := [2, 1, 1, 4, 3, 2, 3, 3]
def baseStart_87712 : Nat := 118140960795 + 87712 * 2 ^ 59
def prefixEnd_87712 : Nat := 4983230072969 + 3 ^ 40 * 87712 * 2
def baseEnd_87712 : Nat := 26689431210231739316519

theorem tailTrace_87712 : CollatzResearch.WordTrace tailWord_87712 prefixEnd_87712 26689431210231739316519 := by
  unfold tailWord_87712
  simp only [CollatzResearch.WordTrace]
  refine ⟨1599559729120939431044695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2132746305494585908059593 1599559729120939431044695)
  ·
    refine ⟨2399339593681409146567043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1599559729120939431044695 2399339593681409146567043)
    ·
      refine ⟨3599009390522113719850565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2399339593681409146567043 3599009390522113719850565)
      ·
        refine ⟨674814260722896322471981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3599009390522113719850565 674814260722896322471981)
        ·
          refine ⟨253055347771086120926993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 674814260722896322471981 253055347771086120926993)
          ·
            refine ⟨189791510828314590695245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253055347771086120926993 189791510828314590695245)
            ·
              refine ⟨71171816560617971510717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189791510828314590695245 71171816560617971510717)
              ·
                refine ⟨26689431210231739316519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71171816560617971510717 26689431210231739316519)
                ·
                  rfl

theorem cell19_87712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_87712 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87712 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87712 prefixEnd_87712 := by exact prefixLift 87712
  have htrace : WordTrace (prefixWord ++ tailWord_87712) baseStart_87712 baseEnd_87712 := by
    simpa [prefixWord, tailWord_87712, baseEnd_87712] using wordTrace_append hprefix tailTrace_87712
  have hstable : (prefixWord ++ tailWord_87712).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87712).length < 2 ^ (prefixWord ++ tailWord_87712).sum := by decide
  have hdescent : baseEnd_87712 < baseStart_87712 := by decide
  rcases family_descends (prefixWord ++ tailWord_87712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87769 : List Nat := [1, 2, 1, 2, 3, 5, 2, 3]
def baseStart_87769 : Nat := 118140960795 + 87769 * 2 ^ 59
def prefixEnd_87769 : Nat := 4983230072969 + 3 ^ 40 * 87769 * 2
def baseEnd_87769 : Nat := 26706775445672496049697

theorem tailTrace_87769 : CollatzResearch.WordTrace tailWord_87769 prefixEnd_87769 26706775445672496049697 := by
  unfold tailWord_87769
  simp only [CollatzResearch.WordTrace]
  refine ⟨3201198419035377596914361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2134132279356918397942907 3201198419035377596914361)
  ·
    refine ⟨2400898814276533197685771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3201198419035377596914361 2400898814276533197685771)
    ·
      refine ⟨3601348221414799796528657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2400898814276533197685771 3601348221414799796528657)
      ·
        refine ⟨2701011166061099847396493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3601348221414799796528657 2701011166061099847396493)
        ·
          refine ⟨1012879187272912442773685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2701011166061099847396493 1012879187272912442773685)
          ·
            refine ⟨94957423806835541510033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1012879187272912442773685 94957423806835541510033)
            ·
              refine ⟨71218067855126656132525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94957423806835541510033 71218067855126656132525)
              ·
                refine ⟨26706775445672496049697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71218067855126656132525 26706775445672496049697)
                ·
                  rfl

theorem cell19_87769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 3].length) (baseStart_87769 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87769 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87769 prefixEnd_87769 := by exact prefixLift 87769
  have htrace : WordTrace (prefixWord ++ tailWord_87769) baseStart_87769 baseEnd_87769 := by
    simpa [prefixWord, tailWord_87769, baseEnd_87769] using wordTrace_append hprefix tailTrace_87769
  have hstable : (prefixWord ++ tailWord_87769).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87769).length < 2 ^ (prefixWord ++ tailWord_87769).sum := by decide
  have hdescent : baseEnd_87769 < baseStart_87769 := by decide
  rcases family_descends (prefixWord ++ tailWord_87769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87811 : List Nat := [1, 1, 1, 3, 2, 2, 3, 6]
def baseStart_87811 : Nat := 118140960795 + 87811 * 2 ^ 59
def prefixEnd_87811 : Nat := 4983230072969 + 3 ^ 40 * 87811 * 2
def baseEnd_87811 : Nat := 26719555408628843116249

theorem tailTrace_87811 : CollatzResearch.WordTrace tailWord_87811 prefixEnd_87811 26719555408628843116249 := by
  unfold tailWord_87811
  simp only [CollatzResearch.WordTrace]
  refine ⟨3202730284883218769943287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2135153523255479179962191 3202730284883218769943287)
  ·
    refine ⟨4804095427324828154914931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3202730284883218769943287 4804095427324828154914931)
    ·
      refine ⟨7206143140987242232372397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4804095427324828154914931 7206143140987242232372397)
      ·
        refine ⟨2702303677870215837139649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7206143140987242232372397 2702303677870215837139649)
        ·
          refine ⟨2026727758402661877854737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2702303677870215837139649 2026727758402661877854737)
          ·
            refine ⟨1520045818801996408391053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2026727758402661877854737 1520045818801996408391053)
            ·
              refine ⟨570017182050748653146645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1520045818801996408391053 570017182050748653146645)
              ·
                refine ⟨26719555408628843116249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 570017182050748653146645 26719555408628843116249)
                ·
                  rfl

theorem cell19_87811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_87811 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87811 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87811 prefixEnd_87811 := by exact prefixLift 87811
  have htrace : WordTrace (prefixWord ++ tailWord_87811) baseStart_87811 baseEnd_87811 := by
    simpa [prefixWord, tailWord_87811, baseEnd_87811] using wordTrace_append hprefix tailTrace_87811
  have hstable : (prefixWord ++ tailWord_87811).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87811).length < 2 ^ (prefixWord ++ tailWord_87811).sum := by decide
  have hdescent : baseEnd_87811 < baseStart_87811 := by decide
  rcases family_descends (prefixWord ++ tailWord_87811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87826 : List Nat := [3, 2, 4, 1, 1, 1, 2, 5]
def baseStart_87826 : Nat := 118140960795 + 87826 * 2 ^ 59
def prefixEnd_87826 : Nat := 4983230072969 + 3 ^ 40 * 87826 * 2
def baseEnd_87826 : Nat := 26724119681113252782875

theorem tailTrace_87826 : CollatzResearch.WordTrace tailWord_87826 prefixEnd_87826 26724119681113252782875 := by
  unfold tailWord_87826
  simp only [CollatzResearch.WordTrace]
  refine ⟨800819344957219082934833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2135518253219250887826221 800819344957219082934833)
  ·
    refine ⟨600614508717914312201125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 800819344957219082934833 600614508717914312201125)
    ·
      refine ⟨112615220384608933537711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 600614508717914312201125 112615220384608933537711)
      ·
        refine ⟨168922830576913400306567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112615220384608933537711 168922830576913400306567)
        ·
          refine ⟨253384245865370100459851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168922830576913400306567 253384245865370100459851)
          ·
            refine ⟨380076368798055150689777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253384245865370100459851 380076368798055150689777)
            ·
              refine ⟨285057276598541363017333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380076368798055150689777 285057276598541363017333)
              ·
                refine ⟨26724119681113252782875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 285057276598541363017333 26724119681113252782875)
                ·
                  rfl

theorem cell19_87826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_87826 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87826 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87826 prefixEnd_87826 := by exact prefixLift 87826
  have htrace : WordTrace (prefixWord ++ tailWord_87826) baseStart_87826 baseEnd_87826 := by
    simpa [prefixWord, tailWord_87826, baseEnd_87826] using wordTrace_append hprefix tailTrace_87826
  have hstable : (prefixWord ++ tailWord_87826).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87826).length < 2 ^ (prefixWord ++ tailWord_87826).sum := by decide
  have hdescent : baseEnd_87826 < baseStart_87826 := by decide
  rcases family_descends (prefixWord ++ tailWord_87826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87862 : List Nat := [5, 1, 2, 2, 1, 3, 1, 4]
def baseStart_87862 : Nat := 118140960795 + 87862 * 2 ^ 59
def prefixEnd_87862 : Nat := 4983230072969 + 3 ^ 40 * 87862 * 2
def baseEnd_87862 : Nat := 26735073935075835982777

theorem tailTrace_87862 : CollatzResearch.WordTrace tailWord_87862 prefixEnd_87862 26735073935075835982777 := by
  unfold tailWord_87862
  simp only [CollatzResearch.WordTrace]
  refine ⟨200286900481153405003115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2136393605132302986699893 200286900481153405003115)
  ·
    refine ⟨300430350721730107504673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200286900481153405003115 300430350721730107504673)
    ·
      refine ⟨225322763041297580628505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300430350721730107504673 225322763041297580628505)
      ·
        refine ⟨168992072280973185471379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225322763041297580628505 168992072280973185471379)
        ·
          refine ⟨253488108421459778207069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168992072280973185471379 253488108421459778207069)
          ·
            refine ⟨95058040658047416827651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253488108421459778207069 95058040658047416827651)
            ·
              refine ⟨142587060987071125241477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95058040658047416827651 142587060987071125241477)
              ·
                refine ⟨26735073935075835982777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142587060987071125241477 26735073935075835982777)
                ·
                  rfl

theorem cell19_87862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_87862 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87862 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87862 prefixEnd_87862 := by exact prefixLift 87862
  have htrace : WordTrace (prefixWord ++ tailWord_87862) baseStart_87862 baseEnd_87862 := by
    simpa [prefixWord, tailWord_87862, baseEnd_87862] using wordTrace_append hprefix tailTrace_87862
  have hstable : (prefixWord ++ tailWord_87862).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87862).length < 2 ^ (prefixWord ++ tailWord_87862).sum := by decide
  have hdescent : baseEnd_87862 < baseStart_87862 := by decide
  rcases family_descends (prefixWord ++ tailWord_87862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87866 : List Nat := [3, 1, 1, 1, 5, 1, 3, 4]
def baseStart_87866 : Nat := 118140960795 + 87866 * 2 ^ 59
def prefixEnd_87866 : Nat := 4983230072969 + 3 ^ 40 * 87866 * 2
def baseEnd_87866 : Nat := 26736291074405011893877

theorem tailTrace_87866 : CollatzResearch.WordTrace tailWord_87866 prefixEnd_87866 26736291074405011893877 := by
  unfold tailWord_87866
  simp only [CollatzResearch.WordTrace]
  refine ⟨801184074920990790798863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2136490866455975442130301 801184074920990790798863)
  ·
    refine ⟨1201776112381486186198295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 801184074920990790798863 1201776112381486186198295)
    ·
      refine ⟨1802664168572229279297443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1201776112381486186198295 1802664168572229279297443)
      ·
        refine ⟨2703996252858343918946165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1802664168572229279297443 2703996252858343918946165)
        ·
          refine ⟨253499648705469742401203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2703996252858343918946165 253499648705469742401203)
          ·
            refine ⟨380249473058204613601805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253499648705469742401203 380249473058204613601805)
            ·
              refine ⟨142593552396826730100677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 380249473058204613601805 142593552396826730100677)
              ·
                refine ⟨26736291074405011893877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142593552396826730100677 26736291074405011893877)
                ·
                  rfl

theorem cell19_87866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_87866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87866 prefixEnd_87866 := by exact prefixLift 87866
  have htrace : WordTrace (prefixWord ++ tailWord_87866) baseStart_87866 baseEnd_87866 := by
    simpa [prefixWord, tailWord_87866, baseEnd_87866] using wordTrace_append hprefix tailTrace_87866
  have hstable : (prefixWord ++ tailWord_87866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87866).length < 2 ^ (prefixWord ++ tailWord_87866).sum := by decide
  have hdescent : baseEnd_87866 < baseStart_87866 := by decide
  rcases family_descends (prefixWord ++ tailWord_87866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87976 : List Nat := [2, 1, 6, 2, 1, 1, 2, 4]
def baseStart_87976 : Nat := 118140960795 + 87976 * 2 ^ 59
def prefixEnd_87976 : Nat := 4983230072969 + 3 ^ 40 * 87976 * 2
def baseEnd_87976 : Nat := 26769762405957349449133

theorem tailTrace_87976 : CollatzResearch.WordTrace tailWord_87976 prefixEnd_87976 26769762405957349449133 := by
  unfold tailWord_87976
  simp only [CollatzResearch.WordTrace]
  refine ⟨1604374164642725974849891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2139165552856967966466521 1604374164642725974849891)
  ·
    refine ⟨2406561246964088962274837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1604374164642725974849891 2406561246964088962274837)
    ·
      refine ⟨112807558451441670106633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2406561246964088962274837 112807558451441670106633)
      ·
        refine ⟨84605668838581252579975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112807558451441670106633 84605668838581252579975)
        ·
          refine ⟨126908503257871878869963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84605668838581252579975 126908503257871878869963)
          ·
            refine ⟨190362754886807818304945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126908503257871878869963 190362754886807818304945)
            ·
              refine ⟨142772066165105863728709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190362754886807818304945 142772066165105863728709)
              ·
                refine ⟨26769762405957349449133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142772066165105863728709 26769762405957349449133)
                ·
                  rfl

theorem cell19_87976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_87976 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_87976 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_87976 prefixEnd_87976 := by exact prefixLift 87976
  have htrace : WordTrace (prefixWord ++ tailWord_87976) baseStart_87976 baseEnd_87976 := by
    simpa [prefixWord, tailWord_87976, baseEnd_87976] using wordTrace_append hprefix tailTrace_87976
  have hstable : (prefixWord ++ tailWord_87976).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87976).length < 2 ^ (prefixWord ++ tailWord_87976).sum := by decide
  have hdescent : baseEnd_87976 < baseStart_87976 := by decide
  rcases family_descends (prefixWord ++ tailWord_87976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88018 : List Nat := [3, 2, 2, 3, 2, 7]
def baseStart_88018 : Nat := 118140960795 + 88018 * 2 ^ 59
def prefixEnd_88018 : Nat := 4983230072969 + 3 ^ 40 * 88018 * 2
def baseEnd_88018 : Nat := 2975838040990410723965

theorem tailTrace_88018 : CollatzResearch.WordTrace tailWord_88018 prefixEnd_88018 2975838040990410723965 := by
  unfold tailWord_88018
  simp only [CollatzResearch.WordTrace]
  refine ⟨802570048783323280682177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2140186796755528748485805 802570048783323280682177)
  ·
    refine ⟨601927536587492460511633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 802570048783323280682177 601927536587492460511633)
    ·
      refine ⟨451445652440619345383725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 601927536587492460511633 451445652440619345383725)
      ·
        refine ⟨169292119665232254518897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 451445652440619345383725 169292119665232254518897)
        ·
          refine ⟨126969089748924190889173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169292119665232254518897 126969089748924190889173)
          ·
            refine ⟨2975838040990410723965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 126969089748924190889173 2975838040990410723965)
            ·
              rfl

theorem cell19_88018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 7].length) (baseStart_88018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88018 prefixEnd_88018 := by exact prefixLift 88018
  have htrace : WordTrace (prefixWord ++ tailWord_88018) baseStart_88018 baseEnd_88018 := by
    simpa [prefixWord, tailWord_88018, baseEnd_88018] using wordTrace_append hprefix tailTrace_88018
  have hstable : (prefixWord ++ tailWord_88018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88018).length < 2 ^ (prefixWord ++ tailWord_88018).sum := by decide
  have hdescent : baseEnd_88018 < baseStart_88018 := by decide
  rcases family_descends (prefixWord ++ tailWord_88018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88113 : List Nat := [1, 2, 2, 3, 1, 3, 4, 3]
def baseStart_88113 : Nat := 118140960795 + 88113 * 2 ^ 59
def prefixEnd_88113 : Nat := 4983230072969 + 3 ^ 40 * 88113 * 2
def baseEnd_88113 : Nat := 26811449427981624404315

theorem tailTrace_88113 : CollatzResearch.WordTrace tailWord_88113 prefixEnd_88113 26811449427981624404315 := by
  unfold tailWord_88113
  simp only [CollatzResearch.WordTrace]
  refine ⟨3213745129789124347436993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2142496753192749564957995 3213745129789124347436993)
  ·
    refine ⟨2410308847341843260577745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3213745129789124347436993 2410308847341843260577745)
    ·
      refine ⟨1807731635506382445433309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2410308847341843260577745 1807731635506382445433309)
      ·
        refine ⟨677899363314893417037491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1807731635506382445433309 677899363314893417037491)
        ·
          refine ⟨1016849044972340125556237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677899363314893417037491 1016849044972340125556237)
          ·
            refine ⟨381318391864627547083589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1016849044972340125556237 381318391864627547083589)
            ·
              refine ⟨71497198474617665078173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 381318391864627547083589 71497198474617665078173)
              ·
                refine ⟨26811449427981624404315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71497198474617665078173 26811449427981624404315)
                ·
                  rfl

theorem cell19_88113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 3].length) (baseStart_88113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88113 prefixEnd_88113 := by exact prefixLift 88113
  have htrace : WordTrace (prefixWord ++ tailWord_88113) baseStart_88113 baseEnd_88113 := by
    simpa [prefixWord, tailWord_88113, baseEnd_88113] using wordTrace_append hprefix tailTrace_88113
  have hstable : (prefixWord ++ tailWord_88113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88113).length < 2 ^ (prefixWord ++ tailWord_88113).sum := by decide
  have hdescent : baseEnd_88113 < baseStart_88113 := by decide
  rcases family_descends (prefixWord ++ tailWord_88113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88153 : List Nat := [1, 2, 1, 2, 2, 1, 6, 4]
def baseStart_88153 : Nat := 118140960795 + 88153 * 2 ^ 59
def prefixEnd_88153 : Nat := 4983230072969 + 3 ^ 40 * 88153 * 2
def baseEnd_88153 : Nat := 26823620821273383515317

theorem tailTrace_88153 : CollatzResearch.WordTrace tailWord_88153 prefixEnd_88153 26823620821273383515317 := by
  unfold tailWord_88153
  simp only [CollatzResearch.WordTrace]
  refine ⟨3215204049644211178893113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2143469366429474119262075 3215204049644211178893113)
  ·
    refine ⟨2411403037233158384169835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3215204049644211178893113 2411403037233158384169835)
    ·
      refine ⟨3617104555849737576254753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2411403037233158384169835 3617104555849737576254753)
      ·
        refine ⟨2712828416887303182191065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3617104555849737576254753 2712828416887303182191065)
        ·
          refine ⟨2034621312665477386643299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2712828416887303182191065 2034621312665477386643299)
          ·
            refine ⟨3051931968998216079964949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2034621312665477386643299 3051931968998216079964949)
            ·
              refine ⟨143059311046791378748357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3051931968998216079964949 143059311046791378748357)
              ·
                refine ⟨26823620821273383515317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143059311046791378748357 26823620821273383515317)
                ·
                  rfl

theorem cell19_88153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_88153 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88153 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88153 prefixEnd_88153 := by exact prefixLift 88153
  have htrace : WordTrace (prefixWord ++ tailWord_88153) baseStart_88153 baseEnd_88153 := by
    simpa [prefixWord, tailWord_88153, baseEnd_88153] using wordTrace_append hprefix tailTrace_88153
  have hstable : (prefixWord ++ tailWord_88153).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88153).length < 2 ^ (prefixWord ++ tailWord_88153).sum := by decide
  have hdescent : baseEnd_88153 < baseStart_88153 := by decide
  rcases family_descends (prefixWord ++ tailWord_88153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88172 : List Nat := [2, 2, 1, 1, 3, 3, 2, 5]
def baseStart_88172 : Nat := 118140960795 + 88172 * 2 ^ 59
def prefixEnd_88172 : Nat := 4983230072969 + 3 ^ 40 * 88172 * 2
def baseEnd_88172 : Nat := 26829402233086969093043

theorem tailTrace_88172 : CollatzResearch.WordTrace tailWord_88172 prefixEnd_88172 26829402233086969093043 := by
  unfold tailWord_88172
  simp only [CollatzResearch.WordTrace]
  refine ⟨1607948518287688711917385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2143931357716918282556513 1607948518287688711917385)
  ·
    refine ⟨1205961388715766533938039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1607948518287688711917385 1205961388715766533938039)
    ·
      refine ⟨1808942083073649800907059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1205961388715766533938039 1808942083073649800907059)
      ·
        refine ⟨2713413124610474701360589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1808942083073649800907059 2713413124610474701360589)
        ·
          refine ⟨1017529921728928013010221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2713413124610474701360589 1017529921728928013010221)
          ·
            refine ⟨381573720648348004878833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1017529921728928013010221 381573720648348004878833)
            ·
              refine ⟨286180290486261003659125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381573720648348004878833 286180290486261003659125)
              ·
                refine ⟨26829402233086969093043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 286180290486261003659125 26829402233086969093043)
                ·
                  rfl

theorem cell19_88172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_88172 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88172 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88172 prefixEnd_88172 := by exact prefixLift 88172
  have htrace : WordTrace (prefixWord ++ tailWord_88172) baseStart_88172 baseEnd_88172 := by
    simpa [prefixWord, tailWord_88172, baseEnd_88172] using wordTrace_append hprefix tailTrace_88172
  have hstable : (prefixWord ++ tailWord_88172).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88172).length < 2 ^ (prefixWord ++ tailWord_88172).sum := by decide
  have hdescent : baseEnd_88172 < baseStart_88172 := by decide
  rcases family_descends (prefixWord ++ tailWord_88172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88206 : List Nat := [4, 1, 1, 3, 3, 2, 1, 4]
def baseStart_88206 : Nat := 118140960795 + 88206 * 2 ^ 59
def prefixEnd_88206 : Nat := 4983230072969 + 3 ^ 40 * 88206 * 2
def baseEnd_88206 : Nat := 26839747917384964337395

theorem tailTrace_88206 : CollatzResearch.WordTrace tailWord_88206 prefixEnd_88206 26839747917384964337395 := by
  unfold tailWord_88206
  simp only [CollatzResearch.WordTrace]
  refine ⟨402142139806525153821559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2144758078968134153714981 402142139806525153821559)
  ·
    refine ⟨603213209709787730732339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 402142139806525153821559 603213209709787730732339)
    ·
      refine ⟨904819814564681596098509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 603213209709787730732339 904819814564681596098509)
      ·
        refine ⟨339307430461755598536941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 904819814564681596098509 339307430461755598536941)
        ·
          refine ⟨127240286423158349451353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339307430461755598536941 127240286423158349451353)
          ·
            refine ⟨95430214817368762088515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127240286423158349451353 95430214817368762088515)
            ·
              refine ⟨143145322226053143132773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95430214817368762088515 143145322226053143132773)
              ·
                refine ⟨26839747917384964337395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143145322226053143132773 26839747917384964337395)
                ·
                  rfl

theorem cell19_88206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_88206 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88206 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88206 prefixEnd_88206 := by exact prefixLift 88206
  have htrace : WordTrace (prefixWord ++ tailWord_88206) baseStart_88206 baseEnd_88206 := by
    simpa [prefixWord, tailWord_88206, baseEnd_88206] using wordTrace_append hprefix tailTrace_88206
  have hstable : (prefixWord ++ tailWord_88206).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88206).length < 2 ^ (prefixWord ++ tailWord_88206).sum := by decide
  have hdescent : baseEnd_88206 < baseStart_88206 := by decide
  rcases family_descends (prefixWord ++ tailWord_88206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88301 : List Nat := [1, 5, 1, 2, 4, 1, 5]
def baseStart_88301 : Nat := 118140960795 + 88301 * 2 ^ 59
def prefixEnd_88301 : Nat := 4983230072969 + 3 ^ 40 * 88301 * 2
def baseEnd_88301 : Nat := 8956218325484297408675

theorem tailTrace_88301 : CollatzResearch.WordTrace tailWord_88301 prefixEnd_88301 8956218325484297408675 := by
  unfold tailWord_88301
  simp only [CollatzResearch.WordTrace]
  refine ⟨3220602053108032455280757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2147068035405354970187171 3220602053108032455280757)
  ·
    refine ⟨301931442478878042682571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3220602053108032455280757 301931442478878042682571)
    ·
      refine ⟨452897163718317064023857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301931442478878042682571 452897163718317064023857)
      ·
        refine ⟨339672872788737798017893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 452897163718317064023857 339672872788737798017893)
        ·
          refine ⟨63688663647888337128355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 339672872788737798017893 63688663647888337128355)
          ·
            refine ⟨95532995471832505692533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63688663647888337128355 95532995471832505692533)
            ·
              refine ⟨8956218325484297408675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95532995471832505692533 8956218325484297408675)
              ·
                rfl

theorem cell19_88301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 5].length) (baseStart_88301 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88301 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88301 prefixEnd_88301 := by exact prefixLift 88301
  have htrace : WordTrace (prefixWord ++ tailWord_88301) baseStart_88301 baseEnd_88301 := by
    simpa [prefixWord, tailWord_88301, baseEnd_88301] using wordTrace_append hprefix tailTrace_88301
  have hstable : (prefixWord ++ tailWord_88301).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88301).length < 2 ^ (prefixWord ++ tailWord_88301).sum := by decide
  have hdescent : baseEnd_88301 < baseStart_88301 := by decide
  rcases family_descends (prefixWord ++ tailWord_88301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88322 : List Nat := [3, 4, 1, 1, 2, 1, 1, 6]
def baseStart_88322 : Nat := 118140960795 + 88322 * 2 ^ 59
def prefixEnd_88322 : Nat := 4983230072969 + 3 ^ 40 * 88322 * 2
def baseEnd_88322 : Nat := 26875044957931065759301

theorem tailTrace_88322 : CollatzResearch.WordTrace tailWord_88322 prefixEnd_88322 26875044957931065759301 := by
  unfold tailWord_88322
  simp only [CollatzResearch.WordTrace]
  refine ⟨805341996507988260448805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2147578657354635361196813 805341996507988260448805)
  ·
    refine ⟨151001624345247798834151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 805341996507988260448805 151001624345247798834151)
    ·
      refine ⟨226502436517871698251227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151001624345247798834151 226502436517871698251227)
      ·
        refine ⟨339753654776807547376841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226502436517871698251227 339753654776807547376841)
        ·
          refine ⟨254815241082605660532631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339753654776807547376841 254815241082605660532631)
          ·
            refine ⟨382222861623908490798947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254815241082605660532631 382222861623908490798947)
            ·
              refine ⟨573334292435862736198421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382222861623908490798947 573334292435862736198421)
              ·
                refine ⟨26875044957931065759301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 573334292435862736198421 26875044957931065759301)
                ·
                  rfl

theorem cell19_88322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_88322 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88322 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88322 prefixEnd_88322 := by exact prefixLift 88322
  have htrace : WordTrace (prefixWord ++ tailWord_88322) baseStart_88322 baseEnd_88322 := by
    simpa [prefixWord, tailWord_88322, baseEnd_88322] using wordTrace_append hprefix tailTrace_88322
  have hstable : (prefixWord ++ tailWord_88322).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88322).length < 2 ^ (prefixWord ++ tailWord_88322).sum := by decide
  have hdescent : baseEnd_88322 < baseStart_88322 := by decide
  rcases family_descends (prefixWord ++ tailWord_88322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88343 : List Nat := [1, 1, 3, 4, 1, 2, 2, 5]
def baseStart_88343 : Nat := 118140960795 + 88343 * 2 ^ 59
def prefixEnd_88343 : Nat := 4983230072969 + 3 ^ 40 * 88343 * 2
def baseEnd_88343 : Nat := 26881434939409239292577

theorem tailTrace_88343 : CollatzResearch.WordTrace tailWord_88343 prefixEnd_88343 26881434939409239292577 := by
  unfold tailWord_88343
  simp only [CollatzResearch.WordTrace]
  refine ⟨3222133918955873628309683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2148089279303915752206455 3222133918955873628309683)
  ·
    refine ⟨4833200878433810442464525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3222133918955873628309683 4833200878433810442464525)
    ·
      refine ⟨1812450329412678915924197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4833200878433810442464525 1812450329412678915924197)
      ·
        refine ⟨339834436764877296735787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1812450329412678915924197 339834436764877296735787)
        ·
          refine ⟨509751655147315945103681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339834436764877296735787 509751655147315945103681)
          ·
            refine ⟨382313741360486958827761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509751655147315945103681 382313741360486958827761)
            ·
              refine ⟨286735306020365219120821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382313741360486958827761 286735306020365219120821)
              ·
                refine ⟨26881434939409239292577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 286735306020365219120821 26881434939409239292577)
                ·
                  rfl

theorem cell19_88343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_88343 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88343 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88343 prefixEnd_88343 := by exact prefixLift 88343
  have htrace : WordTrace (prefixWord ++ tailWord_88343) baseStart_88343 baseEnd_88343 := by
    simpa [prefixWord, tailWord_88343, baseEnd_88343] using wordTrace_append hprefix tailTrace_88343
  have hstable : (prefixWord ++ tailWord_88343).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88343).length < 2 ^ (prefixWord ++ tailWord_88343).sum := by decide
  have hdescent : baseEnd_88343 < baseStart_88343 := by decide
  rcases family_descends (prefixWord ++ tailWord_88343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88360 : List Nat := [2, 1, 5, 1, 4, 6]
def baseStart_88360 : Nat := 118140960795 + 88360 * 2 ^ 59
def prefixEnd_88360 : Nat := 4983230072969 + 3 ^ 40 * 88360 * 2
def baseEnd_88360 : Nat := 2987400864617581879417

theorem tailTrace_88360 : CollatzResearch.WordTrace tailWord_88360 prefixEnd_88360 2987400864617581879417 := by
  unfold tailWord_88360
  simp only [CollatzResearch.WordTrace]
  refine ⟨1611376979947142765839267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2148502639929523687785689 1611376979947142765839267)
  ·
    refine ⟨2417065469920714148758901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1611376979947142765839267 2417065469920714148758901)
    ·
      refine ⟨226599887805066951446147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2417065469920714148758901 226599887805066951446147)
      ·
        refine ⟨339899831707600427169221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226599887805066951446147 339899831707600427169221)
        ·
          refine ⟨63731218445175080094229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 339899831707600427169221 63731218445175080094229)
          ·
            refine ⟨2987400864617581879417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 63731218445175080094229 2987400864617581879417)
            ·
              rfl

theorem cell19_88360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 6].length) (baseStart_88360 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88360 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88360 prefixEnd_88360 := by exact prefixLift 88360
  have htrace : WordTrace (prefixWord ++ tailWord_88360) baseStart_88360 baseEnd_88360 := by
    simpa [prefixWord, tailWord_88360, baseEnd_88360] using wordTrace_append hprefix tailTrace_88360
  have hstable : (prefixWord ++ tailWord_88360).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88360).length < 2 ^ (prefixWord ++ tailWord_88360).sum := by decide
  have hdescent : baseEnd_88360 < baseStart_88360 := by decide
  rcases family_descends (prefixWord ++ tailWord_88360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88362 : List Nat := [3, 1, 4, 2, 9]
def baseStart_88362 : Nat := 118140960795 + 88362 * 2 ^ 59
def prefixEnd_88362 : Nat := 4983230072969 + 3 ^ 40 * 88362 * 2
def baseEnd_88362 : Nat := 995822827823067587789

theorem tailTrace_88362 : CollatzResearch.WordTrace tailWord_88362 prefixEnd_88362 995822827823067587789 := by
  unfold tailWord_88362
  simp only [CollatzResearch.WordTrace]
  refine ⟨805706726471759968312835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2148551270591359915500893 805706726471759968312835)
  ·
    refine ⟨1208560089707639952469253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 805706726471759968312835 1208560089707639952469253)
    ·
      refine ⟨226605016820182491087985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1208560089707639952469253 226605016820182491087985)
      ·
        refine ⟨169953762615136868315989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226605016820182491087985 169953762615136868315989)
        ·
          refine ⟨995822827823067587789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 169953762615136868315989 995822827823067587789)
          ·
            rfl

theorem cell19_88362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 9].length) (baseStart_88362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88362 prefixEnd_88362 := by exact prefixLift 88362
  have htrace : WordTrace (prefixWord ++ tailWord_88362) baseStart_88362 baseEnd_88362 := by
    simpa [prefixWord, tailWord_88362, baseEnd_88362] using wordTrace_append hprefix tailTrace_88362
  have hstable : (prefixWord ++ tailWord_88362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88362).length < 2 ^ (prefixWord ++ tailWord_88362).sum := by decide
  have hdescent : baseEnd_88362 < baseStart_88362 := by decide
  rcases family_descends (prefixWord ++ tailWord_88362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88457 : List Nat := [1, 2, 1, 1, 6, 2, 1, 5]
def baseStart_88457 : Nat := 118140960795 + 88457 * 2 ^ 59
def prefixEnd_88457 : Nat := 4983230072969 + 3 ^ 40 * 88457 * 2
def baseEnd_88457 : Nat := 26916123410290752758933

theorem tailTrace_88457 : CollatzResearch.WordTrace tailWord_88457 prefixEnd_88457 26916123410290752758933 := by
  unfold tailWord_88457
  simp only [CollatzResearch.WordTrace]
  refine ⟨3226291840542871097959625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2150861227028580731973083 3226291840542871097959625)
  ·
    refine ⟨2419718880407153323469719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3226291840542871097959625 2419718880407153323469719)
    ·
      refine ⟨3629578320610729985204579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2419718880407153323469719 3629578320610729985204579)
      ·
        refine ⟨5444367480916094977806869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3629578320610729985204579 5444367480916094977806869)
        ·
          refine ⟨255204725667941952084697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5444367480916094977806869 255204725667941952084697)
          ·
            refine ⟨191403544250956464063523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255204725667941952084697 191403544250956464063523)
            ·
              refine ⟨287105316376434696095285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191403544250956464063523 287105316376434696095285)
              ·
                refine ⟨26916123410290752758933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 287105316376434696095285 26916123410290752758933)
                ·
                  rfl

theorem cell19_88457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_88457 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88457 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88457 prefixEnd_88457 := by exact prefixLift 88457
  have htrace : WordTrace (prefixWord ++ tailWord_88457) baseStart_88457 baseEnd_88457 := by
    simpa [prefixWord, tailWord_88457, baseEnd_88457] using wordTrace_append hprefix tailTrace_88457
  have hstable : (prefixWord ++ tailWord_88457).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88457).length < 2 ^ (prefixWord ++ tailWord_88457).sum := by decide
  have hdescent : baseEnd_88457 < baseStart_88457 := by decide
  rcases family_descends (prefixWord ++ tailWord_88457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88546 : List Nat := [3, 3, 3, 2, 1, 2, 1, 4]
def baseStart_88546 : Nat := 118140960795 + 88546 * 2 ^ 59
def prefixEnd_88546 : Nat := 4983230072969 + 3 ^ 40 * 88546 * 2
def baseEnd_88546 : Nat := 26943204760364916780913

theorem tailTrace_88546 : CollatzResearch.WordTrace tailWord_88546 prefixEnd_88546 26943204760364916780913 := by
  unfold tailWord_88546
  simp only [CollatzResearch.WordTrace]
  refine ⟨807384484305109824487373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2153025291480292865299661 807384484305109824487373)
  ·
    refine ⟨302769181614416184182765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 807384484305109824487373 302769181614416184182765)
    ·
      refine ⟨113538443105406069068537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302769181614416184182765 113538443105406069068537)
      ·
        refine ⟨85153832329054551801403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113538443105406069068537 85153832329054551801403)
        ·
          refine ⟨127730748493581827702105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85153832329054551801403 127730748493581827702105)
          ·
            refine ⟨95798061370186370776579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127730748493581827702105 95798061370186370776579)
            ·
              refine ⟨143697092055279556164869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95798061370186370776579 143697092055279556164869)
              ·
                refine ⟨26943204760364916780913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143697092055279556164869 26943204760364916780913)
                ·
                  rfl

theorem cell19_88546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_88546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88546 prefixEnd_88546 := by exact prefixLift 88546
  have htrace : WordTrace (prefixWord ++ tailWord_88546) baseStart_88546 baseEnd_88546 := by
    simpa [prefixWord, tailWord_88546, baseEnd_88546] using wordTrace_append hprefix tailTrace_88546
  have hstable : (prefixWord ++ tailWord_88546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88546).length < 2 ^ (prefixWord ++ tailWord_88546).sum := by decide
  have hdescent : baseEnd_88546 < baseStart_88546 := by decide
  rcases family_descends (prefixWord ++ tailWord_88546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88552 : List Nat := [2, 1, 4, 1, 1, 3, 3, 4]
def baseStart_88552 : Nat := 118140960795 + 88552 * 2 ^ 59
def prefixEnd_88552 : Nat := 4983230072969 + 3 ^ 40 * 88552 * 2
def baseEnd_88552 : Nat := 26945030469358680647563

theorem tailTrace_88552 : CollatzResearch.WordTrace tailWord_88552 prefixEnd_88552 26945030469358680647563 := by
  unfold tailWord_88552
  simp only [CollatzResearch.WordTrace]
  refine ⟨1614878387599351161333955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2153171183465801548445273 1614878387599351161333955)
  ·
    refine ⟨2422317581399026742000933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1614878387599351161333955 2422317581399026742000933)
    ·
      refine ⟨454184546512317514125175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2422317581399026742000933 454184546512317514125175)
      ·
        refine ⟨681276819768476271187763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454184546512317514125175 681276819768476271187763)
        ·
          refine ⟨1021915229652714406781645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681276819768476271187763 1021915229652714406781645)
          ·
            refine ⟨383218211119767902543117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1021915229652714406781645 383218211119767902543117)
            ·
              refine ⟨143706829169912963453669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 383218211119767902543117 143706829169912963453669)
              ·
                refine ⟨26945030469358680647563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143706829169912963453669 26945030469358680647563)
                ·
                  rfl

theorem cell19_88552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_88552 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88552 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88552 prefixEnd_88552 := by exact prefixLift 88552
  have htrace : WordTrace (prefixWord ++ tailWord_88552) baseStart_88552 baseEnd_88552 := by
    simpa [prefixWord, tailWord_88552, baseEnd_88552] using wordTrace_append hprefix tailTrace_88552
  have hstable : (prefixWord ++ tailWord_88552).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88552).length < 2 ^ (prefixWord ++ tailWord_88552).sum := by decide
  have hdescent : baseEnd_88552 < baseStart_88552 := by decide
  rcases family_descends (prefixWord ++ tailWord_88552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88590 : List Nat := [4, 1, 1, 2, 3, 2, 6]
def baseStart_88590 : Nat := 118140960795 + 88590 * 2 ^ 59
def prefixEnd_88590 : Nat := 4983230072969 + 3 ^ 40 * 88590 * 2
def baseEnd_88590 : Nat := 8985531097661950601005

theorem tailTrace_88590 : CollatzResearch.WordTrace tailWord_88590 prefixEnd_88590 8985531097661950601005 := by
  unfold tailWord_88590
  simp only [CollatzResearch.WordTrace]
  refine ⟨403892843632629351568903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2154095166040689875034149 403892843632629351568903)
  ·
    refine ⟨605839265448944027353355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 403892843632629351568903 605839265448944027353355)
    ·
      refine ⟨908758898173416041030033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 605839265448944027353355 908758898173416041030033)
      ·
        refine ⟨681569173630062030772525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 908758898173416041030033 681569173630062030772525)
        ·
          refine ⟨255588440111273261539697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 681569173630062030772525 255588440111273261539697)
          ·
            refine ⟨191691330083454946154773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255588440111273261539697 191691330083454946154773)
            ·
              refine ⟨8985531097661950601005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 191691330083454946154773 8985531097661950601005)
              ·
                rfl

theorem cell19_88590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 6].length) (baseStart_88590 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88590 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88590 prefixEnd_88590 := by exact prefixLift 88590
  have htrace : WordTrace (prefixWord ++ tailWord_88590) baseStart_88590 baseEnd_88590 := by
    simpa [prefixWord, tailWord_88590, baseEnd_88590] using wordTrace_append hprefix tailTrace_88590
  have hstable : (prefixWord ++ tailWord_88590).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88590).length < 2 ^ (prefixWord ++ tailWord_88590).sum := by decide
  have hdescent : baseEnd_88590 < baseStart_88590 := by decide
  rcases family_descends (prefixWord ++ tailWord_88590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88622 : List Nat := [4, 1, 3, 1, 4, 1, 2, 3]
def baseStart_88622 : Nat := 118140960795 + 88622 * 2 ^ 59
def prefixEnd_88622 : Nat := 4983230072969 + 3 ^ 40 * 88622 * 2
def baseEnd_88622 : Nat := 26966330407619259091817

theorem tailTrace_88622 : CollatzResearch.WordTrace tailWord_88622 prefixEnd_88622 26966330407619259091817 := by
  unfold tailWord_88622
  simp only [CollatzResearch.WordTrace]
  refine ⟨404038735618138034714515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2154873256630069518477413 404038735618138034714515)
  ·
    refine ⟨606058103427207052071773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 404038735618138034714515 606058103427207052071773)
    ·
      refine ⟨227271788785202644526915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 606058103427207052071773 227271788785202644526915)
      ·
        refine ⟨340907683177803966790373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227271788785202644526915 340907683177803966790373)
        ·
          refine ⟨63920190595838243773195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 340907683177803966790373 63920190595838243773195)
          ·
            refine ⟨95880285893757365659793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63920190595838243773195 95880285893757365659793)
            ·
              refine ⟨71910214420318024244845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95880285893757365659793 71910214420318024244845)
              ·
                refine ⟨26966330407619259091817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71910214420318024244845 26966330407619259091817)
                ·
                  rfl

theorem cell19_88622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_88622 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88622 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88622 prefixEnd_88622 := by exact prefixLift 88622
  have htrace : WordTrace (prefixWord ++ tailWord_88622) baseStart_88622 baseEnd_88622 := by
    simpa [prefixWord, tailWord_88622, baseEnd_88622] using wordTrace_append hprefix tailTrace_88622
  have hstable : (prefixWord ++ tailWord_88622).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88622).length < 2 ^ (prefixWord ++ tailWord_88622).sum := by decide
  have hdescent : baseEnd_88622 < baseStart_88622 := by decide
  rcases family_descends (prefixWord ++ tailWord_88622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88647 : List Nat := [1, 1, 4, 1, 4, 3, 5]
def baseStart_88647 : Nat := 118140960795 + 88647 * 2 ^ 59
def prefixEnd_88647 : Nat := 4983230072969 + 3 ^ 40 * 88647 * 2
def baseEnd_88647 : Nat := 8991312509475536178731

theorem tailTrace_88647 : CollatzResearch.WordTrace tailWord_88647 prefixEnd_88647 8991312509475536178731 := by
  unfold tailWord_88647
  simp only [CollatzResearch.WordTrace]
  refine ⟨3233221709854533547376195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2155481139903022364917463 3233221709854533547376195)
  ·
    refine ⟨4849832564781800321064293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3233221709854533547376195 4849832564781800321064293)
    ·
      refine ⟨909343605896587560199555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4849832564781800321064293 909343605896587560199555)
      ·
        refine ⟨1364015408844881340299333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 909343605896587560199555 1364015408844881340299333)
        ·
          refine ⟨255752889158415251306125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1364015408844881340299333 255752889158415251306125)
          ·
            refine ⟨95907333434405719239797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255752889158415251306125 95907333434405719239797)
            ·
              refine ⟨8991312509475536178731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95907333434405719239797 8991312509475536178731)
              ·
                rfl

theorem cell19_88647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 5].length) (baseStart_88647 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88647 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88647 prefixEnd_88647 := by exact prefixLift 88647
  have htrace : WordTrace (prefixWord ++ tailWord_88647) baseStart_88647 baseEnd_88647 := by
    simpa [prefixWord, tailWord_88647, baseEnd_88647] using wordTrace_append hprefix tailTrace_88647
  have hstable : (prefixWord ++ tailWord_88647).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88647).length < 2 ^ (prefixWord ++ tailWord_88647).sum := by decide
  have hdescent : baseEnd_88647 < baseStart_88647 := by decide
  rcases family_descends (prefixWord ++ tailWord_88647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88685 : List Nat := [1, 5, 1, 1, 3, 1, 2, 5]
def baseStart_88685 : Nat := 118140960795 + 88685 * 2 ^ 59
def prefixEnd_88685 : Nat := 4983230072969 + 3 ^ 40 * 88685 * 2
def baseEnd_88685 : Nat := 26985500352053779691645

theorem tailTrace_88685 : CollatzResearch.WordTrace tailWord_88685 prefixEnd_88685 26985500352053779691645 := by
  unfold tailWord_88685
  simp only [CollatzResearch.WordTrace]
  refine ⟨3234607683716866037259509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2156405122477910691506339 3234607683716866037259509)
  ·
    refine ⟨303244470348456190993079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3234607683716866037259509 303244470348456190993079)
    ·
      refine ⟨454866705522684286489619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303244470348456190993079 454866705522684286489619)
      ·
        refine ⟨682300058284026429734429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454866705522684286489619 682300058284026429734429)
        ·
          refine ⟨255862521856509911150411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 682300058284026429734429 255862521856509911150411)
          ·
            refine ⟨383793782784764866725617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255862521856509911150411 383793782784764866725617)
            ·
              refine ⟨287845337088573650044213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383793782784764866725617 287845337088573650044213)
              ·
                refine ⟨26985500352053779691645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 287845337088573650044213 26985500352053779691645)
                ·
                  rfl

theorem cell19_88685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_88685 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88685 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88685 prefixEnd_88685 := by exact prefixLift 88685
  have htrace : WordTrace (prefixWord ++ tailWord_88685) baseStart_88685 baseEnd_88685 := by
    simpa [prefixWord, tailWord_88685, baseEnd_88685] using wordTrace_append hprefix tailTrace_88685
  have hstable : (prefixWord ++ tailWord_88685).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88685).length < 2 ^ (prefixWord ++ tailWord_88685).sum := by decide
  have hdescent : baseEnd_88685 < baseStart_88685 := by decide
  rcases family_descends (prefixWord ++ tailWord_88685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88687 : List Nat := [1, 1, 2, 1, 3, 2, 4, 5]
def baseStart_88687 : Nat := 118140960795 + 88687 * 2 ^ 59
def prefixEnd_88687 : Nat := 4983230072969 + 3 ^ 40 * 88687 * 2
def baseEnd_88687 : Nat := 26986108921718367647195

theorem tailTrace_88687 : CollatzResearch.WordTrace tailWord_88687 prefixEnd_88687 26986108921718367647195 := by
  unfold tailWord_88687
  simp only [CollatzResearch.WordTrace]
  refine ⟨3234680629709620378832315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2156453753139746919221543 3234680629709620378832315)
  ·
    refine ⟨4852020944564430568248473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3234680629709620378832315 4852020944564430568248473)
    ·
      refine ⟨3639015708423322926186355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4852020944564430568248473 3639015708423322926186355)
      ·
        refine ⟨5458523562634984389279533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3639015708423322926186355 5458523562634984389279533)
        ·
          refine ⟨2046946335988119145979825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5458523562634984389279533 2046946335988119145979825)
          ·
            refine ⟨1535209751991089359484869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2046946335988119145979825 1535209751991089359484869)
            ·
              refine ⟨287851828498329254903413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1535209751991089359484869 287851828498329254903413)
              ·
                refine ⟨26986108921718367647195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 287851828498329254903413 26986108921718367647195)
                ·
                  rfl

theorem cell19_88687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_88687 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88687 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88687 prefixEnd_88687 := by exact prefixLift 88687
  have htrace : WordTrace (prefixWord ++ tailWord_88687) baseStart_88687 baseEnd_88687 := by
    simpa [prefixWord, tailWord_88687, baseEnd_88687] using wordTrace_append hprefix tailTrace_88687
  have hstable : (prefixWord ++ tailWord_88687).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88687).length < 2 ^ (prefixWord ++ tailWord_88687).sum := by decide
  have hdescent : baseEnd_88687 < baseStart_88687 := by decide
  rcases family_descends (prefixWord ++ tailWord_88687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88799 : List Nat := [1, 1, 2, 3, 2, 3, 4, 3]
def baseStart_88799 : Nat := 118140960795 + 88799 * 2 ^ 59
def prefixEnd_88799 : Nat := 4983230072969 + 3 ^ 40 * 88799 * 2
def baseEnd_88799 : Nat := 27020188822935293158001

theorem tailTrace_88799 : CollatzResearch.WordTrace tailWord_88799 prefixEnd_88799 27020188822935293158001 := by
  unfold tailWord_88799
  simp only [CollatzResearch.WordTrace]
  refine ⟨3238765605303863506909451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2159177070202575671272967 3238765605303863506909451)
  ·
    refine ⟨4858148407955795260364177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3238765605303863506909451 4858148407955795260364177)
    ·
      refine ⟨3643611305966846445273133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4858148407955795260364177 3643611305966846445273133)
      ·
        refine ⟨1366354239737567416977425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3643611305966846445273133 1366354239737567416977425)
        ·
          refine ⟨1024765679803175562733069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1366354239737567416977425 1024765679803175562733069)
          ·
            refine ⟨384287129926190836024901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1024765679803175562733069 384287129926190836024901)
            ·
              refine ⟨72053836861160781754669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 384287129926190836024901 72053836861160781754669)
              ·
                refine ⟨27020188822935293158001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72053836861160781754669 27020188822935293158001)
                ·
                  rfl

theorem cell19_88799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 3].length) (baseStart_88799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88799 prefixEnd_88799 := by exact prefixLift 88799
  have htrace : WordTrace (prefixWord ++ tailWord_88799) baseStart_88799 baseEnd_88799 := by
    simpa [prefixWord, tailWord_88799, baseEnd_88799] using wordTrace_append hprefix tailTrace_88799
  have hstable : (prefixWord ++ tailWord_88799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88799).length < 2 ^ (prefixWord ++ tailWord_88799).sum := by decide
  have hdescent : baseEnd_88799 < baseStart_88799 := by decide
  rcases family_descends (prefixWord ++ tailWord_88799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88818 : List Nat := [3, 2, 1, 3, 1, 4, 5]
def baseStart_88818 : Nat := 118140960795 + 88818 * 2 ^ 59
def prefixEnd_88818 : Nat := 4983230072969 + 3 ^ 40 * 88818 * 2
def baseEnd_88818 : Nat := 9008656744916292911909

theorem tailTrace_88818 : CollatzResearch.WordTrace tailWord_88818 prefixEnd_88818 9008656744916292911909 := by
  unfold tailWord_88818
  simp only [CollatzResearch.WordTrace]
  refine ⟨809864648058757437962777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2159639061490019834567405 809864648058757437962777)
  ·
    refine ⟨607398486044068078472083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 809864648058757437962777 607398486044068078472083)
    ·
      refine ⟨911097729066102117708125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 607398486044068078472083 911097729066102117708125)
      ·
        refine ⟨341661648399788294140547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 911097729066102117708125 341661648399788294140547)
        ·
          refine ⟨512492472599682441210821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341661648399788294140547 512492472599682441210821)
          ·
            refine ⟨96092338612440457727029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 512492472599682441210821 96092338612440457727029)
            ·
              refine ⟨9008656744916292911909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96092338612440457727029 9008656744916292911909)
              ·
                rfl

theorem cell19_88818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 5].length) (baseStart_88818 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88818 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88818 prefixEnd_88818 := by exact prefixLift 88818
  have htrace : WordTrace (prefixWord ++ tailWord_88818) baseStart_88818 baseEnd_88818 := by
    simpa [prefixWord, tailWord_88818, baseEnd_88818] using wordTrace_append hprefix tailTrace_88818
  have hstable : (prefixWord ++ tailWord_88818).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88818).length < 2 ^ (prefixWord ++ tailWord_88818).sum := by decide
  have hdescent : baseEnd_88818 < baseStart_88818 := by decide
  rcases family_descends (prefixWord ++ tailWord_88818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88858 : List Nat := [3, 1, 1, 3, 2, 1, 1, 7]
def baseStart_88858 : Nat := 118140960795 + 88858 * 2 ^ 59
def prefixEnd_88858 : Nat := 4983230072969 + 3 ^ 40 * 88858 * 2
def baseEnd_88858 : Nat := 27038141628040637846729

theorem tailTrace_88858 : CollatzResearch.WordTrace tailWord_88858 prefixEnd_88858 27038141628040637846729 := by
  unfold tailWord_88858
  simp only [CollatzResearch.WordTrace]
  refine ⟨810229378022529145826807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2160611674726744388871485 810229378022529145826807)
  ·
    refine ⟨1215344067033793718740211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 810229378022529145826807 1215344067033793718740211)
    ·
      refine ⟨1823016100550690578110317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1215344067033793718740211 1823016100550690578110317)
      ·
        refine ⟨683631037706508966791369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1823016100550690578110317 683631037706508966791369)
        ·
          refine ⟨512723278279881725093527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683631037706508966791369 512723278279881725093527)
          ·
            refine ⟨769084917419822587640291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512723278279881725093527 769084917419822587640291)
            ·
              refine ⟨1153627376129733881460437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769084917419822587640291 1153627376129733881460437)
              ·
                refine ⟨27038141628040637846729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1153627376129733881460437 27038141628040637846729)
                ·
                  rfl

theorem cell19_88858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_88858 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88858 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88858 prefixEnd_88858 := by exact prefixLift 88858
  have htrace : WordTrace (prefixWord ++ tailWord_88858) baseStart_88858 baseEnd_88858 := by
    simpa [prefixWord, tailWord_88858, baseEnd_88858] using wordTrace_append hprefix tailTrace_88858
  have hstable : (prefixWord ++ tailWord_88858).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88858).length < 2 ^ (prefixWord ++ tailWord_88858).sum := by decide
  have hdescent : baseEnd_88858 < baseStart_88858 := by decide
  rcases family_descends (prefixWord ++ tailWord_88858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88909 : List Nat := [1, 6, 1, 2, 2, 1, 3, 3]
def baseStart_88909 : Nat := 118140960795 + 88909 * 2 ^ 59
def prefixEnd_88909 : Nat := 4983230072969 + 3 ^ 40 * 88909 * 2
def baseEnd_88909 : Nat := 27053660154487630713257

theorem tailTrace_88909 : CollatzResearch.WordTrace tailWord_88909 prefixEnd_88909 27053660154487630713257 := by
  unfold tailWord_88909
  simp only [CollatzResearch.WordTrace]
  refine ⟨3242777634905352293413781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2161851756603568195609187 3242777634905352293413781)
  ·
    refine ⟨152005201636188388753771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3242777634905352293413781 152005201636188388753771)
    ·
      refine ⟨228007802454282583130657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152005201636188388753771 228007802454282583130657)
      ·
        refine ⟨171005851840711937347993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228007802454282583130657 171005851840711937347993)
        ·
          refine ⟨128254388880533953010995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171005851840711937347993 128254388880533953010995)
          ·
            refine ⟨192381583320800929516493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128254388880533953010995 192381583320800929516493)
            ·
              refine ⟨72143093745300348568685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192381583320800929516493 72143093745300348568685)
              ·
                refine ⟨27053660154487630713257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72143093745300348568685 27053660154487630713257)
                ·
                  rfl

theorem cell19_88909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 3].length) (baseStart_88909 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88909 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88909 prefixEnd_88909 := by exact prefixLift 88909
  have htrace : WordTrace (prefixWord ++ tailWord_88909) baseStart_88909 baseEnd_88909 := by
    simpa [prefixWord, tailWord_88909, baseEnd_88909] using wordTrace_append hprefix tailTrace_88909
  have hstable : (prefixWord ++ tailWord_88909).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88909).length < 2 ^ (prefixWord ++ tailWord_88909).sum := by decide
  have hdescent : baseEnd_88909 < baseStart_88909 := by decide
  rcases family_descends (prefixWord ++ tailWord_88909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88962 : List Nat := [3, 4, 2, 2, 2, 1, 2, 3]
def baseStart_88962 : Nat := 118140960795 + 88962 * 2 ^ 59
def prefixEnd_88962 : Nat := 4983230072969 + 3 ^ 40 * 88962 * 2
def baseEnd_88962 : Nat := 27069787250599211535335

theorem tailTrace_88962 : CollatzResearch.WordTrace tailWord_88962 prefixEnd_88962 27069787250599211535335 := by
  unfold tailWord_88962
  simp only [CollatzResearch.WordTrace]
  refine ⟨811177675928335586273285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2163140469142228230062093 811177675928335586273285)
  ·
    refine ⟨152095814236562922426241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 811177675928335586273285 152095814236562922426241)
    ·
      refine ⟨114071860677422191819681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152095814236562922426241 114071860677422191819681)
      ·
        refine ⟨85553895508066643864761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114071860677422191819681 85553895508066643864761)
        ·
          refine ⟨64165421631049982898571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85553895508066643864761 64165421631049982898571)
          ·
            refine ⟨96248132446574974347857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64165421631049982898571 96248132446574974347857)
            ·
              refine ⟨72186099334931230760893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96248132446574974347857 72186099334931230760893)
              ·
                refine ⟨27069787250599211535335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72186099334931230760893 27069787250599211535335)
                ·
                  rfl

theorem cell19_88962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_88962 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88962 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88962 prefixEnd_88962 := by exact prefixLift 88962
  have htrace : WordTrace (prefixWord ++ tailWord_88962) baseStart_88962 baseEnd_88962 := by
    simpa [prefixWord, tailWord_88962, baseEnd_88962] using wordTrace_append hprefix tailTrace_88962
  have hstable : (prefixWord ++ tailWord_88962).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88962).length < 2 ^ (prefixWord ++ tailWord_88962).sum := by decide
  have hdescent : baseEnd_88962 < baseStart_88962 := by decide
  rcases family_descends (prefixWord ++ tailWord_88962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88968 : List Nat := [2, 1, 3, 3, 2, 3, 2, 3]
def baseStart_88968 : Nat := 118140960795 + 88968 * 2 ^ 59
def prefixEnd_88968 : Nat := 4983230072969 + 3 ^ 40 * 88968 * 2
def baseEnd_88968 : Nat := 27071612959592975401985

theorem tailTrace_88968 : CollatzResearch.WordTrace tailWord_88968 prefixEnd_88968 27071612959592975401985 := by
  unfold tailWord_88968
  simp only [CollatzResearch.WordTrace]
  refine ⟨1622464770845802684905779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2163286361127736913207705 1622464770845802684905779)
  ·
    refine ⟨2433697156268704027358669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1622464770845802684905779 2433697156268704027358669)
    ·
      refine ⟨912636433600764010259501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2433697156268704027358669 912636433600764010259501)
      ·
        refine ⟨342238662600286503847313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 912636433600764010259501 342238662600286503847313)
        ·
          refine ⟨256678996950214877885485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342238662600286503847313 256678996950214877885485)
          ·
            refine ⟨96254623856330579207057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256678996950214877885485 96254623856330579207057)
            ·
              refine ⟨72190967892247934405293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96254623856330579207057 72190967892247934405293)
              ·
                refine ⟨27071612959592975401985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72190967892247934405293 27071612959592975401985)
                ·
                  rfl

theorem cell19_88968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_88968 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88968 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88968 prefixEnd_88968 := by exact prefixLift 88968
  have htrace : WordTrace (prefixWord ++ tailWord_88968) baseStart_88968 baseEnd_88968 := by
    simpa [prefixWord, tailWord_88968, baseEnd_88968] using wordTrace_append hprefix tailTrace_88968
  have hstable : (prefixWord ++ tailWord_88968).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88968).length < 2 ^ (prefixWord ++ tailWord_88968).sum := by decide
  have hdescent : baseEnd_88968 < baseStart_88968 := by decide
  rcases family_descends (prefixWord ++ tailWord_88968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88970 : List Nat := [3, 1, 2, 4, 1, 2, 1, 5]
def baseStart_88970 : Nat := 118140960795 + 88970 * 2 ^ 59
def prefixEnd_88970 : Nat := 4983230072969 + 3 ^ 40 * 88970 * 2
def baseEnd_88970 : Nat := 27072221529257563357535

theorem tailTrace_88970 : CollatzResearch.WordTrace tailWord_88970 prefixEnd_88970 27072221529257563357535 := by
  unfold tailWord_88970
  simp only [CollatzResearch.WordTrace]
  refine ⟨811250621921089927846091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2163334991789573140922909 811250621921089927846091)
  ·
    refine ⟨1216875932881634891769137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 811250621921089927846091 1216875932881634891769137)
    ·
      refine ⟨912656949661226168826853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1216875932881634891769137 912656949661226168826853)
      ·
        refine ⟨171123178061479906655035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 912656949661226168826853 171123178061479906655035)
        ·
          refine ⟨256684767092219859982553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171123178061479906655035 256684767092219859982553)
          ·
            refine ⟨192513575319164894986915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256684767092219859982553 192513575319164894986915)
            ·
              refine ⟨288770362978747342480373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192513575319164894986915 288770362978747342480373)
              ·
                refine ⟨27072221529257563357535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 288770362978747342480373 27072221529257563357535)
                ·
                  rfl

theorem cell19_88970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_88970 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88970 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88970 prefixEnd_88970 := by exact prefixLift 88970
  have htrace : WordTrace (prefixWord ++ tailWord_88970) baseStart_88970 baseEnd_88970 := by
    simpa [prefixWord, tailWord_88970, baseEnd_88970] using wordTrace_append hprefix tailTrace_88970
  have hstable : (prefixWord ++ tailWord_88970).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88970).length < 2 ^ (prefixWord ++ tailWord_88970).sum := by decide
  have hdescent : baseEnd_88970 < baseStart_88970 := by decide
  rcases family_descends (prefixWord ++ tailWord_88970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88991 : List Nat := [1, 1, 2, 5, 2, 1, 7]
def baseStart_88991 : Nat := 118140960795 + 88991 * 2 ^ 59
def prefixEnd_88991 : Nat := 4983230072969 + 3 ^ 40 * 88991 * 2
def baseEnd_88991 : Nat := 9026203836911912296937

theorem tailTrace_88991 : CollatzResearch.WordTrace tailWord_88991 prefixEnd_88991 9026203836911912296937 := by
  unfold tailWord_88991
  simp only [CollatzResearch.WordTrace]
  refine ⟨3245768420608280297898827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2163845613738853531932551 3245768420608280297898827)
  ·
    refine ⟨4868652630912420446848241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3245768420608280297898827 4868652630912420446848241)
    ·
      refine ⟨3651489473184315335136181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4868652630912420446848241 3651489473184315335136181)
      ·
        refine ⟨342327138111029562669017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3651489473184315335136181 342327138111029562669017)
        ·
          refine ⟨256745353583272172001763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342327138111029562669017 256745353583272172001763)
          ·
            refine ⟨385118030374908258002645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256745353583272172001763 385118030374908258002645)
            ·
              refine ⟨9026203836911912296937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 385118030374908258002645 9026203836911912296937)
              ·
                rfl

theorem cell19_88991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 7].length) (baseStart_88991 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_88991 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_88991 prefixEnd_88991 := by exact prefixLift 88991
  have htrace : WordTrace (prefixWord ++ tailWord_88991) baseStart_88991 baseEnd_88991 := by
    simpa [prefixWord, tailWord_88991, baseEnd_88991] using wordTrace_append hprefix tailTrace_88991
  have hstable : (prefixWord ++ tailWord_88991).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88991).length < 2 ^ (prefixWord ++ tailWord_88991).sum := by decide
  have hdescent : baseEnd_88991 < baseStart_88991 := by decide
  rcases family_descends (prefixWord ++ tailWord_88991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89046 : List Nat := [5, 2, 1, 1, 2, 8]
def baseStart_89046 : Nat := 118140960795 + 89046 * 2 ^ 59
def prefixEnd_89046 : Nat := 4983230072969 + 3 ^ 40 * 89046 * 2
def baseEnd_89046 : Nat := 3010594130723545074271

theorem tailTrace_89046 : CollatzResearch.WordTrace tailWord_89046 prefixEnd_89046 3010594130723545074271 := by
  unfold tailWord_89046
  simp only [CollatzResearch.WordTrace]
  refine ⟨202985902213064043196937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2165182956939349794100661 202985902213064043196937)
  ·
    refine ⟨152239426659798032397703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202985902213064043196937 152239426659798032397703)
    ·
      refine ⟨228359139989697048596555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152239426659798032397703 228359139989697048596555)
      ·
        refine ⟨342538709984545572894833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228359139989697048596555 342538709984545572894833)
        ·
          refine ⟨256904032488409179671125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342538709984545572894833 256904032488409179671125)
          ·
            refine ⟨3010594130723545074271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 256904032488409179671125 3010594130723545074271)
            ·
              rfl

theorem cell19_89046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 8].length) (baseStart_89046 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89046 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89046 prefixEnd_89046 := by exact prefixLift 89046
  have htrace : WordTrace (prefixWord ++ tailWord_89046) baseStart_89046 baseEnd_89046 := by
    simpa [prefixWord, tailWord_89046, baseEnd_89046] using wordTrace_append hprefix tailTrace_89046
  have hstable : (prefixWord ++ tailWord_89046).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89046).length < 2 ^ (prefixWord ++ tailWord_89046).sum := by decide
  have hdescent : baseEnd_89046 < baseStart_89046 := by decide
  rcases family_descends (prefixWord ++ tailWord_89046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89061 : List Nat := [1, 3, 1, 6, 2, 1, 1, 4]
def baseStart_89061 : Nat := 118140960795 + 89061 * 2 ^ 59
def prefixEnd_89061 : Nat := 4983230072969 + 3 ^ 40 * 89061 * 2
def baseEnd_89061 : Nat := 27099911448996315335065

theorem tailTrace_89061 : CollatzResearch.WordTrace tailWord_89061 prefixEnd_89061 27099911448996315335065 := by
  unfold tailWord_89061
  simp only [CollatzResearch.WordTrace]
  refine ⟨3248321530354682252947037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2165547686903121501964691 3248321530354682252947037)
  ·
    refine ⟨1218120573883005844855139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3248321530354682252947037 1218120573883005844855139)
    ·
      refine ⟨1827180860824508767282709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1218120573883005844855139 1827180860824508767282709)
      ·
        refine ⟨85649102851148848466377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1827180860824508767282709 85649102851148848466377)
        ·
          refine ⟨64236827138361636349783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85649102851148848466377 64236827138361636349783)
          ·
            refine ⟨96355240707542454524675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64236827138361636349783 96355240707542454524675)
            ·
              refine ⟨144532861061313681787013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96355240707542454524675 144532861061313681787013)
              ·
                refine ⟨27099911448996315335065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144532861061313681787013 27099911448996315335065)
                ·
                  rfl

theorem cell19_89061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 4].length) (baseStart_89061 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89061 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89061 prefixEnd_89061 := by exact prefixLift 89061
  have htrace : WordTrace (prefixWord ++ tailWord_89061) baseStart_89061 baseEnd_89061 := by
    simpa [prefixWord, tailWord_89061, baseEnd_89061] using wordTrace_append hprefix tailTrace_89061
  have hstable : (prefixWord ++ tailWord_89061).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89061).length < 2 ^ (prefixWord ++ tailWord_89061).sum := by decide
  have hdescent : baseEnd_89061 < baseStart_89061 := by decide
  rcases family_descends (prefixWord ++ tailWord_89061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89076 : List Nat := [2, 6, 2, 1, 1, 1, 3, 3]
def baseStart_89076 : Nat := 118140960795 + 89076 * 2 ^ 59
def prefixEnd_89076 : Nat := 4983230072969 + 3 ^ 40 * 89076 * 2
def baseEnd_89076 : Nat := 27104475721480725001691

theorem tailTrace_89076 : CollatzResearch.WordTrace tailWord_89076 prefixEnd_89076 27104475721480725001691 := by
  unfold tailWord_89076
  simp only [CollatzResearch.WordTrace]
  refine ⟨1624434312650169907371541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2165912416866893209828721 1624434312650169907371541)
  ·
    refine ⟨76145358405476714408041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1624434312650169907371541 76145358405476714408041)
    ·
      refine ⟨57109018804107535806031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76145358405476714408041 57109018804107535806031)
      ·
        refine ⟨85663528206161303709047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57109018804107535806031 85663528206161303709047)
        ·
          refine ⟨128495292309241955563571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85663528206161303709047 128495292309241955563571)
          ·
            refine ⟨192742938463862933345357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128495292309241955563571 192742938463862933345357)
            ·
              refine ⟨72278601923948600004509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192742938463862933345357 72278601923948600004509)
              ·
                refine ⟨27104475721480725001691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72278601923948600004509 27104475721480725001691)
                ·
                  rfl

theorem cell19_89076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_89076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89076 prefixEnd_89076 := by exact prefixLift 89076
  have htrace : WordTrace (prefixWord ++ tailWord_89076) baseStart_89076 baseEnd_89076 := by
    simpa [prefixWord, tailWord_89076, baseEnd_89076] using wordTrace_append hprefix tailTrace_89076
  have hstable : (prefixWord ++ tailWord_89076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89076).length < 2 ^ (prefixWord ++ tailWord_89076).sum := by decide
  have hdescent : baseEnd_89076 < baseStart_89076 := by decide
  rcases family_descends (prefixWord ++ tailWord_89076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89084 : List Nat := [2, 2, 2, 1, 2, 4, 3, 3]
def baseStart_89084 : Nat := 118140960795 + 89084 * 2 ^ 59
def prefixEnd_89084 : Nat := 4983230072969 + 3 ^ 40 * 89084 * 2
def baseEnd_89084 : Nat := 27106910000139076823891

theorem tailTrace_89084 : CollatzResearch.WordTrace tailWord_89084 prefixEnd_89084 27106910000139076823891 := by
  unfold tailWord_89084
  simp only [CollatzResearch.WordTrace]
  refine ⟨1624580204635678590517153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2166106939514238120689537 1624580204635678590517153)
  ·
    refine ⟨1218435153476758942887865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1624580204635678590517153 1218435153476758942887865)
    ·
      refine ⟨913826365107569207165899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1218435153476758942887865 913826365107569207165899)
      ·
        refine ⟨1370739547661353810748849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 913826365107569207165899 1370739547661353810748849)
        ·
          refine ⟨1028054660746015358061637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1370739547661353810748849 1028054660746015358061637)
          ·
            refine ⟨192760248889877879636557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1028054660746015358061637 192760248889877879636557)
            ·
              refine ⟨72285093333704204863709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192760248889877879636557 72285093333704204863709)
              ·
                refine ⟨27106910000139076823891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72285093333704204863709 27106910000139076823891)
                ·
                  rfl

theorem cell19_89084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_89084 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89084 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89084 prefixEnd_89084 := by exact prefixLift 89084
  have htrace : WordTrace (prefixWord ++ tailWord_89084) baseStart_89084 baseEnd_89084 := by
    simpa [prefixWord, tailWord_89084, baseEnd_89084] using wordTrace_append hprefix tailTrace_89084
  have hstable : (prefixWord ++ tailWord_89084).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89084).length < 2 ^ (prefixWord ++ tailWord_89084).sum := by decide
  have hdescent : baseEnd_89084 < baseStart_89084 := by decide
  rcases family_descends (prefixWord ++ tailWord_89084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89158 : List Nat := [6, 1, 1, 1, 1, 4, 5]
def baseStart_89158 : Nat := 118140960795 + 89158 * 2 ^ 59
def prefixEnd_89158 : Nat := 4983230072969 + 3 ^ 40 * 89158 * 2
def baseEnd_89158 : Nat := 9043142359242943726415

theorem tailTrace_89158 : CollatzResearch.WordTrace tailWord_89158 prefixEnd_89158 9043142359242943726415 := by
  unfold tailWord_89158
  simp only [CollatzResearch.WordTrace]
  refine ⟨101620606593852119350879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2167906274002178546152085 101620606593852119350879)
  ·
    refine ⟨152430909890778179026319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101620606593852119350879 152430909890778179026319)
    ·
      refine ⟨228646364836167268539479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152430909890778179026319 228646364836167268539479)
      ·
        refine ⟨342969547254250902809219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228646364836167268539479 342969547254250902809219)
        ·
          refine ⟨514454320881376354213829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342969547254250902809219 514454320881376354213829)
          ·
            refine ⟨96460185165258066415093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 514454320881376354213829 96460185165258066415093)
            ·
              refine ⟨9043142359242943726415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96460185165258066415093 9043142359242943726415)
              ·
                rfl

theorem cell19_89158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 5].length) (baseStart_89158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89158 prefixEnd_89158 := by exact prefixLift 89158
  have htrace : WordTrace (prefixWord ++ tailWord_89158) baseStart_89158 baseEnd_89158 := by
    simpa [prefixWord, tailWord_89158, baseEnd_89158] using wordTrace_append hprefix tailTrace_89158
  have hstable : (prefixWord ++ tailWord_89158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89158).length < 2 ^ (prefixWord ++ tailWord_89158).sum := by decide
  have hdescent : baseEnd_89158 < baseStart_89158 := by decide
  rcases family_descends (prefixWord ++ tailWord_89158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89221 : List Nat := [1, 3, 1, 1, 13]
def baseStart_89221 : Nat := 118140960795 + 89221 * 2 ^ 59
def prefixEnd_89221 : Nat := 4983230072969 + 3 ^ 40 * 89221 * 2
def baseEnd_89221 : Nat := 1005503593413457473299

theorem tailTrace_89221 : CollatzResearch.WordTrace tailWord_89221 prefixEnd_89221 1005503593413457473299 := by
  unfold tailWord_89221
  simp only [CollatzResearch.WordTrace]
  refine ⟨3254157209775029578771517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2169438139850019719181011 3254157209775029578771517)
  ·
    refine ⟨1220308953665636092039319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3254157209775029578771517 1220308953665636092039319)
    ·
      refine ⟨1830463430498454138058979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1220308953665636092039319 1830463430498454138058979)
      ·
        refine ⟨2745695145747681207088469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1830463430498454138058979 2745695145747681207088469)
        ·
          refine ⟨1005503593413457473299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 2745695145747681207088469 1005503593413457473299)
          ·
            rfl

theorem cell19_89221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 13].length) (baseStart_89221 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89221 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89221 prefixEnd_89221 := by exact prefixLift 89221
  have htrace : WordTrace (prefixWord ++ tailWord_89221) baseStart_89221 baseEnd_89221 := by
    simpa [prefixWord, tailWord_89221, baseEnd_89221] using wordTrace_append hprefix tailTrace_89221
  have hstable : (prefixWord ++ tailWord_89221).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89221).length < 2 ^ (prefixWord ++ tailWord_89221).sum := by decide
  have hdescent : baseEnd_89221 < baseStart_89221 := by decide
  rcases family_descends (prefixWord ++ tailWord_89221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89276 : List Nat := [2, 2, 2, 3, 2, 2, 6]
def baseStart_89276 : Nat := 118140960795 + 89276 * 2 ^ 59
def prefixEnd_89276 : Nat := 4983230072969 + 3 ^ 40 * 89276 * 2
def baseEnd_89276 : Nat := 9055110895979840185567

theorem tailTrace_89276 : CollatzResearch.WordTrace tailWord_89276 prefixEnd_89276 9055110895979840185567 := by
  unfold tailWord_89276
  simp only [CollatzResearch.WordTrace]
  refine ⟨1628081612287886986011841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2170775483050515981349121 1628081612287886986011841)
  ·
    refine ⟨1221061209215915239508881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1628081612287886986011841 1221061209215915239508881)
    ·
      refine ⟨915795906911936429631661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1221061209215915239508881 915795906911936429631661)
      ·
        refine ⟨343423465091976161111873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 915795906911936429631661 343423465091976161111873)
        ·
          refine ⟨257567598818982120833905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343423465091976161111873 257567598818982120833905)
          ·
            refine ⟨193175699114236590625429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257567598818982120833905 193175699114236590625429)
            ·
              refine ⟨9055110895979840185567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 193175699114236590625429 9055110895979840185567)
              ·
                rfl

theorem cell19_89276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 6].length) (baseStart_89276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89276 prefixEnd_89276 := by exact prefixLift 89276
  have htrace : WordTrace (prefixWord ++ tailWord_89276) baseStart_89276 baseEnd_89276 := by
    simpa [prefixWord, tailWord_89276, baseEnd_89276] using wordTrace_append hprefix tailTrace_89276
  have hstable : (prefixWord ++ tailWord_89276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89276).length < 2 ^ (prefixWord ++ tailWord_89276).sum := by decide
  have hdescent : baseEnd_89276 < baseStart_89276 := by decide
  rcases family_descends (prefixWord ++ tailWord_89276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89297 : List Nat := [1, 2, 2, 1, 2, 2, 1, 8]
def baseStart_89297 : Nat := 118140960795 + 89297 * 2 ^ 59
def prefixEnd_89297 : Nat := 4983230072969 + 3 ^ 40 * 89297 * 2
def baseEnd_89297 : Nat := 27171722669417694089977

theorem tailTrace_89297 : CollatzResearch.WordTrace tailWord_89297 prefixEnd_89297 27171722669417694089977 := by
  unfold tailWord_89297
  simp only [CollatzResearch.WordTrace]
  refine ⟨3256929157499694558538145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2171286104999796372358763 3256929157499694558538145)
  ·
    refine ⟨2442696868124770918903609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3256929157499694558538145 2442696868124770918903609)
    ·
      refine ⟨1832022651093578189177707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2442696868124770918903609 1832022651093578189177707)
      ·
        refine ⟨2748033976640367283766561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1832022651093578189177707 2748033976640367283766561)
        ·
          refine ⟨2061025482480275462824921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2748033976640367283766561 2061025482480275462824921)
          ·
            refine ⟨1545769111860206597118691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2061025482480275462824921 1545769111860206597118691)
            ·
              refine ⟨2318653667790309895678037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545769111860206597118691 2318653667790309895678037)
              ·
                refine ⟨27171722669417694089977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2318653667790309895678037 27171722669417694089977)
                ·
                  rfl

theorem cell19_89297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_89297 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89297 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89297 prefixEnd_89297 := by exact prefixLift 89297
  have htrace : WordTrace (prefixWord ++ tailWord_89297) baseStart_89297 baseEnd_89297 := by
    simpa [prefixWord, tailWord_89297, baseEnd_89297] using wordTrace_append hprefix tailTrace_89297
  have hstable : (prefixWord ++ tailWord_89297).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89297).length < 2 ^ (prefixWord ++ tailWord_89297).sum := by decide
  have hdescent : baseEnd_89297 < baseStart_89297 := by decide
  rcases family_descends (prefixWord ++ tailWord_89297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89312 : List Nat := [2, 1, 1, 3, 1, 6, 2, 3]
def baseStart_89312 : Nat := 118140960795 + 89312 * 2 ^ 59
def prefixEnd_89312 : Nat := 4983230072969 + 3 ^ 40 * 89312 * 2
def baseEnd_89312 : Nat := 27176286941902103756603

theorem tailTrace_89312 : CollatzResearch.WordTrace tailWord_89312 prefixEnd_89312 27176286941902103756603 := by
  unfold tailWord_89312
  simp only [CollatzResearch.WordTrace]
  refine ⟨1628738126222676060167095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2171650834963568080222793 1628738126222676060167095)
  ·
    refine ⟨2443107189334014090250643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1628738126222676060167095 2443107189334014090250643)
    ·
      refine ⟨3664660784001021135375965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2443107189334014090250643 3664660784001021135375965)
      ·
        refine ⟨1374247794000382925765987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3664660784001021135375965 1374247794000382925765987)
        ·
          refine ⟨2061371691000574388648981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1374247794000382925765987 2061371691000574388648981)
          ·
            refine ⟨96626798015651924467921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2061371691000574388648981 96626798015651924467921)
            ·
              refine ⟨72470098511738943350941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96626798015651924467921 72470098511738943350941)
              ·
                refine ⟨27176286941902103756603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72470098511738943350941 27176286941902103756603)
                ·
                  rfl

theorem cell19_89312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_89312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89312 prefixEnd_89312 := by exact prefixLift 89312
  have htrace : WordTrace (prefixWord ++ tailWord_89312) baseStart_89312 baseEnd_89312 := by
    simpa [prefixWord, tailWord_89312, baseEnd_89312] using wordTrace_append hprefix tailTrace_89312
  have hstable : (prefixWord ++ tailWord_89312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89312).length < 2 ^ (prefixWord ++ tailWord_89312).sum := by decide
  have hdescent : baseEnd_89312 < baseStart_89312 := by decide
  rcases family_descends (prefixWord ++ tailWord_89312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89405 : List Nat := [1, 4, 1, 5, 1, 2, 1, 4]
def baseStart_89405 : Nat := 118140960795 + 89405 * 2 ^ 59
def prefixEnd_89405 : Nat := 4983230072969 + 3 ^ 40 * 89405 * 2
def baseEnd_89405 : Nat := 27204585431305443689683

theorem tailTrace_89405 : CollatzResearch.WordTrace tailWord_89405 prefixEnd_89405 27204585431305443689683 := by
  unfold tailWord_89405
  simp only [CollatzResearch.WordTrace]
  refine ⟨3260868241108429003469669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2173912160738952668979779 3260868241108429003469669)
  ·
    refine ⟨611412795207830438150563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3260868241108429003469669 611412795207830438150563)
    ·
      refine ⟨917119192811745657225845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 611412795207830438150563 917119192811745657225845)
      ·
        refine ⟨85979924326101155364923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 917119192811745657225845 85979924326101155364923)
        ·
          refine ⟨128969886489151733047385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85979924326101155364923 128969886489151733047385)
          ·
            refine ⟨96727414866863799785539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128969886489151733047385 96727414866863799785539)
            ·
              refine ⟨145091122300295699678309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96727414866863799785539 145091122300295699678309)
              ·
                refine ⟨27204585431305443689683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145091122300295699678309 27204585431305443689683)
                ·
                  rfl

theorem cell19_89405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 4].length) (baseStart_89405 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89405 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89405 prefixEnd_89405 := by exact prefixLift 89405
  have htrace : WordTrace (prefixWord ++ tailWord_89405) baseStart_89405 baseEnd_89405 := by
    simpa [prefixWord, tailWord_89405, baseEnd_89405] using wordTrace_append hprefix tailTrace_89405
  have hstable : (prefixWord ++ tailWord_89405).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89405).length < 2 ^ (prefixWord ++ tailWord_89405).sum := by decide
  have hdescent : baseEnd_89405 < baseStart_89405 := by decide
  rcases family_descends (prefixWord ++ tailWord_89405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89447 : List Nat := [1, 1, 5, 1, 4, 1, 6]
def baseStart_89447 : Nat := 118140960795 + 89447 * 2 ^ 59
def prefixEnd_89447 : Nat := 4983230072969 + 3 ^ 40 * 89447 * 2
def baseEnd_89447 : Nat := 9072455131420596918745

theorem tailTrace_89447 : CollatzResearch.WordTrace tailWord_89447 prefixEnd_89447 9072455131420596918745 := by
  unfold tailWord_89447
  simp only [CollatzResearch.WordTrace]
  refine ⟨3262400106956270176498595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2174933404637513450999063 3262400106956270176498595)
  ·
    refine ⟨4893600160434405264747893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3262400106956270176498595 4893600160434405264747893)
    ·
      refine ⟨458775015040725493570115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4893600160434405264747893 458775015040725493570115)
      ·
        refine ⟨688162522561088240355173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458775015040725493570115 688162522561088240355173)
        ·
          refine ⟨129030472980204045066595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 688162522561088240355173 129030472980204045066595)
          ·
            refine ⟨193545709470306067599893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129030472980204045066595 193545709470306067599893)
            ·
              refine ⟨9072455131420596918745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 193545709470306067599893 9072455131420596918745)
              ·
                rfl

theorem cell19_89447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 6].length) (baseStart_89447 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89447 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89447 prefixEnd_89447 := by exact prefixLift 89447
  have htrace : WordTrace (prefixWord ++ tailWord_89447) baseStart_89447 baseEnd_89447 := by
    simpa [prefixWord, tailWord_89447, baseEnd_89447] using wordTrace_append hprefix tailTrace_89447
  have hstable : (prefixWord ++ tailWord_89447).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89447).length < 2 ^ (prefixWord ++ tailWord_89447).sum := by decide
  have hdescent : baseEnd_89447 < baseStart_89447 := by decide
  rcases family_descends (prefixWord ++ tailWord_89447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89468 : List Nat := [2, 2, 2, 1, 1, 1, 4, 6]
def baseStart_89468 : Nat := 118140960795 + 89468 * 2 ^ 59
def prefixEnd_89468 : Nat := 4983230072969 + 3 ^ 40 * 89468 * 2
def baseEnd_89468 : Nat := 27223755375739964289511

theorem tailTrace_89468 : CollatzResearch.WordTrace tailWord_89468 prefixEnd_89468 27223755375739964289511 := by
  unfold tailWord_89468
  simp only [CollatzResearch.WordTrace]
  refine ⟨1631583019940095381506529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2175444026586793842008705 1631583019940095381506529)
  ·
    refine ⟨1223687264955071536129897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1631583019940095381506529 1223687264955071536129897)
    ·
      refine ⟨917765448716303652097423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1223687264955071536129897 917765448716303652097423)
      ·
        refine ⟨1376648173074455478146135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 917765448716303652097423 1376648173074455478146135)
        ·
          refine ⟨2064972259611683217219203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1376648173074455478146135 2064972259611683217219203)
          ·
            refine ⟨3097458389417524825828805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064972259611683217219203 3097458389417524825828805)
            ·
              refine ⟨580773448015785904842901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3097458389417524825828805 580773448015785904842901)
              ·
                refine ⟨27223755375739964289511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 580773448015785904842901 27223755375739964289511)
                ·
                  rfl

theorem cell19_89468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_89468 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89468 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89468 prefixEnd_89468 := by exact prefixLift 89468
  have htrace : WordTrace (prefixWord ++ tailWord_89468) baseStart_89468 baseEnd_89468 := by
    simpa [prefixWord, tailWord_89468, baseEnd_89468] using wordTrace_append hprefix tailTrace_89468
  have hstable : (prefixWord ++ tailWord_89468).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89468).length < 2 ^ (prefixWord ++ tailWord_89468).sum := by decide
  have hdescent : baseEnd_89468 < baseStart_89468 := by decide
  rcases family_descends (prefixWord ++ tailWord_89468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89481 : List Nat := [1, 2, 1, 1, 8, 1, 2, 3]
def baseStart_89481 : Nat := 118140960795 + 89481 * 2 ^ 59
def prefixEnd_89481 : Nat := 4983230072969 + 3 ^ 40 * 89481 * 2
def baseEnd_89481 : Nat := 27227711078559786000587

theorem tailTrace_89481 : CollatzResearch.WordTrace tailWord_89481 prefixEnd_89481 27227711078559786000587 := by
  unfold tailWord_89481
  simp only [CollatzResearch.WordTrace]
  refine ⟨3263640188833093983236297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2175760125888729322157531 3263640188833093983236297)
  ·
    refine ⟨2447730141624820487427223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3263640188833093983236297 2447730141624820487427223)
    ·
      refine ⟨3671595212437230731140835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2447730141624820487427223 3671595212437230731140835)
      ·
        refine ⟨5507392818655846096711253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3671595212437230731140835 5507392818655846096711253)
        ·
          refine ⟨64539759593623196445835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 5507392818655846096711253 64539759593623196445835)
          ·
            refine ⟨96809639390434794668753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64539759593623196445835 96809639390434794668753)
            ·
              refine ⟨72607229542826096001565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96809639390434794668753 72607229542826096001565)
              ·
                refine ⟨27227711078559786000587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72607229542826096001565 27227711078559786000587)
                ·
                  rfl

theorem cell19_89481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 3].length) (baseStart_89481 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89481 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89481 prefixEnd_89481 := by exact prefixLift 89481
  have htrace : WordTrace (prefixWord ++ tailWord_89481) baseStart_89481 baseEnd_89481 := by
    simpa [prefixWord, tailWord_89481, baseEnd_89481] using wordTrace_append hprefix tailTrace_89481
  have hstable : (prefixWord ++ tailWord_89481).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89481).length < 2 ^ (prefixWord ++ tailWord_89481).sum := by decide
  have hdescent : baseEnd_89481 < baseStart_89481 := by decide
  rcases family_descends (prefixWord ++ tailWord_89481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89500 : List Nat := [2, 2, 3, 4, 2, 1, 5]
def baseStart_89500 : Nat := 118140960795 + 89500 * 2 ^ 59
def prefixEnd_89500 : Nat := 4983230072969 + 3 ^ 40 * 89500 * 2
def baseEnd_89500 : Nat := 9077830830124457192771

theorem tailTrace_89500 : CollatzResearch.WordTrace tailWord_89500 prefixEnd_89500 9077830830124457192771 := by
  unfold tailWord_89500
  simp only [CollatzResearch.WordTrace]
  refine ⟨1632166587882130114088977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2176222117176173485451969 1632166587882130114088977)
  ·
    refine ⟨1224124940911597585566733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1632166587882130114088977 1224124940911597585566733)
    ·
      refine ⟨459046852841849094587525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1224124940911597585566733 459046852841849094587525)
      ·
        refine ⟨86071284907846705235161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 459046852841849094587525 86071284907846705235161)
        ·
          refine ⟨64553463680885028926371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86071284907846705235161 64553463680885028926371)
          ·
            refine ⟨96830195521327543389557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64553463680885028926371 96830195521327543389557)
            ·
              refine ⟨9077830830124457192771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96830195521327543389557 9077830830124457192771)
              ·
                rfl

theorem cell19_89500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 5].length) (baseStart_89500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89500 prefixEnd_89500 := by exact prefixLift 89500
  have htrace : WordTrace (prefixWord ++ tailWord_89500) baseStart_89500 baseEnd_89500 := by
    simpa [prefixWord, tailWord_89500, baseEnd_89500] using wordTrace_append hprefix tailTrace_89500
  have hstable : (prefixWord ++ tailWord_89500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89500).length < 2 ^ (prefixWord ++ tailWord_89500).sum := by decide
  have hdescent : baseEnd_89500 < baseStart_89500 := by decide
  rcases family_descends (prefixWord ++ tailWord_89500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89544 : List Nat := [2, 1, 3, 1, 3, 1, 1, 7]
def baseStart_89544 : Nat := 118140960795 + 89544 * 2 ^ 59
def prefixEnd_89544 : Nat := 4983230072969 + 3 ^ 40 * 89544 * 2
def baseEnd_89544 : Nat := 27246881022994306600415

theorem tailTrace_89544 : CollatzResearch.WordTrace tailWord_89544 prefixEnd_89544 27246881022994306600415 := by
  unfold tailWord_89544
  simp only [CollatzResearch.WordTrace]
  refine ⟨1632968993802427871389843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2177291991736570495186457 1632968993802427871389843)
  ·
    refine ⟨2449453490703641807084765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1632968993802427871389843 2449453490703641807084765)
    ·
      refine ⟨918545059013865677656787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2449453490703641807084765 918545059013865677656787)
      ·
        refine ⟨1377817588520798516485181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 918545059013865677656787 1377817588520798516485181)
        ·
          refine ⟨516681595695299443681943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1377817588520798516485181 516681595695299443681943)
          ·
            refine ⟨775022393542949165522915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516681595695299443681943 775022393542949165522915)
            ·
              refine ⟨1162533590314423748284373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775022393542949165522915 1162533590314423748284373)
              ·
                refine ⟨27246881022994306600415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1162533590314423748284373 27246881022994306600415)
                ·
                  rfl

theorem cell19_89544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_89544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89544 prefixEnd_89544 := by exact prefixLift 89544
  have htrace : WordTrace (prefixWord ++ tailWord_89544) baseStart_89544 baseEnd_89544 := by
    simpa [prefixWord, tailWord_89544, baseEnd_89544] using wordTrace_append hprefix tailTrace_89544
  have hstable : (prefixWord ++ tailWord_89544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89544).length < 2 ^ (prefixWord ++ tailWord_89544).sum := by decide
  have hdescent : baseEnd_89544 < baseStart_89544 := by decide
  rcases family_descends (prefixWord ++ tailWord_89544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89578 : List Nat := [3, 1, 3, 1, 4, 2, 1, 4]
def baseStart_89578 : Nat := 118140960795 + 89578 * 2 ^ 59
def prefixEnd_89578 : Nat := 4983230072969 + 3 ^ 40 * 89578 * 2
def baseEnd_89578 : Nat := 27257226707292301844767

theorem tailTrace_89578 : CollatzResearch.WordTrace tailWord_89578 prefixEnd_89578 27257226707292301844767 := by
  unfold tailWord_89578
  simp only [CollatzResearch.WordTrace]
  refine ⟨816794517370419887379347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2178118712987786366344925 816794517370419887379347)
  ·
    refine ⟨1225191776055629831069021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 816794517370419887379347 1225191776055629831069021)
    ·
      refine ⟨459446916020861186650883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1225191776055629831069021 459446916020861186650883)
      ·
        refine ⟨689170374031291779976325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459446916020861186650883 689170374031291779976325)
        ·
          refine ⟨129219445130867208745561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 689170374031291779976325 129219445130867208745561)
          ·
            refine ⟨96914583848150406559171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129219445130867208745561 96914583848150406559171)
            ·
              refine ⟨145371875772225609838757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96914583848150406559171 145371875772225609838757)
              ·
                refine ⟨27257226707292301844767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145371875772225609838757 27257226707292301844767)
                ·
                  rfl

theorem cell19_89578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_89578 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89578 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89578 prefixEnd_89578 := by exact prefixLift 89578
  have htrace : WordTrace (prefixWord ++ tailWord_89578) baseStart_89578 baseEnd_89578 := by
    simpa [prefixWord, tailWord_89578, baseEnd_89578] using wordTrace_append hprefix tailTrace_89578
  have hstable : (prefixWord ++ tailWord_89578).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89578).length < 2 ^ (prefixWord ++ tailWord_89578).sum := by decide
  have hdescent : baseEnd_89578 < baseStart_89578 := by decide
  rcases family_descends (prefixWord ++ tailWord_89578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89654 : List Nat := [5, 1, 2, 1, 3, 1, 1, 5]
def baseStart_89654 : Nat := 118140960795 + 89654 * 2 ^ 59
def prefixEnd_89654 : Nat := 4983230072969 + 3 ^ 40 * 89654 * 2
def baseEnd_89654 : Nat := 27280352354546644155671

theorem tailTrace_89654 : CollatzResearch.WordTrace tailWord_89654 prefixEnd_89654 27280352354546644155671 := by
  unfold tailWord_89654
  simp only [CollatzResearch.WordTrace]
  refine ⟨204371876075396533080251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2179966678137563019522677 204371876075396533080251)
  ·
    refine ⟨306557814113094799620377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204371876075396533080251 306557814113094799620377)
    ·
      refine ⟨229918360584821099715283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306557814113094799620377 229918360584821099715283)
      ·
        refine ⟨344877540877231649572925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229918360584821099715283 344877540877231649572925)
        ·
          refine ⟨129329077828961868589847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344877540877231649572925 129329077828961868589847)
          ·
            refine ⟨193993616743442802884771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129329077828961868589847 193993616743442802884771)
            ·
              refine ⟨290990425115164204327157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193993616743442802884771 290990425115164204327157)
              ·
                refine ⟨27280352354546644155671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 290990425115164204327157 27280352354546644155671)
                ·
                  rfl

theorem cell19_89654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_89654 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89654 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89654 prefixEnd_89654 := by exact prefixLift 89654
  have htrace : WordTrace (prefixWord ++ tailWord_89654) baseStart_89654 baseEnd_89654 := by
    simpa [prefixWord, tailWord_89654, baseEnd_89654] using wordTrace_append hprefix tailTrace_89654
  have hstable : (prefixWord ++ tailWord_89654).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89654).length < 2 ^ (prefixWord ++ tailWord_89654).sum := by decide
  have hdescent : baseEnd_89654 < baseStart_89654 := by decide
  rcases family_descends (prefixWord ++ tailWord_89654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89656 : List Nat := [2, 1, 2, 1, 4, 2, 4, 3]
def baseStart_89656 : Nat := 118140960795 + 89656 * 2 ^ 59
def prefixEnd_89656 : Nat := 4983230072969 + 3 ^ 40 * 89656 * 2
def baseEnd_89656 : Nat := 27280960924211232111221

theorem tailTrace_89656 : CollatzResearch.WordTrace tailWord_89656 prefixEnd_89656 27280960924211232111221 := by
  unfold tailWord_89656
  simp only [CollatzResearch.WordTrace]
  refine ⟨1635011481599549435428411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2180015308799399247237881 1635011481599549435428411)
  ·
    refine ⟨2452517222399324153142617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1635011481599549435428411 2452517222399324153142617)
    ·
      refine ⟨1839387916799493114856963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2452517222399324153142617 1839387916799493114856963)
      ·
        refine ⟨2759081875199239672285445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1839387916799493114856963 2759081875199239672285445)
        ·
          refine ⟨517327851599857438553521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2759081875199239672285445 517327851599857438553521)
          ·
            refine ⟨387995888699893078915141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 517327851599857438553521 387995888699893078915141)
            ·
              refine ⟨72749229131229952296589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 387995888699893078915141 72749229131229952296589)
              ·
                refine ⟨27280960924211232111221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72749229131229952296589 27280960924211232111221)
                ·
                  rfl

theorem cell19_89656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_89656 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89656 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89656 prefixEnd_89656 := by exact prefixLift 89656
  have htrace : WordTrace (prefixWord ++ tailWord_89656) baseStart_89656 baseEnd_89656 := by
    simpa [prefixWord, tailWord_89656, baseEnd_89656] using wordTrace_append hprefix tailTrace_89656
  have hstable : (prefixWord ++ tailWord_89656).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89656).length < 2 ^ (prefixWord ++ tailWord_89656).sum := by decide
  have hdescent : baseEnd_89656 < baseStart_89656 := by decide
  rcases family_descends (prefixWord ++ tailWord_89656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89658 : List Nat := [3, 1, 1, 1, 3, 2, 3, 5]
def baseStart_89658 : Nat := 118140960795 + 89658 * 2 ^ 59
def prefixEnd_89658 : Nat := 4983230072969 + 3 ^ 40 * 89658 * 2
def baseEnd_89658 : Nat := 27281569493875820066771

theorem tailTrace_89658 : CollatzResearch.WordTrace tailWord_89658 prefixEnd_89658 27281569493875820066771 := by
  unfold tailWord_89658
  simp only [CollatzResearch.WordTrace]
  refine ⟨817523977297963303107407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2180063939461235474953085 817523977297963303107407)
  ·
    refine ⟨1226285965946944954661111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 817523977297963303107407 1226285965946944954661111)
    ·
      refine ⟨1839428948920417431991667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1226285965946944954661111 1839428948920417431991667)
      ·
        refine ⟨2759143423380626147987501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1839428948920417431991667 2759143423380626147987501)
        ·
          refine ⟨1034678783767734805495313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2759143423380626147987501 1034678783767734805495313)
          ·
            refine ⟨776009087825801104121485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1034678783767734805495313 776009087825801104121485)
            ·
              refine ⟨291003407934675414045557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 776009087825801104121485 291003407934675414045557)
              ·
                refine ⟨27281569493875820066771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 291003407934675414045557 27281569493875820066771)
                ·
                  rfl

theorem cell19_89658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_89658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89658 prefixEnd_89658 := by exact prefixLift 89658
  have htrace : WordTrace (prefixWord ++ tailWord_89658) baseStart_89658 baseEnd_89658 := by
    simpa [prefixWord, tailWord_89658, baseEnd_89658] using wordTrace_append hprefix tailTrace_89658
  have hstable : (prefixWord ++ tailWord_89658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89658).length < 2 ^ (prefixWord ++ tailWord_89658).sum := by decide
  have hdescent : baseEnd_89658 < baseStart_89658 := by decide
  rcases family_descends (prefixWord ++ tailWord_89658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89732 : List Nat := [2, 3, 2, 1, 5, 6]
def baseStart_89732 : Nat := 118140960795 + 89732 * 2 ^ 59
def prefixEnd_89732 : Nat := 4983230072969 + 3 ^ 40 * 89732 * 2
def baseEnd_89732 : Nat := 3033787396829508269125

theorem tailTrace_89732 : CollatzResearch.WordTrace tailWord_89732 prefixEnd_89732 3033787396829508269125 := by
  unfold tailWord_89732
  simp only [CollatzResearch.WordTrace]
  refine ⟨1636397455461881925311725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2181863273949175900415633 1636397455461881925311725)
  ·
    refine ⟨613649045798205721991897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1636397455461881925311725 613649045798205721991897)
    ·
      refine ⟨460236784348654291493923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 613649045798205721991897 460236784348654291493923)
      ·
        refine ⟨690355176522981437240885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460236784348654291493923 690355176522981437240885)
        ·
          refine ⟨64720797799029509741333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 690355176522981437240885 64720797799029509741333)
          ·
            refine ⟨3033787396829508269125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 64720797799029509741333 3033787396829508269125)
            ·
              rfl

theorem cell19_89732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 6].length) (baseStart_89732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89732 prefixEnd_89732 := by exact prefixLift 89732
  have htrace : WordTrace (prefixWord ++ tailWord_89732) baseStart_89732 baseEnd_89732 := by
    simpa [prefixWord, tailWord_89732, baseEnd_89732] using wordTrace_append hprefix tailTrace_89732
  have hstable : (prefixWord ++ tailWord_89732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89732).length < 2 ^ (prefixWord ++ tailWord_89732).sum := by decide
  have hdescent : baseEnd_89732 < baseStart_89732 := by decide
  rcases family_descends (prefixWord ++ tailWord_89732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89734 : List Nat := [6, 13]
def baseStart_89734 : Nat := 118140960795 + 89734 * 2 ^ 59
def prefixEnd_89734 : Nat := 4983230072969 + 3 ^ 40 * 89734 * 2
def baseEnd_89734 : Nat := 37455000193594187075

theorem tailTrace_89734 : CollatzResearch.WordTrace tailWord_89734 prefixEnd_89734 37455000193594187075 := by
  unfold tailWord_89734
  simp only [CollatzResearch.WordTrace]
  refine ⟨102277120528641193506133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2181911904611012128130837 102277120528641193506133)
  ·
    refine ⟨37455000193594187075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 13 102277120528641193506133 37455000193594187075)
    ·
      rfl

theorem cell19_89734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 13].length) (baseStart_89734 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89734 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89734 prefixEnd_89734 := by exact prefixLift 89734
  have htrace : WordTrace (prefixWord ++ tailWord_89734) baseStart_89734 baseEnd_89734 := by
    simpa [prefixWord, tailWord_89734, baseEnd_89734] using wordTrace_append hprefix tailTrace_89734
  have hstable : (prefixWord ++ tailWord_89734).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89734).length < 2 ^ (prefixWord ++ tailWord_89734).sum := by decide
  have hdescent : baseEnd_89734 < baseStart_89734 := by decide
  rcases family_descends (prefixWord ++ tailWord_89734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89751 : List Nat := [1, 1, 3, 3, 2, 4, 1, 4]
def baseStart_89751 : Nat := 118140960795 + 89751 * 2 ^ 59
def prefixEnd_89751 : Nat := 4983230072969 + 3 ^ 40 * 89751 * 2
def baseEnd_89751 : Nat := 27309867983279159999851

theorem tailTrace_89751 : CollatzResearch.WordTrace tailWord_89751 prefixEnd_89751 27309867983279159999851 := by
  unfold tailWord_89751
  simp only [CollatzResearch.WordTrace]
  refine ⟨3273487897854930095565107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2182325265236620063710071 3273487897854930095565107)
  ·
    refine ⟨4910231846782395143347661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3273487897854930095565107 4910231846782395143347661)
    ·
      refine ⟨1841336942543398178755373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4910231846782395143347661 1841336942543398178755373)
      ·
        refine ⟨690501353453774317033265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1841336942543398178755373 690501353453774317033265)
        ·
          refine ⟨517876015090330737774949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 690501353453774317033265 517876015090330737774949)
          ·
            refine ⟨97101752829437013332803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 517876015090330737774949 97101752829437013332803)
            ·
              refine ⟨145652629244155519999205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97101752829437013332803 145652629244155519999205)
              ·
                refine ⟨27309867983279159999851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145652629244155519999205 27309867983279159999851)
                ·
                  rfl

theorem cell19_89751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 4].length) (baseStart_89751 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89751 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89751 prefixEnd_89751 := by exact prefixLift 89751
  have htrace : WordTrace (prefixWord ++ tailWord_89751) baseStart_89751 baseEnd_89751 := by
    simpa [prefixWord, tailWord_89751, baseEnd_89751] using wordTrace_append hprefix tailTrace_89751
  have hstable : (prefixWord ++ tailWord_89751).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89751).length < 2 ^ (prefixWord ++ tailWord_89751).sum := by decide
  have hdescent : baseEnd_89751 < baseStart_89751 := by decide
  rcases family_descends (prefixWord ++ tailWord_89751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89821 : List Nat := [1, 4, 3, 3, 2, 1, 2, 3]
def baseStart_89821 : Nat := 118140960795 + 89821 * 2 ^ 59
def prefixEnd_89821 : Nat := 4983230072969 + 3 ^ 40 * 89821 * 2
def baseEnd_89821 : Nat := 27331167921539738444105

theorem tailTrace_89821 : CollatzResearch.WordTrace tailWord_89821 prefixEnd_89821 27331167921539738444105 := by
  unfold tailWord_89821
  simp only [CollatzResearch.WordTrace]
  refine ⟨3276041007601332050613317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2184027338400888033742211 3276041007601332050613317)
  ·
    refine ⟨614257688925249759489997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3276041007601332050613317 614257688925249759489997)
    ·
      refine ⟨230346633346968659808749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 614257688925249759489997 230346633346968659808749)
      ·
        refine ⟨86379987505113247428281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230346633346968659808749 86379987505113247428281)
        ·
          refine ⟨64784990628834935571211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86379987505113247428281 64784990628834935571211)
          ·
            refine ⟨97177485943252403356817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64784990628834935571211 97177485943252403356817)
            ·
              refine ⟨72883114457439302517613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97177485943252403356817 72883114457439302517613)
              ·
                refine ⟨27331167921539738444105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72883114457439302517613 27331167921539738444105)
                ·
                  rfl

theorem cell19_89821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 3].length) (baseStart_89821 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89821 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89821 prefixEnd_89821 := by exact prefixLift 89821
  have htrace : WordTrace (prefixWord ++ tailWord_89821) baseStart_89821 baseEnd_89821 := by
    simpa [prefixWord, tailWord_89821, baseEnd_89821] using wordTrace_append hprefix tailTrace_89821
  have hstable : (prefixWord ++ tailWord_89821).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89821).length < 2 ^ (prefixWord ++ tailWord_89821).sum := by decide
  have hdescent : baseEnd_89821 < baseStart_89821 := by decide
  rcases family_descends (prefixWord ++ tailWord_89821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89825 : List Nat := [1, 2, 3, 1, 5, 2, 2, 3]
def baseStart_89825 : Nat := 118140960795 + 89825 * 2 ^ 59
def prefixEnd_89825 : Nat := 4983230072969 + 3 ^ 40 * 89825 * 2
def baseEnd_89825 : Nat := 27332385060868914355205

theorem tailTrace_89825 : CollatzResearch.WordTrace tailWord_89825 prefixEnd_89825 27332385060868914355205 := by
  unfold tailWord_89825
  simp only [CollatzResearch.WordTrace]
  refine ⟨3276186899586840733758929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2184124599724560489172619 3276186899586840733758929)
  ·
    refine ⟨2457140174690130550319197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3276186899586840733758929 2457140174690130550319197)
    ·
      refine ⟨921427565508798956369699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2457140174690130550319197 921427565508798956369699)
      ·
        refine ⟨1382141348263198434554549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 921427565508798956369699 1382141348263198434554549)
        ·
          refine ⟨129575751399674853239489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1382141348263198434554549 129575751399674853239489)
          ·
            refine ⟨97181813549756139929617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129575751399674853239489 97181813549756139929617)
            ·
              refine ⟨72886360162317104947213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97181813549756139929617 72886360162317104947213)
              ·
                refine ⟨27332385060868914355205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72886360162317104947213 27332385060868914355205)
                ·
                  rfl

theorem cell19_89825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 3].length) (baseStart_89825 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89825 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89825 prefixEnd_89825 := by exact prefixLift 89825
  have htrace : WordTrace (prefixWord ++ tailWord_89825) baseStart_89825 baseEnd_89825 := by
    simpa [prefixWord, tailWord_89825, baseEnd_89825] using wordTrace_append hprefix tailTrace_89825
  have hstable : (prefixWord ++ tailWord_89825).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89825).length < 2 ^ (prefixWord ++ tailWord_89825).sum := by decide
  have hdescent : baseEnd_89825 < baseStart_89825 := by decide
  rcases family_descends (prefixWord ++ tailWord_89825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89827 : List Nat := [1, 1, 1, 7, 2, 1, 1, 5]
def baseStart_89827 : Nat := 118140960795 + 89827 * 2 ^ 59
def prefixEnd_89827 : Nat := 4983230072969 + 3 ^ 40 * 89827 * 2
def baseEnd_89827 : Nat := 27332993630533502310755

theorem tailTrace_89827 : CollatzResearch.WordTrace tailWord_89827 prefixEnd_89827 27332993630533502310755 := by
  unfold tailWord_89827
  simp only [CollatzResearch.WordTrace]
  refine ⟨3276259845579595075331735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2184173230386396716887823 3276259845579595075331735)
  ·
    refine ⟨4914389768369392612997603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3276259845579595075331735 4914389768369392612997603)
    ·
      refine ⟨7371584652554088919496405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4914389768369392612997603 7371584652554088919496405)
      ·
        refine ⟨172771515294236459050697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 7371584652554088919496405 172771515294236459050697)
        ·
          refine ⟨129578636470677344288023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172771515294236459050697 129578636470677344288023)
          ·
            refine ⟨194367954706016016432035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129578636470677344288023 194367954706016016432035)
            ·
              refine ⟨291551932059024024648053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194367954706016016432035 291551932059024024648053)
              ·
                refine ⟨27332993630533502310755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 291551932059024024648053 27332993630533502310755)
                ·
                  rfl

theorem cell19_89827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_89827 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89827 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89827 prefixEnd_89827 := by exact prefixLift 89827
  have htrace : WordTrace (prefixWord ++ tailWord_89827) baseStart_89827 baseEnd_89827 := by
    simpa [prefixWord, tailWord_89827, baseEnd_89827] using wordTrace_append hprefix tailTrace_89827
  have hstable : (prefixWord ++ tailWord_89827).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89827).length < 2 ^ (prefixWord ++ tailWord_89827).sum := by decide
  have hdescent : baseEnd_89827 < baseStart_89827 := by decide
  rcases family_descends (prefixWord ++ tailWord_89827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89829 : List Nat := [1, 3, 1, 4, 1, 1, 3, 5]
def baseStart_89829 : Nat := 118140960795 + 89829 * 2 ^ 59
def prefixEnd_89829 : Nat := 4983230072969 + 3 ^ 40 * 89829 * 2
def baseEnd_89829 : Nat := 27333602200198090266305

theorem tailTrace_89829 : CollatzResearch.WordTrace tailWord_89829 prefixEnd_89829 27333602200198090266305 := by
  unfold tailWord_89829
  simp only [CollatzResearch.WordTrace]
  refine ⟨3276332791572349416904541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2184221861048232944603027 3276332791572349416904541)
  ·
    refine ⟨1228624796839631031339203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3276332791572349416904541 1228624796839631031339203)
    ·
      refine ⟨1842937195259446547008805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1228624796839631031339203 1842937195259446547008805)
      ·
        refine ⟨345550724111146227564151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1842937195259446547008805 345550724111146227564151)
        ·
          refine ⟨518326086166719341346227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345550724111146227564151 518326086166719341346227)
          ·
            refine ⟨777489129250079012019341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518326086166719341346227 777489129250079012019341)
            ·
              refine ⟨291558423468779629507253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 777489129250079012019341 291558423468779629507253)
              ·
                refine ⟨27333602200198090266305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 291558423468779629507253 27333602200198090266305)
                ·
                  rfl

theorem cell19_89829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_89829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89829 prefixEnd_89829 := by exact prefixLift 89829
  have htrace : WordTrace (prefixWord ++ tailWord_89829) baseStart_89829 baseEnd_89829 := by
    simpa [prefixWord, tailWord_89829, baseEnd_89829] using wordTrace_append hprefix tailTrace_89829
  have hstable : (prefixWord ++ tailWord_89829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89829).length < 2 ^ (prefixWord ++ tailWord_89829).sum := by decide
  have hdescent : baseEnd_89829 < baseStart_89829 := by decide
  rcases family_descends (prefixWord ++ tailWord_89829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89844 : List Nat := [2, 6, 1, 1, 1, 1, 7]
def baseStart_89844 : Nat := 118140960795 + 89844 * 2 ^ 59
def prefixEnd_89844 : Nat := 4983230072969 + 3 ^ 40 * 89844 * 2
def baseEnd_89844 : Nat := 9112722157560833310977

theorem tailTrace_89844 : CollatzResearch.WordTrace tailWord_89844 prefixEnd_89844 9112722157560833310977 := by
  unfold tailWord_89844
  simp only [CollatzResearch.WordTrace]
  refine ⟨1638439943259003489350293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2184586591012004652467057 1638439943259003489350293)
  ·
    refine ⟨76801872340265788563295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1638439943259003489350293 76801872340265788563295)
    ·
      refine ⟨115202808510398682844943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76801872340265788563295 115202808510398682844943)
      ·
        refine ⟨172804212765598024267415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115202808510398682844943 172804212765598024267415)
        ·
          refine ⟨259206319148397036401123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172804212765598024267415 259206319148397036401123)
          ·
            refine ⟨388809478722595554601685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259206319148397036401123 388809478722595554601685)
            ·
              refine ⟨9112722157560833310977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 388809478722595554601685 9112722157560833310977)
              ·
                rfl

theorem cell19_89844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 7].length) (baseStart_89844 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89844 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89844 prefixEnd_89844 := by exact prefixLift 89844
  have htrace : WordTrace (prefixWord ++ tailWord_89844) baseStart_89844 baseEnd_89844 := by
    simpa [prefixWord, tailWord_89844, baseEnd_89844] using wordTrace_append hprefix tailTrace_89844
  have hstable : (prefixWord ++ tailWord_89844).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89844).length < 2 ^ (prefixWord ++ tailWord_89844).sum := by decide
  have hdescent : baseEnd_89844 < baseStart_89844 := by decide
  rcases family_descends (prefixWord ++ tailWord_89844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89846 : List Nat := [5, 1, 1, 1, 1, 5, 5]
def baseStart_89846 : Nat := 118140960795 + 89846 * 2 ^ 59
def prefixEnd_89846 : Nat := 4983230072969 + 3 ^ 40 * 89846 * 2
def baseEnd_89846 : Nat := 9112925014115695962827

theorem tailTrace_89846 : CollatzResearch.WordTrace tailWord_89846 prefixEnd_89846 9112925014115695962827 := by
  unfold tailWord_89846
  simp only [CollatzResearch.WordTrace]
  refine ⟨204809552031922582517087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2184635221673840880182261 204809552031922582517087)
  ·
    refine ⟨307214328047883873775631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204809552031922582517087 307214328047883873775631)
    ·
      refine ⟨460821492071825810663447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307214328047883873775631 460821492071825810663447)
      ·
        refine ⟨691232238107738715995171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460821492071825810663447 691232238107738715995171)
        ·
          refine ⟨1036848357161608073992757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691232238107738715995171 1036848357161608073992757)
          ·
            refine ⟨97204533483900756936821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1036848357161608073992757 97204533483900756936821)
            ·
              refine ⟨9112925014115695962827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97204533483900756936821 9112925014115695962827)
              ·
                rfl

theorem cell19_89846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 5].length) (baseStart_89846 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89846 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89846 prefixEnd_89846 := by exact prefixLift 89846
  have htrace : WordTrace (prefixWord ++ tailWord_89846) baseStart_89846 baseEnd_89846 := by
    simpa [prefixWord, tailWord_89846, baseEnd_89846] using wordTrace_append hprefix tailTrace_89846
  have hstable : (prefixWord ++ tailWord_89846).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89846).length < 2 ^ (prefixWord ++ tailWord_89846).sum := by decide
  have hdescent : baseEnd_89846 < baseStart_89846 := by decide
  rcases family_descends (prefixWord ++ tailWord_89846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89907 : List Nat := [1, 1, 1, 2, 14]
def baseStart_89907 : Nat := 118140960795 + 89907 * 2 ^ 59
def prefixEnd_89907 : Nat := 4983230072969 + 3 ^ 40 * 89907 * 2
def baseEnd_89907 : Nat := 1013234682115445204917

theorem tailTrace_89907 : CollatzResearch.WordTrace tailWord_89907 prefixEnd_89907 1013234682115445204917 := by
  unfold tailWord_89907
  simp only [CollatzResearch.WordTrace]
  refine ⟨3279177685289768738243975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2186118456859845825495983 3279177685289768738243975)
  ·
    refine ⟨4918766527934653107365963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3279177685289768738243975 4918766527934653107365963)
    ·
      refine ⟨7378149791901979661048945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4918766527934653107365963 7378149791901979661048945)
      ·
        refine ⟨5533612343926484745786709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7378149791901979661048945 5533612343926484745786709)
        ·
          refine ⟨1013234682115445204917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 5533612343926484745786709 1013234682115445204917)
          ·
            rfl

theorem cell19_89907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 14].length) (baseStart_89907 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89907 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89907 prefixEnd_89907 := by exact prefixLift 89907
  have htrace : WordTrace (prefixWord ++ tailWord_89907) baseStart_89907 baseEnd_89907 := by
    simpa [prefixWord, tailWord_89907, baseEnd_89907] using wordTrace_append hprefix tailTrace_89907
  have hstable : (prefixWord ++ tailWord_89907).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89907).length < 2 ^ (prefixWord ++ tailWord_89907).sum := by decide
  have hdescent : baseEnd_89907 < baseStart_89907 := by decide
  rcases family_descends (prefixWord ++ tailWord_89907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89941 : List Nat := [1, 3, 2, 2, 2, 3, 3, 3]
def baseStart_89941 : Nat := 118140960795 + 89941 * 2 ^ 59
def prefixEnd_89941 : Nat := 4983230072969 + 3 ^ 40 * 89941 * 2
def baseEnd_89941 : Nat := 27367682101415015777111

theorem tailTrace_89941 : CollatzResearch.WordTrace tailWord_89941 prefixEnd_89941 27367682101415015777111 := by
  unfold tailWord_89941
  simp only [CollatzResearch.WordTrace]
  refine ⟨3280417767166592544981677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2186945178111061696654451 3280417767166592544981677)
  ·
    refine ⟨1230156662687472204368129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3280417767166592544981677 1230156662687472204368129)
    ·
      refine ⟨922617497015604153276097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1230156662687472204368129 922617497015604153276097)
      ·
        refine ⟨691963122761703114957073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 922617497015604153276097 691963122761703114957073)
        ·
          refine ⟨518972342071277336217805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 691963122761703114957073 518972342071277336217805)
          ·
            refine ⟨194614628276729001081677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 518972342071277336217805 194614628276729001081677)
            ·
              refine ⟨72980485603773375405629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194614628276729001081677 72980485603773375405629)
              ·
                refine ⟨27367682101415015777111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72980485603773375405629 27367682101415015777111)
                ·
                  rfl

theorem cell19_89941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 3].length) (baseStart_89941 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89941 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89941 prefixEnd_89941 := by exact prefixLift 89941
  have htrace : WordTrace (prefixWord ++ tailWord_89941) baseStart_89941 baseEnd_89941 := by
    simpa [prefixWord, tailWord_89941, baseEnd_89941] using wordTrace_append hprefix tailTrace_89941
  have hstable : (prefixWord ++ tailWord_89941).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89941).length < 2 ^ (prefixWord ++ tailWord_89941).sum := by decide
  have hdescent : baseEnd_89941 < baseStart_89941 := by decide
  rcases family_descends (prefixWord ++ tailWord_89941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89983 : List Nat := [1, 1, 2, 2, 1, 1, 3, 8]
def baseStart_89983 : Nat := 118140960795 + 89983 * 2 ^ 59
def prefixEnd_89983 : Nat := 4983230072969 + 3 ^ 40 * 89983 * 2
def baseEnd_89983 : Nat := 27380462064371362843663

theorem tailTrace_89983 : CollatzResearch.WordTrace tailWord_89983 prefixEnd_89983 27380462064371362843663 := by
  unfold tailWord_89983
  simp only [CollatzResearch.WordTrace]
  refine ⟨3281949633014433718010603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2187966422009622478673735 3281949633014433718010603)
  ·
    refine ⟨4922924449521650577015905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3281949633014433718010603 4922924449521650577015905)
    ·
      refine ⟨3692193337141237932761929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4922924449521650577015905 3692193337141237932761929)
      ·
        refine ⟨2769145002855928449571447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3692193337141237932761929 2769145002855928449571447)
        ·
          refine ⟨4153717504283892674357171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2769145002855928449571447 4153717504283892674357171)
          ·
            refine ⟨6230576256425839011535757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4153717504283892674357171 6230576256425839011535757)
            ·
              refine ⟨2336466096159689629325909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6230576256425839011535757 2336466096159689629325909)
              ·
                refine ⟨27380462064371362843663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2336466096159689629325909 27380462064371362843663)
                ·
                  rfl

theorem cell19_89983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_89983 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89983 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89983 prefixEnd_89983 := by exact prefixLift 89983
  have htrace : WordTrace (prefixWord ++ tailWord_89983) baseStart_89983 baseEnd_89983 := by
    simpa [prefixWord, tailWord_89983, baseEnd_89983] using wordTrace_append hprefix tailTrace_89983
  have hstable : (prefixWord ++ tailWord_89983).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89983).length < 2 ^ (prefixWord ++ tailWord_89983).sum := by decide
  have hdescent : baseEnd_89983 < baseStart_89983 := by decide
  rcases family_descends (prefixWord ++ tailWord_89983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89994 : List Nat := [3, 1, 2, 4, 3, 1, 2, 3]
def baseStart_89994 : Nat := 118140960795 + 89994 * 2 ^ 59
def prefixEnd_89994 : Nat := 4983230072969 + 3 ^ 40 * 89994 * 2
def baseEnd_89994 : Nat := 27383809197526596599189

theorem tailTrace_89994 : CollatzResearch.WordTrace tailWord_89994 prefixEnd_89994 27383809197526596599189 := by
  unfold tailWord_89994
  simp only [CollatzResearch.WordTrace]
  refine ⟨820587708993645649165259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2188233890649721731107357 820587708993645649165259)
  ·
    refine ⟨1230881563490468473747889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 820587708993645649165259 1230881563490468473747889)
    ·
      refine ⟨923161172617851355310917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1230881563490468473747889 923161172617851355310917)
      ·
        refine ⟨173092719865847129120797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 923161172617851355310917 173092719865847129120797)
        ·
          refine ⟨64909769949692673420299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173092719865847129120797 64909769949692673420299)
          ·
            refine ⟨97364654924539010130449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64909769949692673420299 97364654924539010130449)
            ·
              refine ⟨73023491193404257597837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97364654924539010130449 73023491193404257597837)
              ·
                refine ⟨27383809197526596599189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73023491193404257597837 27383809197526596599189)
                ·
                  rfl

theorem cell19_89994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_89994 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_89994 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_89994 prefixEnd_89994 := by exact prefixLift 89994
  have htrace : WordTrace (prefixWord ++ tailWord_89994) baseStart_89994 baseEnd_89994 := by
    simpa [prefixWord, tailWord_89994, baseEnd_89994] using wordTrace_append hprefix tailTrace_89994
  have hstable : (prefixWord ++ tailWord_89994).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89994).length < 2 ^ (prefixWord ++ tailWord_89994).sum := by decide
  have hdescent : baseEnd_89994 < baseStart_89994 := by decide
  rcases family_descends (prefixWord ++ tailWord_89994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90017 : List Nat := [1, 2, 3, 4, 2, 2, 5]
def baseStart_90017 : Nat := 118140960795 + 90017 * 2 ^ 59
def prefixEnd_90017 : Nat := 4983230072969 + 3 ^ 40 * 90017 * 2
def baseEnd_90017 : Nat := 9130269249556452696005

theorem tailTrace_90017 : CollatzResearch.WordTrace tailWord_90017 prefixEnd_90017 9130269249556452696005 := by
  unfold tailWord_90017
  simp only [CollatzResearch.WordTrace]
  refine ⟨3283189714891257524748305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2188793143260838349832203 3283189714891257524748305)
  ·
    refine ⟨2462392286168443143561229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3283189714891257524748305 2462392286168443143561229)
    ·
      refine ⟨923397107313166178835461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2462392286168443143561229 923397107313166178835461)
      ·
        refine ⟨173136957621218658531649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 923397107313166178835461 173136957621218658531649)
        ·
          refine ⟨129852718215913993898737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173136957621218658531649 129852718215913993898737)
          ·
            refine ⟨97389538661935495424053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129852718215913993898737 97389538661935495424053)
            ·
              refine ⟨9130269249556452696005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97389538661935495424053 9130269249556452696005)
              ·
                rfl

theorem cell19_90017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 5].length) (baseStart_90017 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90017 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90017 prefixEnd_90017 := by exact prefixLift 90017
  have htrace : WordTrace (prefixWord ++ tailWord_90017) baseStart_90017 baseEnd_90017 := by
    simpa [prefixWord, tailWord_90017, baseEnd_90017] using wordTrace_append hprefix tailTrace_90017
  have hstable : (prefixWord ++ tailWord_90017).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90017).length < 2 ^ (prefixWord ++ tailWord_90017).sum := by decide
  have hdescent : baseEnd_90017 < baseStart_90017 := by decide
  rcases family_descends (prefixWord ++ tailWord_90017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90059 : List Nat := [1, 1, 1, 1, 3, 4, 1, 7]
def baseStart_90059 : Nat := 118140960795 + 90059 * 2 ^ 59
def prefixEnd_90059 : Nat := 4983230072969 + 3 ^ 40 * 90059 * 2
def baseEnd_90059 : Nat := 27403587711625705154567

theorem tailTrace_90059 : CollatzResearch.WordTrace tailWord_90059 prefixEnd_90059 27403587711625705154567 := by
  unfold tailWord_90059
  simp only [CollatzResearch.WordTrace]
  refine ⟨3284721580739098697777231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2189814387159399131851487 3284721580739098697777231)
  ·
    refine ⟨4927082371108648046665847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3284721580739098697777231 4927082371108648046665847)
    ·
      refine ⟨7390623556662972069998771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4927082371108648046665847 7390623556662972069998771)
      ·
        refine ⟨11085935334994458104998157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7390623556662972069998771 11085935334994458104998157)
        ·
          refine ⟨4157225750622921789374309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11085935334994458104998157 4157225750622921789374309)
          ·
            refine ⟨779479828241797835507683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4157225750622921789374309 779479828241797835507683)
            ·
              refine ⟨1169219742362696753261525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779479828241797835507683 1169219742362696753261525)
              ·
                refine ⟨27403587711625705154567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1169219742362696753261525 27403587711625705154567)
                ·
                  rfl

theorem cell19_90059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_90059 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90059 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90059 prefixEnd_90059 := by exact prefixLift 90059
  have htrace : WordTrace (prefixWord ++ tailWord_90059) baseStart_90059 baseEnd_90059 := by
    simpa [prefixWord, tailWord_90059, baseEnd_90059] using wordTrace_append hprefix tailTrace_90059
  have hstable : (prefixWord ++ tailWord_90059).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90059).length < 2 ^ (prefixWord ++ tailWord_90059).sum := by decide
  have hdescent : baseEnd_90059 < baseStart_90059 := by decide
  rcases family_descends (prefixWord ++ tailWord_90059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90110 : List Nat := [4, 2, 2, 2, 1, 2, 3, 3]
def baseStart_90110 : Nat := 118140960795 + 90110 * 2 ^ 59
def prefixEnd_90110 : Nat := 4983230072969 + 3 ^ 40 * 90110 * 2
def baseEnd_90110 : Nat := 27419106238072698021095

theorem tailTrace_90110 : CollatzResearch.WordTrace tailWord_90110 prefixEnd_90110 27419106238072698021095 := by
  unfold tailWord_90110
  simp only [CollatzResearch.WordTrace]
  refine ⟨410822712944291800985473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2191054469036222938589189 410822712944291800985473)
  ·
    refine ⟨308117034708218850739105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 410822712944291800985473 308117034708218850739105)
    ·
      refine ⟨231087776031164138054329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308117034708218850739105 231087776031164138054329)
      ·
        refine ⟨173315832023373103540747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231087776031164138054329 173315832023373103540747)
        ·
          refine ⟨259973748035059655311121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173315832023373103540747 259973748035059655311121)
          ·
            refine ⟨194980311026294741483341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259973748035059655311121 194980311026294741483341)
            ·
              refine ⟨73117616634860528056253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194980311026294741483341 73117616634860528056253)
              ·
                refine ⟨27419106238072698021095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73117616634860528056253 27419106238072698021095)
                ·
                  rfl

theorem cell19_90110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_90110 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90110 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90110 prefixEnd_90110 := by exact prefixLift 90110
  have htrace : WordTrace (prefixWord ++ tailWord_90110) baseStart_90110 baseEnd_90110 := by
    simpa [prefixWord, tailWord_90110, baseEnd_90110] using wordTrace_append hprefix tailTrace_90110
  have hstable : (prefixWord ++ tailWord_90110).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90110).length < 2 ^ (prefixWord ++ tailWord_90110).sum := by decide
  have hdescent : baseEnd_90110 < baseStart_90110 := by decide
  rcases family_descends (prefixWord ++ tailWord_90110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90133 : List Nat := [1, 3, 2, 1, 5, 1, 6]
def baseStart_90133 : Nat := 118140960795 + 90133 * 2 ^ 59
def prefixEnd_90133 : Nat := 4983230072969 + 3 ^ 40 * 90133 * 2
def baseEnd_90133 : Nat := 9142034929738486503307

theorem tailTrace_90133 : CollatzResearch.WordTrace tailWord_90133 prefixEnd_90133 9142034929738486503307 := by
  unfold tailWord_90133
  simp only [CollatzResearch.WordTrace]
  refine ⟨3287420582471009335971053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2191613721647339557314035 3287420582471009335971053)
  ·
    refine ⟨1232782718426628500989145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3287420582471009335971053 1232782718426628500989145)
    ·
      refine ⟨924587038819971375741859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1232782718426628500989145 924587038819971375741859)
      ·
        refine ⟨1386880558229957063612789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 924587038819971375741859 1386880558229957063612789)
        ·
          refine ⟨130020052334058474713699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1386880558229957063612789 130020052334058474713699)
          ·
            refine ⟨195030078501087712070549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130020052334058474713699 195030078501087712070549)
            ·
              refine ⟨9142034929738486503307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 195030078501087712070549 9142034929738486503307)
              ·
                rfl

theorem cell19_90133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 6].length) (baseStart_90133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90133 prefixEnd_90133 := by exact prefixLift 90133
  have htrace : WordTrace (prefixWord ++ tailWord_90133) baseStart_90133 baseEnd_90133 := by
    simpa [prefixWord, tailWord_90133, baseEnd_90133] using wordTrace_append hprefix tailTrace_90133
  have hstable : (prefixWord ++ tailWord_90133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90133).length < 2 ^ (prefixWord ++ tailWord_90133).sum := by decide
  have hdescent : baseEnd_90133 < baseStart_90133 := by decide
  rcases family_descends (prefixWord ++ tailWord_90133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90190 : List Nat := [4, 1, 1, 1, 1, 6, 5]
def baseStart_90190 : Nat := 118140960795 + 90190 * 2 ^ 59
def prefixEnd_90190 : Nat := 4983230072969 + 3 ^ 40 * 90190 * 2
def baseEnd_90190 : Nat := 9147816341552072081033

theorem tailTrace_90190 : CollatzResearch.WordTrace tailWord_90190 prefixEnd_90190 9147816341552072081033 := by
  unfold tailWord_90190
  simp only [CollatzResearch.WordTrace]
  refine ⟨411187442908063508849503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2192999695509672047197349 411187442908063508849503)
  ·
    refine ⟨616781164362095263274255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 411187442908063508849503 616781164362095263274255)
    ·
      refine ⟨925171746543142894911383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 616781164362095263274255 925171746543142894911383)
      ·
        refine ⟨1387757619814714342367075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 925171746543142894911383 1387757619814714342367075)
        ·
          refine ⟨2081636429722071513550613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1387757619814714342367075 2081636429722071513550613)
          ·
            refine ⟨97576707643222102197685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2081636429722071513550613 97576707643222102197685)
            ·
              refine ⟨9147816341552072081033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97576707643222102197685 9147816341552072081033)
              ·
                rfl

theorem cell19_90190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 5].length) (baseStart_90190 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90190 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90190 prefixEnd_90190 := by exact prefixLift 90190
  have htrace : WordTrace (prefixWord ++ tailWord_90190) baseStart_90190 baseEnd_90190 := by
    simpa [prefixWord, tailWord_90190, baseEnd_90190] using wordTrace_append hprefix tailTrace_90190
  have hstable : (prefixWord ++ tailWord_90190).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90190).length < 2 ^ (prefixWord ++ tailWord_90190).sum := by decide
  have hdescent : baseEnd_90190 < baseStart_90190 := by decide
  rcases family_descends (prefixWord ++ tailWord_90190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90211 : List Nat := [1, 1, 1, 5, 1, 1, 3, 6]
def baseStart_90211 : Nat := 118140960795 + 90211 * 2 ^ 59
def prefixEnd_90211 : Nat := 4983230072969 + 3 ^ 40 * 90211 * 2
def baseEnd_90211 : Nat := 27449839006134389776375

theorem tailTrace_90211 : CollatzResearch.WordTrace tailWord_90211 prefixEnd_90211 27449839006134389776375 := by
  unfold tailWord_90211
  simp only [CollatzResearch.WordTrace]
  refine ⟨3290265476188428657310487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2193510317458952438206991 3290265476188428657310487)
  ·
    refine ⟨4935398214282642985965731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3290265476188428657310487 4935398214282642985965731)
    ·
      refine ⟨7403097321423964478948597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4935398214282642985965731 7403097321423964478948597)
      ·
        refine ⟨694040373883496669901431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7403097321423964478948597 694040373883496669901431)
        ·
          refine ⟨1041060560825245004852147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694040373883496669901431 1041060560825245004852147)
          ·
            refine ⟨1561590841237867507278221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041060560825245004852147 1561590841237867507278221)
            ·
              refine ⟨585596565464200315229333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1561590841237867507278221 585596565464200315229333)
              ·
                refine ⟨27449839006134389776375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 585596565464200315229333 27449839006134389776375)
                ·
                  rfl

theorem cell19_90211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_90211 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90211 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90211 prefixEnd_90211 := by exact prefixLift 90211
  have htrace : WordTrace (prefixWord ++ tailWord_90211) baseStart_90211 baseEnd_90211 := by
    simpa [prefixWord, tailWord_90211, baseEnd_90211] using wordTrace_append hprefix tailTrace_90211
  have hstable : (prefixWord ++ tailWord_90211).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90211).length < 2 ^ (prefixWord ++ tailWord_90211).sum := by decide
  have hdescent : baseEnd_90211 < baseStart_90211 := by decide
  rcases family_descends (prefixWord ++ tailWord_90211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90260 : List Nat := [2, 4, 2, 3, 2, 1, 1, 4]
def baseStart_90260 : Nat := 118140960795 + 90260 * 2 ^ 59
def prefixEnd_90260 : Nat := 4983230072969 + 3 ^ 40 * 90260 * 2
def baseEnd_90260 : Nat := 27464748962916794687353

theorem tailTrace_90260 : CollatzResearch.WordTrace tailWord_90260 prefixEnd_90260 27464748962916794687353 := by
  unfold tailWord_90260
  simp only [CollatzResearch.WordTrace]
  refine ⟨1646026326505455012922117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2194701768673940017229489 1646026326505455012922117)
  ·
    refine ⟨308629936219772814922897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1646026326505455012922117 308629936219772814922897)
    ·
      refine ⟨231472452164829611192173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308629936219772814922897 231472452164829611192173)
      ·
        refine ⟨86802169561811104197065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231472452164829611192173 86802169561811104197065)
        ·
          refine ⟨65101627171358328147799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86802169561811104197065 65101627171358328147799)
          ·
            refine ⟨97652440757037492221699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65101627171358328147799 97652440757037492221699)
            ·
              refine ⟨146478661135556238332549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97652440757037492221699 146478661135556238332549)
              ·
                refine ⟨27464748962916794687353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146478661135556238332549 27464748962916794687353)
                ·
                  rfl

theorem cell19_90260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_90260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90260 prefixEnd_90260 := by exact prefixLift 90260
  have htrace : WordTrace (prefixWord ++ tailWord_90260) baseStart_90260 baseEnd_90260 := by
    simpa [prefixWord, tailWord_90260, baseEnd_90260] using wordTrace_append hprefix tailTrace_90260
  have hstable : (prefixWord ++ tailWord_90260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90260).length < 2 ^ (prefixWord ++ tailWord_90260).sum := by decide
  have hdescent : baseEnd_90260 < baseStart_90260 := by decide
  rcases family_descends (prefixWord ++ tailWord_90260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90264 : List Nat := [2, 1, 2, 4, 3, 2, 1, 4]
def baseStart_90264 : Nat := 118140960795 + 90264 * 2 ^ 59
def prefixEnd_90264 : Nat := 4983230072969 + 3 ^ 40 * 90264 * 2
def baseEnd_90264 : Nat := 27465966102245970598453

theorem tailTrace_90264 : CollatzResearch.WordTrace tailWord_90264 prefixEnd_90264 27465966102245970598453 := by
  unfold tailWord_90264
  simp only [CollatzResearch.WordTrace]
  refine ⟨1646099272498209354494923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2194799029997612472659897 1646099272498209354494923)
  ·
    refine ⟨2469148908747314031742385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1646099272498209354494923 2469148908747314031742385)
    ·
      refine ⟨1851861681560485523806789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2469148908747314031742385 1851861681560485523806789)
      ·
        refine ⟨347224065292591035713773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1851861681560485523806789 347224065292591035713773)
        ·
          refine ⟨130209024484721638392665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 347224065292591035713773 130209024484721638392665)
          ·
            refine ⟨97656768363541228794499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130209024484721638392665 97656768363541228794499)
            ·
              refine ⟨146485152545311843191749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97656768363541228794499 146485152545311843191749)
              ·
                refine ⟨27465966102245970598453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146485152545311843191749 27465966102245970598453)
                ·
                  rfl

theorem cell19_90264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_90264 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90264 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90264 prefixEnd_90264 := by exact prefixLift 90264
  have htrace : WordTrace (prefixWord ++ tailWord_90264) baseStart_90264 baseEnd_90264 := by
    simpa [prefixWord, tailWord_90264, baseEnd_90264] using wordTrace_append hprefix tailTrace_90264
  have hstable : (prefixWord ++ tailWord_90264).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90264).length < 2 ^ (prefixWord ++ tailWord_90264).sum := by decide
  have hdescent : baseEnd_90264 < baseStart_90264 := by decide
  rcases family_descends (prefixWord ++ tailWord_90264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90401 : List Nat := [1, 2, 3, 2, 1, 1, 4, 5]
def baseStart_90401 : Nat := 118140960795 + 90401 * 2 ^ 59
def prefixEnd_90401 : Nat := 4983230072969 + 3 ^ 40 * 90401 * 2
def baseEnd_90401 : Nat := 27507653124270245553635

theorem tailTrace_90401 : CollatzResearch.WordTrace tailWord_90401 prefixEnd_90401 27507653124270245553635 := by
  unfold tailWord_90401
  simp only [CollatzResearch.WordTrace]
  refine ⟨3297195345500091106727057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2198130230333394071151371 3297195345500091106727057)
  ·
    refine ⟨2472896509125068330045293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3297195345500091106727057 2472896509125068330045293)
    ·
      refine ⟨927336190921900623766985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2472896509125068330045293 927336190921900623766985)
      ·
        refine ⟨695502143191425467825239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 927336190921900623766985 695502143191425467825239)
        ·
          refine ⟨1043253214787138201737859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695502143191425467825239 1043253214787138201737859)
          ·
            refine ⟨1564879822180707302606789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043253214787138201737859 1564879822180707302606789)
            ·
              refine ⟨293414966658882619238773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1564879822180707302606789 293414966658882619238773)
              ·
                refine ⟨27507653124270245553635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 293414966658882619238773 27507653124270245553635)
                ·
                  rfl

theorem cell19_90401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_90401 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90401 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90401 prefixEnd_90401 := by exact prefixLift 90401
  have htrace : WordTrace (prefixWord ++ tailWord_90401) baseStart_90401 baseEnd_90401 := by
    simpa [prefixWord, tailWord_90401, baseEnd_90401] using wordTrace_append hprefix tailTrace_90401
  have hstable : (prefixWord ++ tailWord_90401).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90401).length < 2 ^ (prefixWord ++ tailWord_90401).sum := by decide
  have hdescent : baseEnd_90401 < baseStart_90401 := by decide
  rcases family_descends (prefixWord ++ tailWord_90401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90418 : List Nat := [3, 2, 1, 1, 6, 6]
def baseStart_90418 : Nat := 118140960795 + 90418 * 2 ^ 59
def prefixEnd_90418 : Nat := 4983230072969 + 3 ^ 40 * 90418 * 2
def baseEnd_90418 : Nat := 3056980662935471463979

theorem tailTrace_90418 : CollatzResearch.WordTrace tailWord_90418 prefixEnd_90418 3056980662935471463979 := by
  unfold tailWord_90418
  simp only [CollatzResearch.WordTrace]
  refine ⟨824453846609625752523977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2198543590959002006730605 824453846609625752523977)
  ·
    refine ⟨618340384957219314392983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 824453846609625752523977 618340384957219314392983)
    ·
      refine ⟨927510577435828971589475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 618340384957219314392983 927510577435828971589475)
      ·
        refine ⟨1391265866153743457384213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 927510577435828971589475 1391265866153743457384213)
        ·
          refine ⟨65215587475956724564885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1391265866153743457384213 65215587475956724564885)
          ·
            refine ⟨3056980662935471463979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65215587475956724564885 3056980662935471463979)
            ·
              rfl

theorem cell19_90418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 6].length) (baseStart_90418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90418 prefixEnd_90418 := by exact prefixLift 90418
  have htrace : WordTrace (prefixWord ++ tailWord_90418) baseStart_90418 baseEnd_90418 := by
    simpa [prefixWord, tailWord_90418, baseEnd_90418] using wordTrace_append hprefix tailTrace_90418
  have hstable : (prefixWord ++ tailWord_90418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90418).length < 2 ^ (prefixWord ++ tailWord_90418).sum := by decide
  have hdescent : baseEnd_90418 < baseStart_90418 := by decide
  rcases family_descends (prefixWord ++ tailWord_90418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90433 : List Nat := [1, 2, 5, 2, 3, 1, 1, 4]
def baseStart_90433 : Nat := 118140960795 + 90433 * 2 ^ 59
def prefixEnd_90433 : Nat := 4983230072969 + 3 ^ 40 * 90433 * 2
def baseEnd_90433 : Nat := 27517390238903652842437

theorem tailTrace_90433 : CollatzResearch.WordTrace tailWord_90433 prefixEnd_90433 27517390238903652842437 := by
  unfold tailWord_90433
  simp only [CollatzResearch.WordTrace]
  refine ⟨3298362481384160571891953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2198908320922773714594635 3298362481384160571891953)
  ·
    refine ⟨2473771861038120428918965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3298362481384160571891953 2473771861038120428918965)
    ·
      refine ⟨231916111972323790211153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2473771861038120428918965 231916111972323790211153)
      ·
        refine ⟨173937083979242842658365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231916111972323790211153 173937083979242842658365)
        ·
          refine ⟨65226406492216065996887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173937083979242842658365 65226406492216065996887)
          ·
            refine ⟨97839609738324098995331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65226406492216065996887 97839609738324098995331)
            ·
              refine ⟨146759414607486148492997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97839609738324098995331 146759414607486148492997)
              ·
                refine ⟨27517390238903652842437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146759414607486148492997 27517390238903652842437)
                ·
                  rfl

theorem cell19_90433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 4].length) (baseStart_90433 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90433 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90433 prefixEnd_90433 := by exact prefixLift 90433
  have htrace : WordTrace (prefixWord ++ tailWord_90433) baseStart_90433 baseEnd_90433 := by
    simpa [prefixWord, tailWord_90433, baseEnd_90433] using wordTrace_append hprefix tailTrace_90433
  have hstable : (prefixWord ++ tailWord_90433).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90433).length < 2 ^ (prefixWord ++ tailWord_90433).sum := by decide
  have hdescent : baseEnd_90433 < baseStart_90433 := by decide
  rcases family_descends (prefixWord ++ tailWord_90433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90477 : List Nat := [1, 5, 1, 1, 1, 2, 8]
def baseStart_90477 : Nat := 118140960795 + 90477 * 2 ^ 59
def prefixEnd_90477 : Nat := 4983230072969 + 3 ^ 40 * 90477 * 2
def baseEnd_90477 : Nat := 9176926257174862621513

theorem tailTrace_90477 : CollatzResearch.WordTrace tailWord_90477 prefixEnd_90477 9176926257174862621513 := by
  unfold tailWord_90477
  simp only [CollatzResearch.WordTrace]
  refine ⟨3299967293224756086493685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2199978195483170724329123 3299967293224756086493685)
  ·
    refine ⟨309371933739820883108783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3299967293224756086493685 309371933739820883108783)
    ·
      refine ⟨464057900609731324663175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309371933739820883108783 464057900609731324663175)
      ·
        refine ⟨696086850914596986994763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464057900609731324663175 696086850914596986994763)
        ·
          refine ⟨1044130276371895480492145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696086850914596986994763 1044130276371895480492145)
          ·
            refine ⟨783097707278921610369109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1044130276371895480492145 783097707278921610369109)
            ·
              refine ⟨9176926257174862621513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 783097707278921610369109 9176926257174862621513)
              ·
                rfl

theorem cell19_90477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 8].length) (baseStart_90477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90477 prefixEnd_90477 := by exact prefixLift 90477
  have htrace : WordTrace (prefixWord ++ tailWord_90477) baseStart_90477 baseEnd_90477 := by
    simpa [prefixWord, tailWord_90477, baseEnd_90477] using wordTrace_append hprefix tailTrace_90477
  have hstable : (prefixWord ++ tailWord_90477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90477).length < 2 ^ (prefixWord ++ tailWord_90477).sum := by decide
  have hdescent : baseEnd_90477 < baseStart_90477 := by decide
  rcases family_descends (prefixWord ++ tailWord_90477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90553 : List Nat := [1, 2, 1, 4, 3, 1, 1, 6]
def baseStart_90553 : Nat := 118140960795 + 90553 * 2 ^ 59
def prefixEnd_90553 : Nat := 4983230072969 + 3 ^ 40 * 90553 * 2
def baseEnd_90553 : Nat := 27553904418778930175443

theorem tailTrace_90553 : CollatzResearch.WordTrace tailWord_90553 prefixEnd_90553 27553904418778930175443 := by
  unfold tailWord_90553
  simp only [CollatzResearch.WordTrace]
  refine ⟨3302739240949421066260313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2201826160632947377506875 3302739240949421066260313)
  ·
    refine ⟨2477054430712065799695235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3302739240949421066260313 2477054430712065799695235)
    ·
      refine ⟨3715581646068098699542853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2477054430712065799695235 3715581646068098699542853)
      ·
        refine ⟨696671558637768506164285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3715581646068098699542853 696671558637768506164285)
        ·
          refine ⟨261251834489163189811607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 696671558637768506164285 261251834489163189811607)
          ·
            refine ⟨391877751733744784717411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261251834489163189811607 391877751733744784717411)
            ·
              refine ⟨587816627600617177076117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391877751733744784717411 587816627600617177076117)
              ·
                refine ⟨27553904418778930175443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 587816627600617177076117 27553904418778930175443)
                ·
                  rfl

theorem cell19_90553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_90553 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90553 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90553 prefixEnd_90553 := by exact prefixLift 90553
  have htrace : WordTrace (prefixWord ++ tailWord_90553) baseStart_90553 baseEnd_90553 := by
    simpa [prefixWord, tailWord_90553, baseEnd_90553] using wordTrace_append hprefix tailTrace_90553
  have hstable : (prefixWord ++ tailWord_90553).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90553).length < 2 ^ (prefixWord ++ tailWord_90553).sum := by decide
  have hdescent : baseEnd_90553 < baseStart_90553 := by decide
  rcases family_descends (prefixWord ++ tailWord_90553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90648 : List Nat := [2, 1, 2, 3, 3, 2, 6]
def baseStart_90648 : Nat := 118140960795 + 90648 * 2 ^ 59
def prefixEnd_90648 : Nat := 4983230072969 + 3 ^ 40 * 90648 * 2
def baseEnd_90648 : Nat := 9194270492615619354691

theorem tailTrace_90648 : CollatzResearch.WordTrace tailWord_90648 prefixEnd_90648 9194270492615619354691 := by
  unfold tailWord_90648
  simp only [CollatzResearch.WordTrace]
  refine ⟨1653102087802626145484299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2204136117070168193979065 1653102087802626145484299)
  ·
    refine ⟨2479653131703939218226449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1653102087802626145484299 2479653131703939218226449)
    ·
      refine ⟨1859739848777954413669837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2479653131703939218226449 1859739848777954413669837)
      ·
        refine ⟨697402443291732905126189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1859739848777954413669837 697402443291732905126189)
        ·
          refine ⟨261525916234399839422321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 697402443291732905126189 261525916234399839422321)
          ·
            refine ⟨196144437175799879566741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261525916234399839422321 196144437175799879566741)
            ·
              refine ⟨9194270492615619354691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 196144437175799879566741 9194270492615619354691)
              ·
                rfl

theorem cell19_90648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 6].length) (baseStart_90648 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90648 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90648 prefixEnd_90648 := by exact prefixLift 90648
  have htrace : WordTrace (prefixWord ++ tailWord_90648) baseStart_90648 baseEnd_90648 := by
    simpa [prefixWord, tailWord_90648, baseEnd_90648] using wordTrace_append hprefix tailTrace_90648
  have hstable : (prefixWord ++ tailWord_90648).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90648).length < 2 ^ (prefixWord ++ tailWord_90648).sum := by decide
  have hdescent : baseEnd_90648 < baseStart_90648 := by decide
  rcases family_descends (prefixWord ++ tailWord_90648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90684 : List Nat := [2, 2, 2, 2, 3, 1, 4, 3]
def baseStart_90684 : Nat := 118140960795 + 90684 * 2 ^ 59
def prefixEnd_90684 : Nat := 4983230072969 + 3 ^ 40 * 90684 * 2
def baseEnd_90684 : Nat := 27593765731809441263975

theorem tailTrace_90684 : CollatzResearch.WordTrace tailWord_90684 prefixEnd_90684 27593765731809441263975 := by
  unfold tailWord_90684
  simp only [CollatzResearch.WordTrace]
  refine ⟨1653758601737415219639553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2205011468983220292852737 1653758601737415219639553)
  ·
    refine ⟨1240318951303061414729665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1653758601737415219639553 1240318951303061414729665)
    ·
      refine ⟨930239213477296061047249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1240318951303061414729665 930239213477296061047249)
      ·
        refine ⟨697679410107972045785437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 930239213477296061047249 697679410107972045785437)
        ·
          refine ⟨261629778790489517169539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 697679410107972045785437 261629778790489517169539)
          ·
            refine ⟨392444668185734275754309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261629778790489517169539 392444668185734275754309)
            ·
              refine ⟨73583375284825176703933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 392444668185734275754309 73583375284825176703933)
              ·
                refine ⟨27593765731809441263975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73583375284825176703933 27593765731809441263975)
                ·
                  rfl

theorem cell19_90684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_90684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90684 prefixEnd_90684 := by exact prefixLift 90684
  have htrace : WordTrace (prefixWord ++ tailWord_90684) baseStart_90684 baseEnd_90684 := by
    simpa [prefixWord, tailWord_90684, baseEnd_90684] using wordTrace_append hprefix tailTrace_90684
  have hstable : (prefixWord ++ tailWord_90684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90684).length < 2 ^ (prefixWord ++ tailWord_90684).sum := by decide
  have hdescent : baseEnd_90684 < baseStart_90684 := by decide
  rcases family_descends (prefixWord ++ tailWord_90684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90705 : List Nat := [1, 2, 2, 1, 3, 5, 5]
def baseStart_90705 : Nat := 118140960795 + 90705 * 2 ^ 59
def prefixEnd_90705 : Nat := 4983230072969 + 3 ^ 40 * 90705 * 2
def baseEnd_90705 : Nat := 9200051904429204932417

theorem tailTrace_90705 : CollatzResearch.WordTrace tailWord_90705 prefixEnd_90705 9200051904429204932417 := by
  unfold tailWord_90705
  simp only [CollatzResearch.WordTrace]
  refine ⟨3308283136398751025793569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2205522090932500683862379 3308283136398751025793569)
  ·
    refine ⟨2481212352299063269345177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3308283136398751025793569 2481212352299063269345177)
    ·
      refine ⟨1860909264224297452008883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2481212352299063269345177 1860909264224297452008883)
      ·
        refine ⟨2791363896336446178013325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1860909264224297452008883 2791363896336446178013325)
        ·
          refine ⟨1046761461126167316754997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2791363896336446178013325 1046761461126167316754997)
          ·
            refine ⟨98133886980578185945781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1046761461126167316754997 98133886980578185945781)
            ·
              refine ⟨9200051904429204932417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98133886980578185945781 9200051904429204932417)
              ·
                rfl

theorem cell19_90705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 5].length) (baseStart_90705 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90705 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90705 prefixEnd_90705 := by exact prefixLift 90705
  have htrace : WordTrace (prefixWord ++ tailWord_90705) baseStart_90705 baseEnd_90705 := by
    simpa [prefixWord, tailWord_90705, baseEnd_90705] using wordTrace_append hprefix tailTrace_90705
  have hstable : (prefixWord ++ tailWord_90705).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90705).length < 2 ^ (prefixWord ++ tailWord_90705).sum := by decide
  have hdescent : baseEnd_90705 < baseStart_90705 := by decide
  rcases family_descends (prefixWord ++ tailWord_90705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90724 : List Nat := [2, 3, 1, 1, 2, 2, 4, 4]
def baseStart_90724 : Nat := 118140960795 + 90724 * 2 ^ 59
def prefixEnd_90724 : Nat := 4983230072969 + 3 ^ 40 * 90724 * 2
def baseEnd_90724 : Nat := 27605937125101200374977

theorem tailTrace_90724 : CollatzResearch.WordTrace tailWord_90724 prefixEnd_90724 27605937125101200374977 := by
  unfold tailWord_90724
  simp only [CollatzResearch.WordTrace]
  refine ⟨1654488061664958635367613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2205984082219944847156817 1654488061664958635367613)
  ·
    refine ⟨620433023124359488262855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1654488061664958635367613 620433023124359488262855)
    ·
      refine ⟨930649534686539232394283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 620433023124359488262855 930649534686539232394283)
      ·
        refine ⟨1395974302029808848591425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 930649534686539232394283 1395974302029808848591425)
        ·
          refine ⟨1046980726522356636443569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1395974302029808848591425 1046980726522356636443569)
          ·
            refine ⟨785235544891767477332677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1046980726522356636443569 785235544891767477332677)
            ·
              refine ⟨147231664667206401999877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 785235544891767477332677 147231664667206401999877)
              ·
                refine ⟨27605937125101200374977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147231664667206401999877 27605937125101200374977)
                ·
                  rfl

theorem cell19_90724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_90724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90724 prefixEnd_90724 := by exact prefixLift 90724
  have htrace : WordTrace (prefixWord ++ tailWord_90724) baseStart_90724 baseEnd_90724 := by
    simpa [prefixWord, tailWord_90724, baseEnd_90724] using wordTrace_append hprefix tailTrace_90724
  have hstable : (prefixWord ++ tailWord_90724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90724).length < 2 ^ (prefixWord ++ tailWord_90724).sum := by decide
  have hdescent : baseEnd_90724 < baseStart_90724 := by decide
  rcases family_descends (prefixWord ++ tailWord_90724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
