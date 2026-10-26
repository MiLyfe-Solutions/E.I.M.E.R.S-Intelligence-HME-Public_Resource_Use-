import V185TrunkScan22Chunk017

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_160968 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 1, 5]
def baseStart_160968 : Nat := 118140960795 + 160968 * 2 ^ 59
def prefixEnd_160968 : Nat := 4983230072969 + 3 ^ 40 * 160968 * 2
def baseEnd_160968 : Nat := 55102635995354297106485

theorem tailTrace_160968 : CollatzResearch.WordTrace tailWord_160968 prefixEnd_160968 55102635995354297106485 := by
  unfold tailWord_160968
  simp only [CollatzResearch.WordTrace]
  refine ⟨2935492640423950995413779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3913990187231934660551705 2935492640423950995413779)
  ·
    refine ⟨4403238960635926493120669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2935492640423950995413779 4403238960635926493120669)
    ·
      refine ⟨1651214610238472434920251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4403238960635926493120669 1651214610238472434920251)
      ·
        refine ⟨2476821915357708652380377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1651214610238472434920251 2476821915357708652380377)
        ·
          refine ⟨1857616436518281489285283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2476821915357708652380377 1857616436518281489285283)
          ·
            refine ⟨2786424654777422233927925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1857616436518281489285283 2786424654777422233927925)
            ·
              refine ⟨261227311385383334430743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2786424654777422233927925 261227311385383334430743)
              ·
                refine ⟨391840967078075001646115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261227311385383334430743 391840967078075001646115)
                ·
                  refine ⟨587761450617112502469173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 391840967078075001646115 587761450617112502469173)
                  ·
                    refine ⟨55102635995354297106485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 587761450617112502469173 55102635995354297106485)
                    ·
                      rfl

theorem cell22_160968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_160968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160968 prefixEnd_160968 := by exact prefixLift 160968
  have htrace : WordTrace (prefixWord ++ tailWord_160968) baseStart_160968 baseEnd_160968 := by
    simpa [prefixWord, tailWord_160968, baseEnd_160968] using wordTrace_append hprefix tailTrace_160968
  have hstable : (prefixWord ++ tailWord_160968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160968).length < 2 ^ (prefixWord ++ tailWord_160968).sum := by decide
  have hdescent : baseEnd_160968 < baseStart_160968 := by decide
  rcases family_descends (prefixWord ++ tailWord_160968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161047 : List Nat := [1, 1, 3, 4, 1, 1, 2, 5, 1, 3]
def baseStart_161047 : Nat := 118140960795 + 161047 * 2 ^ 59
def prefixEnd_161047 : Nat := 4983230072969 + 3 ^ 40 * 161047 * 2
def baseEnd_161047 : Nat := 55129679309824424381243

theorem tailTrace_161047 : CollatzResearch.WordTrace tailWord_161047 prefixEnd_161047 55129679309824424381243 := by
  unfold tailWord_161047
  simp only [CollatzResearch.WordTrace]
  refine ⟨5873866647561698482953395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3915911098374465655302263 5873866647561698482953395)
  ·
    refine ⟨8810799971342547724430093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5873866647561698482953395 8810799971342547724430093)
    ·
      refine ⟨3304049989253455396661285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8810799971342547724430093 3304049989253455396661285)
      ·
        refine ⟨619509372985022886873991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3304049989253455396661285 619509372985022886873991)
        ·
          refine ⟨929264059477534330310987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619509372985022886873991 929264059477534330310987)
          ·
            refine ⟨1393896089216301495466481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929264059477534330310987 1393896089216301495466481)
            ·
              refine ⟨1045422066912226121599861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1393896089216301495466481 1045422066912226121599861)
              ·
                refine ⟨98008318773021198899987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1045422066912226121599861 98008318773021198899987)
                ·
                  refine ⟨147012478159531798349981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98008318773021198899987 147012478159531798349981)
                  ·
                    refine ⟨55129679309824424381243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 147012478159531798349981 55129679309824424381243)
                    ·
                      rfl

theorem cell22_161047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_161047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161047 prefixEnd_161047 := by exact prefixLift 161047
  have htrace : WordTrace (prefixWord ++ tailWord_161047) baseStart_161047 baseEnd_161047 := by
    simpa [prefixWord, tailWord_161047, baseEnd_161047] using wordTrace_append hprefix tailTrace_161047
  have hstable : (prefixWord ++ tailWord_161047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161047).length < 2 ^ (prefixWord ++ tailWord_161047).sum := by decide
  have hdescent : baseEnd_161047 < baseStart_161047 := by decide
  rcases family_descends (prefixWord ++ tailWord_161047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161060 : List Nat := [2, 3, 1, 3, 1, 1, 4, 2, 5]
def baseStart_161060 : Nat := 118140960795 + 161060 * 2 ^ 59
def prefixEnd_161060 : Nat := 4983230072969 + 3 ^ 40 * 161060 * 2
def baseEnd_161060 : Nat := 18378043158498907935401

theorem tailTrace_161060 : CollatzResearch.WordTrace tailWord_161060 prefixEnd_161060 18378043158498907935401 := by
  unfold tailWord_161060
  simp only [CollatzResearch.WordTrace]
  refine ⟨2937170398257300851588317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3916227197676401135451089 2937170398257300851588317)
  ·
    refine ⟨1101438899346487819345619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2937170398257300851588317 1101438899346487819345619)
    ·
      refine ⟨1652158349019731729018429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1101438899346487819345619 1652158349019731729018429)
      ·
        refine ⟨619559380882399398381911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1652158349019731729018429 619559380882399398381911)
        ·
          refine ⟨929339071323599097572867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619559380882399398381911 929339071323599097572867)
          ·
            refine ⟨1394008606985398646359301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929339071323599097572867 1394008606985398646359301)
            ·
              refine ⟨261376613809762246192369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1394008606985398646359301 261376613809762246192369)
              ·
                refine ⟨196032460357321684644277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261376613809762246192369 196032460357321684644277)
                ·
                  refine ⟨18378043158498907935401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 196032460357321684644277 18378043158498907935401)
                  ·
                    rfl

theorem cell22_161060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_161060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161060 prefixEnd_161060 := by exact prefixLift 161060
  have htrace : WordTrace (prefixWord ++ tailWord_161060) baseStart_161060 baseEnd_161060 := by
    simpa [prefixWord, tailWord_161060, baseEnd_161060] using wordTrace_append hprefix tailTrace_161060
  have hstable : (prefixWord ++ tailWord_161060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161060).length < 2 ^ (prefixWord ++ tailWord_161060).sum := by decide
  have hdescent : baseEnd_161060 < baseStart_161060 := by decide
  rcases family_descends (prefixWord ++ tailWord_161060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161064 : List Nat := [2, 1, 5, 1, 2, 2, 1, 4, 1, 3]
def baseStart_161064 : Nat := 118140960795 + 161064 * 2 ^ 59
def prefixEnd_161064 : Nat := 4983230072969 + 3 ^ 40 * 161064 * 2
def baseEnd_161064 : Nat := 55135498757242046706191

theorem tailTrace_161064 : CollatzResearch.WordTrace tailWord_161064 prefixEnd_161064 55135498757242046706191 := by
  unfold tailWord_161064
  simp only [CollatzResearch.WordTrace]
  refine ⟨2937243344250055193161123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3916324459000073590881497 2937243344250055193161123)
  ·
    refine ⟨4405865016375082789741685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2937243344250055193161123 4405865016375082789741685)
    ·
      refine ⟨413049845285164011538283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4405865016375082789741685 413049845285164011538283)
      ·
        refine ⟨619574767927746017307425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413049845285164011538283 619574767927746017307425)
        ·
          refine ⟨464681075945809512980569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 619574767927746017307425 464681075945809512980569)
          ·
            refine ⟨348510806959357134735427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464681075945809512980569 348510806959357134735427)
            ·
              refine ⟨522766210439035702103141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348510806959357134735427 522766210439035702103141)
              ·
                refine ⟨98018664457319194144339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 522766210439035702103141 98018664457319194144339)
                ·
                  refine ⟨147027996685978791216509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98018664457319194144339 147027996685978791216509)
                  ·
                    refine ⟨55135498757242046706191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 147027996685978791216509 55135498757242046706191)
                    ·
                      rfl

theorem cell22_161064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_161064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161064 prefixEnd_161064 := by exact prefixLift 161064
  have htrace : WordTrace (prefixWord ++ tailWord_161064) baseStart_161064 baseEnd_161064 := by
    simpa [prefixWord, tailWord_161064, baseEnd_161064] using wordTrace_append hprefix tailTrace_161064
  have hstable : (prefixWord ++ tailWord_161064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161064).length < 2 ^ (prefixWord ++ tailWord_161064).sum := by decide
  have hdescent : baseEnd_161064 < baseStart_161064 := by decide
  rcases family_descends (prefixWord ++ tailWord_161064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161088 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 6]
def baseStart_161088 : Nat := 118140960795 + 161088 * 2 ^ 59
def prefixEnd_161088 : Nat := 4983230072969 + 3 ^ 40 * 161088 * 2
def baseEnd_161088 : Nat := 18381238149237994702039

theorem tailTrace_161088 : CollatzResearch.WordTrace tailWord_161088 prefixEnd_161088 18381238149237994702039 := by
  unfold tailWord_161088
  simp only [CollatzResearch.WordTrace]
  refine ⟨2937681020206581242597959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3916908026942108323463945 2937681020206581242597959)
  ·
    refine ⟨4406521530309871863896939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2937681020206581242597959 4406521530309871863896939)
    ·
      refine ⟨6609782295464807795845409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4406521530309871863896939 6609782295464807795845409)
      ·
        refine ⟨4957336721598605846884057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6609782295464807795845409 4957336721598605846884057)
        ·
          refine ⟨3718002541198954385163043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4957336721598605846884057 3718002541198954385163043)
          ·
            refine ⟨5577003811798431577744565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3718002541198954385163043 5577003811798431577744565)
            ·
              refine ⟨522844107356102960413553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5577003811798431577744565 522844107356102960413553)
              ·
                refine ⟨392133080517077220310165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522844107356102960413553 392133080517077220310165)
                ·
                  refine ⟨18381238149237994702039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 392133080517077220310165 18381238149237994702039)
                  ·
                    rfl

theorem cell22_161088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 6].length) (baseStart_161088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161088 prefixEnd_161088 := by exact prefixLift 161088
  have htrace : WordTrace (prefixWord ++ tailWord_161088) baseStart_161088 baseEnd_161088 := by
    simpa [prefixWord, tailWord_161088, baseEnd_161088] using wordTrace_append hprefix tailTrace_161088
  have hstable : (prefixWord ++ tailWord_161088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161088).length < 2 ^ (prefixWord ++ tailWord_161088).sum := by decide
  have hdescent : baseEnd_161088 < baseStart_161088 := by decide
  rcases family_descends (prefixWord ++ tailWord_161088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161122 : List Nat := [3, 3, 2, 1, 1, 1, 1, 6, 4]
def baseStart_161122 : Nat := 118140960795 + 161122 * 2 ^ 59
def prefixEnd_161122 : Nat := 4983230072969 + 3 ^ 40 * 161122 * 2
def baseEnd_161122 : Nat := 18385117780849742918671

theorem tailTrace_161122 : CollatzResearch.WordTrace tailWord_161122 prefixEnd_161122 18385117780849742918671 := by
  unfold tailWord_161122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1469150530572496572983405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3917734748193324194622413 1469150530572496572983405)
  ·
    refine ⟨550931448964686214868777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1469150530572496572983405 550931448964686214868777)
    ·
      refine ⟨413198586723514661151583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 550931448964686214868777 413198586723514661151583)
      ·
        refine ⟨619797880085271991727375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413198586723514661151583 619797880085271991727375)
        ·
          refine ⟨929696820127907987591063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619797880085271991727375 929696820127907987591063)
          ·
            refine ⟨1394545230191861981386595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929696820127907987591063 1394545230191861981386595)
            ·
              refine ⟨2091817845287792972079893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394545230191861981386595 2091817845287792972079893)
              ·
                refine ⟨98053961497865295566245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2091817845287792972079893 98053961497865295566245)
                ·
                  refine ⟨18385117780849742918671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98053961497865295566245 18385117780849742918671)
                  ·
                    rfl

theorem cell22_161122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_161122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161122 prefixEnd_161122 := by exact prefixLift 161122
  have htrace : WordTrace (prefixWord ++ tailWord_161122) baseStart_161122 baseEnd_161122 := by
    simpa [prefixWord, tailWord_161122, baseEnd_161122] using wordTrace_append hprefix tailTrace_161122
  have hstable : (prefixWord ++ tailWord_161122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161122).length < 2 ^ (prefixWord ++ tailWord_161122).sum := by decide
  have hdescent : baseEnd_161122 < baseStart_161122 := by decide
  rcases family_descends (prefixWord ++ tailWord_161122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161148 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 2, 7]
def baseStart_161148 : Nat := 118140960795 + 161148 * 2 ^ 59
def prefixEnd_161148 : Nat := 4983230072969 + 3 ^ 40 * 161148 * 2
def baseEnd_161148 : Nat := 55164253673893827605933

theorem tailTrace_161148 : CollatzResearch.WordTrace tailWord_161148 prefixEnd_161148 55164253673893827605933 := by
  unfold tailWord_161148
  simp only [CollatzResearch.WordTrace]
  refine ⟨2938775210097896366190049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3918366946797195154920065 2938775210097896366190049)
  ·
    refine ⟨2204081407573422274642537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2938775210097896366190049 2204081407573422274642537)
    ·
      refine ⟨1653061055680066705981903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2204081407573422274642537 1653061055680066705981903)
      ·
        refine ⟨2479591583520100058972855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1653061055680066705981903 2479591583520100058972855)
        ·
          refine ⟨3719387375280150088459283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2479591583520100058972855 3719387375280150088459283)
          ·
            refine ⟨5579081062920225132688925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3719387375280150088459283 5579081062920225132688925)
            ·
              refine ⟨2092155398595084424758347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5579081062920225132688925 2092155398595084424758347)
              ·
                refine ⟨3138233097892626637137521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2092155398595084424758347 3138233097892626637137521)
                ·
                  refine ⟨2353674823419469977853141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3138233097892626637137521 2353674823419469977853141)
                  ·
                    refine ⟨55164253673893827605933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2353674823419469977853141 55164253673893827605933)
                    ·
                      rfl

theorem cell22_161148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_161148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161148 prefixEnd_161148 := by exact prefixLift 161148
  have htrace : WordTrace (prefixWord ++ tailWord_161148) baseStart_161148 baseEnd_161148 := by
    simpa [prefixWord, tailWord_161148, baseEnd_161148] using wordTrace_append hprefix tailTrace_161148
  have hstable : (prefixWord ++ tailWord_161148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161148).length < 2 ^ (prefixWord ++ tailWord_161148).sum := by decide
  have hdescent : baseEnd_161148 < baseStart_161148 := by decide
  rcases family_descends (prefixWord ++ tailWord_161148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161154 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_161154 : Nat := 118140960795 + 161154 * 2 ^ 59
def prefixEnd_161154 : Nat := 4983230072969 + 3 ^ 40 * 161154 * 2
def baseEnd_161154 : Nat := 55166307596511811955915

theorem tailTrace_161154 : CollatzResearch.WordTrace tailWord_161154 prefixEnd_161154 55166307596511811955915 := by
  unfold tailWord_161154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1469442314543513939274629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3918512838782703838065677 1469442314543513939274629)
  ·
    refine ⟨275520433976908863613993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1469442314543513939274629 275520433976908863613993)
    ·
      refine ⟨206640325482681647710495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275520433976908863613993 206640325482681647710495)
      ·
        refine ⟨309960488224022471565743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206640325482681647710495 309960488224022471565743)
        ·
          refine ⟨464940732336033707348615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309960488224022471565743 464940732336033707348615)
          ·
            refine ⟨697411098504050561022923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464940732336033707348615 697411098504050561022923)
            ·
              refine ⟨1046116647756075841534385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697411098504050561022923 1046116647756075841534385)
              ·
                refine ⟨784587485817056881150789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1046116647756075841534385 784587485817056881150789)
                ·
                  refine ⟨147110153590698165215773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 784587485817056881150789 147110153590698165215773)
                  ·
                    refine ⟨55166307596511811955915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 147110153590698165215773 55166307596511811955915)
                    ·
                      rfl

theorem cell22_161154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_161154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161154 prefixEnd_161154 := by exact prefixLift 161154
  have htrace : WordTrace (prefixWord ++ tailWord_161154) baseStart_161154 baseEnd_161154 := by
    simpa [prefixWord, tailWord_161154, baseEnd_161154] using wordTrace_append hprefix tailTrace_161154
  have hstable : (prefixWord ++ tailWord_161154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161154).length < 2 ^ (prefixWord ++ tailWord_161154).sum := by decide
  have hdescent : baseEnd_161154 < baseStart_161154 := by decide
  rcases family_descends (prefixWord ++ tailWord_161154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161310 : List Nat := [4, 3, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_161310 : Nat := 118140960795 + 161310 * 2 ^ 59
def prefixEnd_161310 : Nat := 4983230072969 + 3 ^ 40 * 161310 * 2
def baseEnd_161310 : Nat := 55219709584579405055437

theorem tailTrace_161310 : CollatzResearch.WordTrace tailWord_161310 prefixEnd_161310 55219709584579405055437 := by
  unfold tailWord_161310
  simp only [CollatzResearch.WordTrace]
  refine ⟨735432380701111799972173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3922306030405929599851589 735432380701111799972173)
  ·
    refine ⟨275787142762916924989565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 735432380701111799972173 275787142762916924989565)
    ·
      refine ⟨103420178536093846871087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275787142762916924989565 103420178536093846871087)
      ·
        refine ⟨155130267804140770306631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103420178536093846871087 155130267804140770306631)
        ·
          refine ⟨232695401706211155459947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155130267804140770306631 232695401706211155459947)
          ·
            refine ⟨349043102559316733189921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232695401706211155459947 349043102559316733189921)
            ·
              refine ⟨261782326919487549892441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349043102559316733189921 261782326919487549892441)
              ·
                refine ⟨196336745189615662419331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261782326919487549892441 196336745189615662419331)
                ·
                  refine ⟨294505117784423493628997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196336745189615662419331 294505117784423493628997)
                  ·
                    refine ⟨55219709584579405055437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 294505117784423493628997 55219709584579405055437)
                    ·
                      rfl

theorem cell22_161310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_161310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161310 prefixEnd_161310 := by exact prefixLift 161310
  have htrace : WordTrace (prefixWord ++ tailWord_161310) baseStart_161310 baseEnd_161310 := by
    simpa [prefixWord, tailWord_161310, baseEnd_161310] using wordTrace_append hprefix tailTrace_161310
  have hstable : (prefixWord ++ tailWord_161310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161310).length < 2 ^ (prefixWord ++ tailWord_161310).sum := by decide
  have hdescent : baseEnd_161310 < baseStart_161310 := by decide
  rcases family_descends (prefixWord ++ tailWord_161310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161351 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 3, 3]
def baseStart_161351 : Nat := 118140960795 + 161351 * 2 ^ 59
def prefixEnd_161351 : Nat := 4983230072969 + 3 ^ 40 * 161351 * 2
def baseEnd_161351 : Nat := 55233744722468964780311

theorem tailTrace_161351 : CollatzResearch.WordTrace tailWord_161351 prefixEnd_161351 55233744722468964780311 := by
  unfold tailWord_161351
  simp only [CollatzResearch.WordTrace]
  refine ⟨5884954438460358402019907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3923302958973572268013271 5884954438460358402019907)
  ·
    refine ⟨8827431657690537603029861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5884954438460358402019907 8827431657690537603029861)
    ·
      refine ⟨1655143435816975800568099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8827431657690537603029861 1655143435816975800568099)
      ·
        refine ⟨2482715153725463700852149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655143435816975800568099 2482715153725463700852149)
        ·
          refine ⟨232754545661762221954889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2482715153725463700852149 232754545661762221954889)
          ·
            refine ⟨174565909246321666466167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232754545661762221954889 174565909246321666466167)
            ·
              refine ⟨261848863869482499699251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174565909246321666466167 261848863869482499699251)
              ·
                refine ⟨392773295804223749548877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261848863869482499699251 392773295804223749548877)
                ·
                  refine ⟨147289985926583906080829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392773295804223749548877 147289985926583906080829)
                  ·
                    refine ⟨55233744722468964780311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 147289985926583906080829 55233744722468964780311)
                    ·
                      rfl

theorem cell22_161351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_161351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161351 prefixEnd_161351 := by exact prefixLift 161351
  have htrace : WordTrace (prefixWord ++ tailWord_161351) baseStart_161351 baseEnd_161351 := by
    simpa [prefixWord, tailWord_161351, baseEnd_161351] using wordTrace_append hprefix tailTrace_161351
  have hstable : (prefixWord ++ tailWord_161351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161351).length < 2 ^ (prefixWord ++ tailWord_161351).sum := by decide
  have hdescent : baseEnd_161351 < baseStart_161351 := by decide
  rcases family_descends (prefixWord ++ tailWord_161351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161377 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 3, 4]
def baseStart_161377 : Nat := 118140960795 + 161377 * 2 ^ 59
def prefixEnd_161377 : Nat := 4983230072969 + 3 ^ 40 * 161377 * 2
def baseEnd_161377 : Nat := 55242645053813563630231

theorem tailTrace_161377 : CollatzResearch.WordTrace tailWord_161377 prefixEnd_161377 55242645053813563630231 := by
  unfold tailWord_161377
  simp only [CollatzResearch.WordTrace]
  refine ⟨5885902736366164842466385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3923935157577443228310923 5885902736366164842466385)
  ·
    refine ⟨4414427052274623631849789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5885902736366164842466385 4414427052274623631849789)
    ·
      refine ⟨1655410144602983861943671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4414427052274623631849789 1655410144602983861943671)
      ·
        refine ⟨2483115216904475792915507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655410144602983861943671 2483115216904475792915507)
        ·
          refine ⟨3724672825356713689373261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2483115216904475792915507 3724672825356713689373261)
          ·
            refine ⟨1396752309508767633514973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3724672825356713689373261 1396752309508767633514973)
            ·
              refine ⟨523782116065787862568115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1396752309508767633514973 523782116065787862568115)
              ·
                refine ⟨785673174098681793852173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523782116065787862568115 785673174098681793852173)
                ·
                  refine ⟨294627440287005672694565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 785673174098681793852173 294627440287005672694565)
                  ·
                    refine ⟨55242645053813563630231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 294627440287005672694565 55242645053813563630231)
                    ·
                      rfl

theorem cell22_161377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_161377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161377 prefixEnd_161377 := by exact prefixLift 161377
  have htrace : WordTrace (prefixWord ++ tailWord_161377) baseStart_161377 baseEnd_161377 := by
    simpa [prefixWord, tailWord_161377, baseEnd_161377] using wordTrace_append hprefix tailTrace_161377
  have hstable : (prefixWord ++ tailWord_161377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161377).length < 2 ^ (prefixWord ++ tailWord_161377).sum := by decide
  have hdescent : baseEnd_161377 < baseStart_161377 := by decide
  rcases family_descends (prefixWord ++ tailWord_161377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161407 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 8, 3]
def baseStart_161407 : Nat := 118140960795 + 161407 * 2 ^ 59
def prefixEnd_161407 : Nat := 4983230072969 + 3 ^ 40 * 161407 * 2
def baseEnd_161407 : Nat := 55252914666903485380139

theorem tailTrace_161407 : CollatzResearch.WordTrace tailWord_161407 prefixEnd_161407 55252914666903485380139 := by
  unfold tailWord_161407
  simp only [CollatzResearch.WordTrace]
  refine ⟨5886996926257479966058475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3924664617504986644038983 5886996926257479966058475)
  ·
    refine ⟨8830495389386219949087713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5886996926257479966058475 8830495389386219949087713)
    ·
      refine ⟨6622871542039664961815785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8830495389386219949087713 6622871542039664961815785)
      ·
        refine ⟨4967153656529748721361839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6622871542039664961815785 4967153656529748721361839)
        ·
          refine ⟨7450730484794623082042759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4967153656529748721361839 7450730484794623082042759)
          ·
            refine ⟨11176095727191934623064139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7450730484794623082042759 11176095727191934623064139)
            ·
              refine ⟨16764143590787901934596209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11176095727191934623064139 16764143590787901934596209)
              ·
                refine ⟨12573107693090926450947157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16764143590787901934596209 12573107693090926450947157)
                ·
                  refine ⟨147341105778409294347037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12573107693090926450947157 147341105778409294347037)
                  ·
                    refine ⟨55252914666903485380139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 147341105778409294347037 55252914666903485380139)
                    ·
                      rfl

theorem cell22_161407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 3].length) (baseStart_161407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161407 prefixEnd_161407 := by exact prefixLift 161407
  have htrace : WordTrace (prefixWord ++ tailWord_161407) baseStart_161407 baseEnd_161407 := by
    simpa [prefixWord, tailWord_161407, baseEnd_161407] using wordTrace_append hprefix tailTrace_161407
  have hstable : (prefixWord ++ tailWord_161407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161407).length < 2 ^ (prefixWord ++ tailWord_161407).sum := by decide
  have hdescent : baseEnd_161407 < baseStart_161407 := by decide
  rcases family_descends (prefixWord ++ tailWord_161407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161546 : List Nat := [3, 1, 2, 2, 1, 3, 3, 2, 1, 4]
def baseStart_161546 : Nat := 118140960795 + 161546 * 2 ^ 59
def prefixEnd_161546 : Nat := 4983230072969 + 3 ^ 40 * 161546 * 2
def baseEnd_161546 : Nat := 55300497207553456154713

theorem tailTrace_161546 : CollatzResearch.WordTrace tailWord_161546 prefixEnd_161546 55300497207553456154713 := by
  unfold tailWord_161546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1473016668188476676342123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3928044448502604470245661 1473016668188476676342123)
  ·
    refine ⟨2209525002282715014513185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1473016668188476676342123 2209525002282715014513185)
    ·
      refine ⟨1657143751712036260884889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2209525002282715014513185 1657143751712036260884889)
      ·
        refine ⟨1242857813784027195663667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1657143751712036260884889 1242857813784027195663667)
        ·
          refine ⟨1864286720676040793495501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242857813784027195663667 1864286720676040793495501)
          ·
            refine ⟨699107520253515297560813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1864286720676040793495501 699107520253515297560813)
            ·
              refine ⟨262165320095068236585305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 699107520253515297560813 262165320095068236585305)
              ·
                refine ⟨196623990071301177438979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262165320095068236585305 196623990071301177438979)
                ·
                  refine ⟨294935985106951766158469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196623990071301177438979 294935985106951766158469)
                  ·
                    refine ⟨55300497207553456154713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 294935985106951766158469 55300497207553456154713)
                    ·
                      rfl

theorem cell22_161546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_161546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161546 prefixEnd_161546 := by exact prefixLift 161546
  have htrace : WordTrace (prefixWord ++ tailWord_161546) baseStart_161546 baseEnd_161546 := by
    simpa [prefixWord, tailWord_161546, baseEnd_161546] using wordTrace_append hprefix tailTrace_161546
  have hstable : (prefixWord ++ tailWord_161546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161546).length < 2 ^ (prefixWord ++ tailWord_161546).sum := by decide
  have hdescent : baseEnd_161546 < baseStart_161546 := by decide
  rcases family_descends (prefixWord ++ tailWord_161546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161559 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 3, 5]
def baseStart_161559 : Nat := 118140960795 + 161559 * 2 ^ 59
def prefixEnd_161559 : Nat := 4983230072969 + 3 ^ 40 * 161559 * 2
def baseEnd_161559 : Nat := 55304947373225755579673

theorem tailTrace_161559 : CollatzResearch.WordTrace tailWord_161559 prefixEnd_161559 55304947373225755579673 := by
  unfold tailWord_161559
  simp only [CollatzResearch.WordTrace]
  refine ⟨5892540821706809925591731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3928360547804539950394487 5892540821706809925591731)
  ·
    refine ⟨8838811232560214888387597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5892540821706809925591731 8838811232560214888387597)
    ·
      refine ⟨3314554212210080583145349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8838811232560214888387597 3314554212210080583145349)
      ·
        refine ⟨621478914789390109339753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3314554212210080583145349 621478914789390109339753)
        ·
          refine ⟨466109186092042582004815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 621478914789390109339753 466109186092042582004815)
          ·
            refine ⟨699163779138063873007223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466109186092042582004815 699163779138063873007223)
            ·
              refine ⟨1048745668707095809510835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699163779138063873007223 1048745668707095809510835)
              ·
                refine ⟨1573118503060643714266253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048745668707095809510835 1573118503060643714266253)
                ·
                  refine ⟨589919438647741392849845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1573118503060643714266253 589919438647741392849845)
                  ·
                    refine ⟨55304947373225755579673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 589919438647741392849845 55304947373225755579673)
                    ·
                      rfl

theorem cell22_161559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_161559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161559 prefixEnd_161559 := by exact prefixLift 161559
  have htrace : WordTrace (prefixWord ++ tailWord_161559) baseStart_161559 baseEnd_161559 := by
    simpa [prefixWord, tailWord_161559, baseEnd_161559] using wordTrace_append hprefix tailTrace_161559
  have hstable : (prefixWord ++ tailWord_161559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161559).length < 2 ^ (prefixWord ++ tailWord_161559).sum := by decide
  have hdescent : baseEnd_161559 < baseStart_161559 := by decide
  rcases family_descends (prefixWord ++ tailWord_161559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161593 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 1, 5]
def baseStart_161593 : Nat := 118140960795 + 161593 * 2 ^ 59
def prefixEnd_161593 : Nat := 4983230072969 + 3 ^ 40 * 161593 * 2
def baseEnd_161593 : Nat := 55316586268061000229569

theorem tailTrace_161593 : CollatzResearch.WordTrace tailWord_161593 prefixEnd_161593 55316586268061000229569 := by
  unfold tailWord_161593
  simp only [CollatzResearch.WordTrace]
  refine ⟨5893780903583633732329433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3929187269055755821552955 5893780903583633732329433)
  ·
    refine ⟨4420335677687725299247075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5893780903583633732329433 4420335677687725299247075)
    ·
      refine ⟨6630503516531587948870613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4420335677687725299247075 6630503516531587948870613)
      ·
        refine ⟨155402426168709092551655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 6630503516531587948870613 155402426168709092551655)
        ·
          refine ⟨233103639253063638827483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155402426168709092551655 233103639253063638827483)
          ·
            refine ⟨349655458879595458241225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233103639253063638827483 349655458879595458241225)
            ·
              refine ⟨262241594159696593680919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349655458879595458241225 262241594159696593680919)
              ·
                refine ⟨393362391239544890521379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262241594159696593680919 393362391239544890521379)
                ·
                  refine ⟨590043586859317335782069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 393362391239544890521379 590043586859317335782069)
                  ·
                    refine ⟨55316586268061000229569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 590043586859317335782069 55316586268061000229569)
                    ·
                      rfl

theorem cell22_161593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 5].length) (baseStart_161593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161593 prefixEnd_161593 := by exact prefixLift 161593
  have htrace : WordTrace (prefixWord ++ tailWord_161593) baseStart_161593 baseEnd_161593 := by
    simpa [prefixWord, tailWord_161593, baseEnd_161593] using wordTrace_append hprefix tailTrace_161593
  have hstable : (prefixWord ++ tailWord_161593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161593).length < 2 ^ (prefixWord ++ tailWord_161593).sum := by decide
  have hdescent : baseEnd_161593 < baseStart_161593 := by decide
  rcases family_descends (prefixWord ++ tailWord_161593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161649 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 2, 5]
def baseStart_161649 : Nat := 118140960795 + 161649 * 2 ^ 59
def prefixEnd_161649 : Nat := 4983230072969 + 3 ^ 40 * 161649 * 2
def baseEnd_161649 : Nat := 55335756212495520829397

theorem tailTrace_161649 : CollatzResearch.WordTrace tailWord_161649 prefixEnd_161649 55335756212495520829397 := by
  unfold tailWord_161649
  simp only [CollatzResearch.WordTrace]
  refine ⟨5895823391380755296368001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3930548927587170197578667 5895823391380755296368001)
  ·
    refine ⟨4421867543535566472276001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5895823391380755296368001 4421867543535566472276001)
    ·
      refine ⟨3316400657651674854207001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4421867543535566472276001 3316400657651674854207001)
      ·
        refine ⟨2487300493238756140655251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3316400657651674854207001 2487300493238756140655251)
        ·
          refine ⟨3730950739858134210982877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2487300493238756140655251 3730950739858134210982877)
          ·
            refine ⟨1399106527446800329118579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3730950739858134210982877 1399106527446800329118579)
            ·
              refine ⟨2098659791170200493677869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399106527446800329118579 2098659791170200493677869)
              ·
                refine ⟨786997421688825185129201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2098659791170200493677869 786997421688825185129201)
                ·
                  refine ⟨590248066266618888846901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 786997421688825185129201 590248066266618888846901)
                  ·
                    refine ⟨55335756212495520829397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 590248066266618888846901 55335756212495520829397)
                    ·
                      rfl

theorem cell22_161649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_161649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161649 prefixEnd_161649 := by exact prefixLift 161649
  have htrace : WordTrace (prefixWord ++ tailWord_161649) baseStart_161649 baseEnd_161649 := by
    simpa [prefixWord, tailWord_161649, baseEnd_161649] using wordTrace_append hprefix tailTrace_161649
  have hstable : (prefixWord ++ tailWord_161649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161649).length < 2 ^ (prefixWord ++ tailWord_161649).sum := by decide
  have hdescent : baseEnd_161649 < baseStart_161649 := by decide
  rcases family_descends (prefixWord ++ tailWord_161649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161672 : List Nat := [2, 1, 3, 3, 3, 2, 1, 3, 1, 3]
def baseStart_161672 : Nat := 118140960795 + 161672 * 2 ^ 59
def prefixEnd_161672 : Nat := 4983230072969 + 3 ^ 40 * 161672 * 2
def baseEnd_161672 : Nat := 55343629582531127504327

theorem tailTrace_161672 : CollatzResearch.WordTrace tailWord_161672 prefixEnd_161672 55343629582531127504327 := by
  unfold tailWord_161672
  simp only [CollatzResearch.WordTrace]
  refine ⟨2948331135148715112227635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3931108180198286816303513 2948331135148715112227635)
  ·
    refine ⟨4422496702723072668341453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2948331135148715112227635 4422496702723072668341453)
    ·
      refine ⟨1658436263521152250628045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4422496702723072668341453 1658436263521152250628045)
      ·
        refine ⟨621913598820432093985517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1658436263521152250628045 621913598820432093985517)
        ·
          refine ⟨233217599557662035244569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 621913598820432093985517 233217599557662035244569)
          ·
            refine ⟨174913199668246526433427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233217599557662035244569 174913199668246526433427)
            ·
              refine ⟨262369799502369789650141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174913199668246526433427 262369799502369789650141)
              ·
                refine ⟨98388674813388671118803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262369799502369789650141 98388674813388671118803)
                ·
                  refine ⟨147583012220083006678205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98388674813388671118803 147583012220083006678205)
                  ·
                    refine ⟨55343629582531127504327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 147583012220083006678205 55343629582531127504327)
                    ·
                      rfl

theorem cell22_161672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_161672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161672 prefixEnd_161672 := by exact prefixLift 161672
  have htrace : WordTrace (prefixWord ++ tailWord_161672) baseStart_161672 baseEnd_161672 := by
    simpa [prefixWord, tailWord_161672, baseEnd_161672] using wordTrace_append hprefix tailTrace_161672
  have hstable : (prefixWord ++ tailWord_161672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161672).length < 2 ^ (prefixWord ++ tailWord_161672).sum := by decide
  have hdescent : baseEnd_161672 < baseStart_161672 := by decide
  rcases family_descends (prefixWord ++ tailWord_161672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161681 : List Nat := [1, 2, 2, 1, 1, 1, 6, 3, 1, 4]
def baseStart_161681 : Nat := 118140960795 + 161681 * 2 ^ 59
def prefixEnd_161681 : Nat := 4983230072969 + 3 ^ 40 * 161681 * 2
def baseEnd_161681 : Nat := 55346710466458104029299

theorem tailTrace_161681 : CollatzResearch.WordTrace tailWord_161681 prefixEnd_161681 55346710466458104029299 := by
  unfold tailWord_161681
  simp only [CollatzResearch.WordTrace]
  refine ⟨5896990527264824761532897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3931327018176549841021931 5896990527264824761532897)
  ·
    refine ⟨4422742895448618571149673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5896990527264824761532897 4422742895448618571149673)
    ·
      refine ⟨3317057171586463928362255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4422742895448618571149673 3317057171586463928362255)
      ·
        refine ⟨4975585757379695892543383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3317057171586463928362255 4975585757379695892543383)
        ·
          refine ⟨7463378636069543838815075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4975585757379695892543383 7463378636069543838815075)
          ·
            refine ⟨11195067954104315758222613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7463378636069543838815075 11195067954104315758222613)
            ·
              refine ⟨524768810348639801166685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11195067954104315758222613 524768810348639801166685)
              ·
                refine ⟨196788303880739925437507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 524768810348639801166685 196788303880739925437507)
                ·
                  refine ⟨295182455821109888156261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196788303880739925437507 295182455821109888156261)
                  ·
                    refine ⟨55346710466458104029299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 295182455821109888156261 55346710466458104029299)
                    ·
                      rfl

theorem cell22_161681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_161681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161681 prefixEnd_161681 := by exact prefixLift 161681
  have htrace : WordTrace (prefixWord ++ tailWord_161681) baseStart_161681 baseEnd_161681 := by
    simpa [prefixWord, tailWord_161681, baseEnd_161681] using wordTrace_append hprefix tailTrace_161681
  have hstable : (prefixWord ++ tailWord_161681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161681).length < 2 ^ (prefixWord ++ tailWord_161681).sum := by decide
  have hdescent : baseEnd_161681 < baseStart_161681 := by decide
  rcases family_descends (prefixWord ++ tailWord_161681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161820 : List Nat := [2, 2, 3, 1, 3, 2, 3, 1, 5]
def baseStart_161820 : Nat := 118140960795 + 161820 * 2 ^ 59
def prefixEnd_161820 : Nat := 4983230072969 + 3 ^ 40 * 161820 * 2
def baseEnd_161820 : Nat := 18464764335702691601291

theorem tailTrace_161820 : CollatzResearch.WordTrace tailWord_161820 prefixEnd_161820 18464764335702691601291 := by
  unfold tailWord_161820
  simp only [CollatzResearch.WordTrace]
  refine ⟨2951030136880625750421457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3934706849174167667228609 2951030136880625750421457)
  ·
    refine ⟨2213272602660469312816093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2951030136880625750421457 2213272602660469312816093)
    ·
      refine ⟨829977225997675992306035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2213272602660469312816093 829977225997675992306035)
      ·
        refine ⟨1244965838996513988459053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 829977225997675992306035 1244965838996513988459053)
        ·
          refine ⟨466862189623692745672145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1244965838996513988459053 466862189623692745672145)
          ·
            refine ⟨350146642217769559254109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 466862189623692745672145 350146642217769559254109)
            ·
              refine ⟨131304990831663584720291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350146642217769559254109 131304990831663584720291)
              ·
                refine ⟨196957486247495377080437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131304990831663584720291 196957486247495377080437)
                ·
                  refine ⟨18464764335702691601291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 196957486247495377080437 18464764335702691601291)
                  ·
                    rfl

theorem cell22_161820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_161820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161820 prefixEnd_161820 := by exact prefixLift 161820
  have htrace : WordTrace (prefixWord ++ tailWord_161820) baseStart_161820 baseEnd_161820 := by
    simpa [prefixWord, tailWord_161820, baseEnd_161820] using wordTrace_append hprefix tailTrace_161820
  have hstable : (prefixWord ++ tailWord_161820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161820).length < 2 ^ (prefixWord ++ tailWord_161820).sum := by decide
  have hdescent : baseEnd_161820 < baseStart_161820 := by decide
  rcases family_descends (prefixWord ++ tailWord_161820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161863 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 4, 3]
def baseStart_161863 : Nat := 118140960795 + 161863 * 2 ^ 59
def prefixEnd_161863 : Nat := 4983230072969 + 3 ^ 40 * 161863 * 2
def baseEnd_161863 : Nat := 55409012785870295978741

theorem tailTrace_161863 : CollatzResearch.WordTrace tailWord_161863 prefixEnd_161863 55409012785870295978741 := by
  unfold tailWord_161863
  simp only [CollatzResearch.WordTrace]
  refine ⟨5903628612605469844658243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3935752408403646563105495 5903628612605469844658243)
  ·
    refine ⟨8855442918908204766987365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5903628612605469844658243 8855442918908204766987365)
    ·
      refine ⟨1660395547295288393810131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8855442918908204766987365 1660395547295288393810131)
      ·
        refine ⟨2490593320942932590715197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660395547295288393810131 2490593320942932590715197)
        ·
          refine ⟨933972495353599721518199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2490593320942932590715197 933972495353599721518199)
          ·
            refine ⟨1400958743030399582277299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933972495353599721518199 1400958743030399582277299)
            ·
              refine ⟨2101438114545599373415949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1400958743030399582277299 2101438114545599373415949)
              ·
                refine ⟨788039292954599765030981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2101438114545599373415949 788039292954599765030981)
                ·
                  refine ⟨147757367428987455943309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 788039292954599765030981 147757367428987455943309)
                  ·
                    refine ⟨55409012785870295978741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 147757367428987455943309 55409012785870295978741)
                    ·
                      rfl

theorem cell22_161863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_161863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161863 prefixEnd_161863 := by exact prefixLift 161863
  have htrace : WordTrace (prefixWord ++ tailWord_161863) baseStart_161863 baseEnd_161863 := by
    simpa [prefixWord, tailWord_161863, baseEnd_161863] using wordTrace_append hprefix tailTrace_161863
  have hstable : (prefixWord ++ tailWord_161863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161863).length < 2 ^ (prefixWord ++ tailWord_161863).sum := by decide
  have hdescent : baseEnd_161863 < baseStart_161863 := by decide
  rcases family_descends (prefixWord ++ tailWord_161863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161865 : List Nat := [1, 2, 1, 1, 2, 2, 7, 2, 4]
def baseStart_161865 : Nat := 118140960795 + 161865 * 2 ^ 59
def prefixEnd_161865 : Nat := 4983230072969 + 3 ^ 40 * 161865 * 2
def baseEnd_161865 : Nat := 18469899142247652476245

theorem tailTrace_161865 : CollatzResearch.WordTrace tailWord_161865 prefixEnd_161865 18469899142247652476245 := by
  unfold tailWord_161865
  simp only [CollatzResearch.WordTrace]
  refine ⟨5903701558598224186231049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3935801039065482790820699 5903701558598224186231049)
  ·
    refine ⟨4427776168948668139673287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5903701558598224186231049 4427776168948668139673287)
    ·
      refine ⟨6641664253423002209509931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4427776168948668139673287 6641664253423002209509931)
      ·
        refine ⟨9962496380134503314264897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6641664253423002209509931 9962496380134503314264897)
        ·
          refine ⟨7471872285100877485698673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9962496380134503314264897 7471872285100877485698673)
          ·
            refine ⟨5603904213825658114274005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7471872285100877485698673 5603904213825658114274005)
            ·
              refine ⟨131341505011538862053297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5603904213825658114274005 131341505011538862053297)
              ·
                refine ⟨98506128758654146539973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131341505011538862053297 98506128758654146539973)
                ·
                  refine ⟨18469899142247652476245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98506128758654146539973 18469899142247652476245)
                  ·
                    rfl

theorem cell22_161865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 4].length) (baseStart_161865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161865 prefixEnd_161865 := by exact prefixLift 161865
  have htrace : WordTrace (prefixWord ++ tailWord_161865) baseStart_161865 baseEnd_161865 := by
    simpa [prefixWord, tailWord_161865, baseEnd_161865] using wordTrace_append hprefix tailTrace_161865
  have hstable : (prefixWord ++ tailWord_161865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161865).length < 2 ^ (prefixWord ++ tailWord_161865).sum := by decide
  have hdescent : baseEnd_161865 < baseStart_161865 := by decide
  rcases family_descends (prefixWord ++ tailWord_161865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161880 : List Nat := [2, 1, 2, 2, 1, 5, 1, 3, 2, 3]
def baseStart_161880 : Nat := 118140960795 + 161880 * 2 ^ 59
def prefixEnd_161880 : Nat := 4983230072969 + 3 ^ 40 * 161880 * 2
def baseEnd_161880 : Nat := 55414832233287918303689

theorem tailTrace_161880 : CollatzResearch.WordTrace tailWord_161880 prefixEnd_161880 55414832233287918303689 := by
  unfold tailWord_161880
  simp only [CollatzResearch.WordTrace]
  refine ⟨2952124326771940874013547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3936165769029254498684729 2952124326771940874013547)
  ·
    refine ⟨4428186490157911311020321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2952124326771940874013547 4428186490157911311020321)
    ·
      refine ⟨3321139867618433483265241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4428186490157911311020321 3321139867618433483265241)
      ·
        refine ⟨2490854900713825112448931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3321139867618433483265241 2490854900713825112448931)
        ·
          refine ⟨3736282351070737668673397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2490854900713825112448931 3736282351070737668673397)
          ·
            refine ⟨350276470412881656438131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3736282351070737668673397 350276470412881656438131)
            ·
              refine ⟨525414705619322484657197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350276470412881656438131 525414705619322484657197)
              ·
                refine ⟨197030514607245931746449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 525414705619322484657197 197030514607245931746449)
                ·
                  refine ⟨147772885955434448809837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197030514607245931746449 147772885955434448809837)
                  ·
                    refine ⟨55414832233287918303689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 147772885955434448809837 55414832233287918303689)
                    ·
                      rfl

theorem cell22_161880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_161880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161880 prefixEnd_161880 := by exact prefixLift 161880
  have htrace : WordTrace (prefixWord ++ tailWord_161880) baseStart_161880 baseEnd_161880 := by
    simpa [prefixWord, tailWord_161880, baseEnd_161880] using wordTrace_append hprefix tailTrace_161880
  have hstable : (prefixWord ++ tailWord_161880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161880).length < 2 ^ (prefixWord ++ tailWord_161880).sum := by decide
  have hdescent : baseEnd_161880 < baseStart_161880 := by decide
  rcases family_descends (prefixWord ++ tailWord_161880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161891 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 2, 7]
def baseStart_161891 : Nat := 118140960795 + 161891 * 2 ^ 59
def prefixEnd_161891 : Nat := 4983230072969 + 3 ^ 40 * 161891 * 2
def baseEnd_161891 : Nat := 55418597758087556278655

theorem tailTrace_161891 : CollatzResearch.WordTrace tailWord_161891 prefixEnd_161891 55418597758087556278655 := by
  unfold tailWord_161891
  simp only [CollatzResearch.WordTrace]
  refine ⟨5904649856504030626677527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3936433237669353751118351 5904649856504030626677527)
  ·
    refine ⟨8856974784756045940016291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5904649856504030626677527 8856974784756045940016291)
    ·
      refine ⟨13285462177134068910024437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8856974784756045940016291 13285462177134068910024437)
      ·
        refine ⟨1245512079106318960314791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13285462177134068910024437 1245512079106318960314791)
        ·
          refine ⟨1868268118659478440472187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245512079106318960314791 1868268118659478440472187)
          ·
            refine ⟨2802402177989217660708281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868268118659478440472187 2802402177989217660708281)
            ·
              refine ⟨2101801633491913245531211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2802402177989217660708281 2101801633491913245531211)
              ·
                refine ⟨3152702450237869868296817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2101801633491913245531211 3152702450237869868296817)
                ·
                  refine ⟨2364526837678402401222613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3152702450237869868296817 2364526837678402401222613)
                  ·
                    refine ⟨55418597758087556278655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2364526837678402401222613 55418597758087556278655)
                    ·
                      rfl

theorem cell22_161891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 7].length) (baseStart_161891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_161891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_161891 prefixEnd_161891 := by exact prefixLift 161891
  have htrace : WordTrace (prefixWord ++ tailWord_161891) baseStart_161891 baseEnd_161891 := by
    simpa [prefixWord, tailWord_161891, baseEnd_161891] using wordTrace_append hprefix tailTrace_161891
  have hstable : (prefixWord ++ tailWord_161891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161891).length < 2 ^ (prefixWord ++ tailWord_161891).sum := by decide
  have hdescent : baseEnd_161891 < baseStart_161891 := by decide
  rcases family_descends (prefixWord ++ tailWord_161891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162002 : List Nat := [3, 2, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_162002 : Nat := 118140960795 + 162002 * 2 ^ 59
def prefixEnd_162002 : Nat := 4983230072969 + 3 ^ 40 * 162002 * 2
def baseEnd_162002 : Nat := 55456595326520266753315

theorem tailTrace_162002 : CollatzResearch.WordTrace tailWord_162002 prefixEnd_162002 55456595326520266753315 := by
  unfold tailWord_162002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1477174589775474145992065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3939132239401264389312173 1477174589775474145992065)
  ·
    refine ⟨1107880942331605609494049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1477174589775474145992065 1107880942331605609494049)
    ·
      refine ⟨830910706748704207120537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1107880942331605609494049 830910706748704207120537)
      ·
        refine ⟨623183030061528155340403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 830910706748704207120537 623183030061528155340403)
        ·
          refine ⟨934774545092292233010605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623183030061528155340403 934774545092292233010605)
          ·
            refine ⟨350540454409609587378977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 934774545092292233010605 350540454409609587378977)
            ·
              refine ⟨262905340807207190534233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 350540454409609587378977 262905340807207190534233)
              ·
                refine ⟨197179005605405392900675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262905340807207190534233 197179005605405392900675)
                ·
                  refine ⟨295768508408108089351013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197179005605405392900675 295768508408108089351013)
                  ·
                    refine ⟨55456595326520266753315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 295768508408108089351013 55456595326520266753315)
                    ·
                      rfl

theorem cell22_162002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_162002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162002 prefixEnd_162002 := by exact prefixLift 162002
  have htrace : WordTrace (prefixWord ++ tailWord_162002) baseStart_162002 baseEnd_162002 := by
    simpa [prefixWord, tailWord_162002, baseEnd_162002] using wordTrace_append hprefix tailTrace_162002
  have hstable : (prefixWord ++ tailWord_162002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162002).length < 2 ^ (prefixWord ++ tailWord_162002).sum := by decide
  have hdescent : baseEnd_162002 < baseStart_162002 := by decide
  rcases family_descends (prefixWord ++ tailWord_162002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162034 : List Nat := [3, 2, 1, 3, 2, 2, 3, 2, 4]
def baseStart_162034 : Nat := 118140960795 + 162034 * 2 ^ 59
def prefixEnd_162034 : Nat := 4983230072969 + 3 ^ 40 * 162034 * 2
def baseEnd_162034 : Nat := 18489183193494283317739

theorem tailTrace_162034 : CollatzResearch.WordTrace tailWord_162034 prefixEnd_162034 18489183193494283317739 := by
  unfold tailWord_162034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1477466373746491512283289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3939910329990644032755437 1477466373746491512283289)
  ·
    refine ⟨1108099780309868634212467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1477466373746491512283289 1108099780309868634212467)
    ·
      refine ⟨1662149670464802951318701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1108099780309868634212467 1662149670464802951318701)
      ·
        refine ⟨623306126424301106744513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1662149670464802951318701 623306126424301106744513)
        ·
          refine ⟨467479594818225830058385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 623306126424301106744513 467479594818225830058385)
          ·
            refine ⟨350609696113669372543789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 467479594818225830058385 350609696113669372543789)
            ·
              refine ⟨131478636042626014703921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350609696113669372543789 131478636042626014703921)
              ·
                refine ⟨98608977031969511027941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131478636042626014703921 98608977031969511027941)
                ·
                  refine ⟨18489183193494283317739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98608977031969511027941 18489183193494283317739)
                  ·
                    rfl

theorem cell22_162034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_162034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162034 prefixEnd_162034 := by exact prefixLift 162034
  have htrace : WordTrace (prefixWord ++ tailWord_162034) baseStart_162034 baseEnd_162034 := by
    simpa [prefixWord, tailWord_162034, baseEnd_162034] using wordTrace_append hprefix tailTrace_162034
  have hstable : (prefixWord ++ tailWord_162034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162034).length < 2 ^ (prefixWord ++ tailWord_162034).sum := by decide
  have hdescent : baseEnd_162034 < baseStart_162034 := by decide
  rcases family_descends (prefixWord ++ tailWord_162034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162060 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 5, 3]
def baseStart_162060 : Nat := 118140960795 + 162060 * 2 ^ 59
def prefixEnd_162060 : Nat := 4983230072969 + 3 ^ 40 * 162060 * 2
def baseEnd_162060 : Nat := 55476449911827448803137

theorem tailTrace_162060 : CollatzResearch.WordTrace tailWord_162060 prefixEnd_162060 55476449911827448803137 := by
  unfold tailWord_162060
  simp only [CollatzResearch.WordTrace]
  refine ⟨2955406896445886244789817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3940542528594514993053089 2955406896445886244789817)
  ·
    refine ⟨2216555172334414683592363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2955406896445886244789817 2216555172334414683592363)
    ·
      refine ⟨3324832758501622025388545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2216555172334414683592363 3324832758501622025388545)
      ·
        refine ⟨2493624568876216519041409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3324832758501622025388545 2493624568876216519041409)
        ·
          refine ⟨1870218426657162389281057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2493624568876216519041409 1870218426657162389281057)
          ·
            refine ⟨1402663819992871791960793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1870218426657162389281057 1402663819992871791960793)
            ·
              refine ⟨1051997864994653843970595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1402663819992871791960793 1051997864994653843970595)
              ·
                refine ⟨1577996797491980765955893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051997864994653843970595 1577996797491980765955893)
                ·
                  refine ⟨147937199764873196808365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1577996797491980765955893 147937199764873196808365)
                  ·
                    refine ⟨55476449911827448803137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 147937199764873196808365 55476449911827448803137)
                    ·
                      rfl

theorem cell22_162060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_162060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162060 prefixEnd_162060 := by exact prefixLift 162060
  have htrace : WordTrace (prefixWord ++ tailWord_162060) baseStart_162060 baseEnd_162060 := by
    simpa [prefixWord, tailWord_162060, baseEnd_162060] using wordTrace_append hprefix tailTrace_162060
  have hstable : (prefixWord ++ tailWord_162060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162060).length < 2 ^ (prefixWord ++ tailWord_162060).sum := by decide
  have hdescent : baseEnd_162060 < baseStart_162060 := by decide
  rcases family_descends (prefixWord ++ tailWord_162060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162105 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 1, 7]
def baseStart_162105 : Nat := 118140960795 + 162105 * 2 ^ 59
def prefixEnd_162105 : Nat := 4983230072969 + 3 ^ 40 * 162105 * 2
def baseEnd_162105 : Nat := 55491854331462331427999

theorem tailTrace_162105 : CollatzResearch.WordTrace tailWord_162105 prefixEnd_162105 55491854331462331427999 := by
  unfold tailWord_162105
  simp only [CollatzResearch.WordTrace]
  refine ⟨5912455077728745174967769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3941636718485830116645179 5912455077728745174967769)
  ·
    refine ⟨4434341308296558881225827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5912455077728745174967769 4434341308296558881225827)
    ·
      refine ⟨6651511962444838321838741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4434341308296558881225827 6651511962444838321838741)
      ·
        refine ⟨311789623239601796336191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6651511962444838321838741 311789623239601796336191)
        ·
          refine ⟨467684434859402694504287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311789623239601796336191 467684434859402694504287)
          ·
            refine ⟨701526652289104041756431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467684434859402694504287 701526652289104041756431)
            ·
              refine ⟨1052289978433656062634647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701526652289104041756431 1052289978433656062634647)
              ·
                refine ⟨1578434967650484093951971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052289978433656062634647 1578434967650484093951971)
                ·
                  refine ⟨2367652451475726140927957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1578434967650484093951971 2367652451475726140927957)
                  ·
                    refine ⟨55491854331462331427999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2367652451475726140927957 55491854331462331427999)
                    ·
                      rfl

theorem cell22_162105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_162105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162105 prefixEnd_162105 := by exact prefixLift 162105
  have htrace : WordTrace (prefixWord ++ tailWord_162105) baseStart_162105 baseEnd_162105 := by
    simpa [prefixWord, tailWord_162105, baseEnd_162105] using wordTrace_append hprefix tailTrace_162105
  have hstable : (prefixWord ++ tailWord_162105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162105).length < 2 ^ (prefixWord ++ tailWord_162105).sum := by decide
  have hdescent : baseEnd_162105 < baseStart_162105 := by decide
  rcases family_descends (prefixWord ++ tailWord_162105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162120 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 3, 4]
def baseStart_162120 : Nat := 118140960795 + 162120 * 2 ^ 59
def prefixEnd_162120 : Nat := 4983230072969 + 3 ^ 40 * 162120 * 2
def baseEnd_162120 : Nat := 55496989138007292302953

theorem tailTrace_162120 : CollatzResearch.WordTrace tailWord_162120 prefixEnd_162120 55496989138007292302953 := by
  unfold tailWord_162120
  simp only [CollatzResearch.WordTrace]
  refine ⟨2956501086337201368381907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3942001448449601824509209 2956501086337201368381907)
  ·
    refine ⟨4434751629505802052572861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2956501086337201368381907 4434751629505802052572861)
    ·
      refine ⟨1663031861064675769714823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4434751629505802052572861 1663031861064675769714823)
      ·
        refine ⟨2494547791597013654572235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1663031861064675769714823 2494547791597013654572235)
        ·
          refine ⟨3741821687395520481858353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2494547791597013654572235 3741821687395520481858353)
          ·
            refine ⟨2806366265546640361393765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3741821687395520481858353 2806366265546640361393765)
            ·
              refine ⟨526193674789995067761331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2806366265546640361393765 526193674789995067761331)
              ·
                refine ⟨789290512184992601641997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526193674789995067761331 789290512184992601641997)
                ·
                  refine ⟨295983942069372225615749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 789290512184992601641997 295983942069372225615749)
                  ·
                    refine ⟨55496989138007292302953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 295983942069372225615749 55496989138007292302953)
                    ·
                      rfl

theorem cell22_162120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_162120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162120 prefixEnd_162120 := by exact prefixLift 162120
  have htrace : WordTrace (prefixWord ++ tailWord_162120) baseStart_162120 baseEnd_162120 := by
    simpa [prefixWord, tailWord_162120, baseEnd_162120] using wordTrace_append hprefix tailTrace_162120
  have hstable : (prefixWord ++ tailWord_162120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162120).length < 2 ^ (prefixWord ++ tailWord_162120).sum := by decide
  have hdescent : baseEnd_162120 < baseStart_162120 := by decide
  rcases family_descends (prefixWord ++ tailWord_162120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162152 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 6]
def baseStart_162152 : Nat := 118140960795 + 162152 * 2 ^ 59
def prefixEnd_162152 : Nat := 4983230072969 + 3 ^ 40 * 162152 * 2
def baseEnd_162152 : Nat := 18502647797323291834285

theorem tailTrace_162152 : CollatzResearch.WordTrace tailWord_162152 prefixEnd_162152 18502647797323291834285 := by
  unfold tailWord_162152
  simp only [CollatzResearch.WordTrace]
  refine ⟨2957084654279236100964355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3942779539038981467952473 2957084654279236100964355)
  ·
    refine ⟨4435626981418854151446533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2957084654279236100964355 4435626981418854151446533)
    ·
      refine ⟨831680059016035153396225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4435626981418854151446533 831680059016035153396225)
      ·
        refine ⟨623760044262026365047169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 831680059016035153396225 623760044262026365047169)
        ·
          refine ⟨467820033196519773785377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 623760044262026365047169 467820033196519773785377)
          ·
            refine ⟨350865024897389830339033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 467820033196519773785377 350865024897389830339033)
            ·
              refine ⟨263148768673042372754275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 350865024897389830339033 263148768673042372754275)
              ·
                refine ⟨394723153009563559131413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263148768673042372754275 394723153009563559131413)
                ·
                  refine ⟨18502647797323291834285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 394723153009563559131413 18502647797323291834285)
                  ·
                    rfl

theorem cell22_162152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 6].length) (baseStart_162152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162152 prefixEnd_162152 := by exact prefixLift 162152
  have htrace : WordTrace (prefixWord ++ tailWord_162152) baseStart_162152 baseEnd_162152 := by
    simpa [prefixWord, tailWord_162152, baseEnd_162152] using wordTrace_append hprefix tailTrace_162152
  have hstable : (prefixWord ++ tailWord_162152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162152).length < 2 ^ (prefixWord ++ tailWord_162152).sum := by decide
  have hdescent : baseEnd_162152 < baseStart_162152 := by decide
  rcases family_descends (prefixWord ++ tailWord_162152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162180 : List Nat := [2, 3, 2, 1, 1, 2, 3, 8]
def baseStart_162180 : Nat := 118140960795 + 162180 * 2 ^ 59
def prefixEnd_162180 : Nat := 4983230072969 + 3 ^ 40 * 162180 * 2
def baseEnd_162180 : Nat := 6168614262687459533641

theorem tailTrace_162180 : CollatzResearch.WordTrace tailWord_162180 prefixEnd_162180 6168614262687459533641 := by
  unfold tailWord_162180
  simp only [CollatzResearch.WordTrace]
  refine ⟨2957595276228516491973997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3943460368304688655965329 2957595276228516491973997)
  ·
    refine ⟨1109098228585693684490249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2957595276228516491973997 1109098228585693684490249)
    ·
      refine ⟨831823671439270263367687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1109098228585693684490249 831823671439270263367687)
      ·
        refine ⟨1247735507158905395051531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831823671439270263367687 1247735507158905395051531)
        ·
          refine ⟨1871603260738358092577297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1247735507158905395051531 1871603260738358092577297)
          ·
            refine ⟨1403702445553768569432973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1871603260738358092577297 1403702445553768569432973)
            ·
              refine ⟨526388417082663213537365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1403702445553768569432973 526388417082663213537365)
              ·
                refine ⟨6168614262687459533641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 526388417082663213537365 6168614262687459533641)
                ·
                  rfl

theorem cell22_162180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 8].length) (baseStart_162180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162180 prefixEnd_162180 := by exact prefixLift 162180
  have htrace : WordTrace (prefixWord ++ tailWord_162180) baseStart_162180 baseEnd_162180 := by
    simpa [prefixWord, tailWord_162180, baseEnd_162180] using wordTrace_append hprefix tailTrace_162180
  have hstable : (prefixWord ++ tailWord_162180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162180).length < 2 ^ (prefixWord ++ tailWord_162180).sum := by decide
  have hdescent : baseEnd_162180 < baseStart_162180 := by decide
  rcases family_descends (prefixWord ++ tailWord_162180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162240 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 4, 5]
def baseStart_162240 : Nat := 118140960795 + 162240 * 2 ^ 59
def prefixEnd_162240 : Nat := 4983230072969 + 3 ^ 40 * 162240 * 2
def baseEnd_162240 : Nat := 55538067590366979302585

theorem tailTrace_162240 : CollatzResearch.WordTrace tailWord_162240 prefixEnd_162240 55538067590366979302585 := by
  unfold tailWord_162240
  simp only [CollatzResearch.WordTrace]
  refine ⟨2958689466119831615566087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3944919288159775487421449 2958689466119831615566087)
  ·
    refine ⟨4438034199179747423349131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2958689466119831615566087 4438034199179747423349131)
    ·
      refine ⟨6657051298769621135023697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4438034199179747423349131 6657051298769621135023697)
      ·
        refine ⟨4992788474077215851267773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6657051298769621135023697 4992788474077215851267773)
        ·
          refine ⟨1872295677778955944225415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4992788474077215851267773 1872295677778955944225415)
          ·
            refine ⟨2808443516668433916338123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1872295677778955944225415 2808443516668433916338123)
            ·
              refine ⟨4212665275002650874507185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2808443516668433916338123 4212665275002650874507185)
              ·
                refine ⟨3159498956251988155880389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4212665275002650874507185 3159498956251988155880389)
                ·
                  refine ⟨592406054297247779227573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3159498956251988155880389 592406054297247779227573)
                  ·
                    refine ⟨55538067590366979302585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 592406054297247779227573 55538067590366979302585)
                    ·
                      rfl

theorem cell22_162240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_162240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162240 prefixEnd_162240 := by exact prefixLift 162240
  have htrace : WordTrace (prefixWord ++ tailWord_162240) baseStart_162240 baseEnd_162240 := by
    simpa [prefixWord, tailWord_162240, baseEnd_162240] using wordTrace_append hprefix tailTrace_162240
  have hstable : (prefixWord ++ tailWord_162240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162240).length < 2 ^ (prefixWord ++ tailWord_162240).sum := by decide
  have hdescent : baseEnd_162240 < baseStart_162240 := by decide
  rcases family_descends (prefixWord ++ tailWord_162240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162310 : List Nat := [6, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_162310 : Nat := 118140960795 + 162310 * 2 ^ 59
def prefixEnd_162310 : Nat := 4983230072969 + 3 ^ 40 * 162310 * 2
def baseEnd_162310 : Nat := 18520676673636710017457

theorem tailTrace_162310 : CollatzResearch.WordTrace tailWord_162310 prefixEnd_162310 18520676673636710017457 := by
  unfold tailWord_162310
  simp only [CollatzResearch.WordTrace]
  refine ⟨184997876312064537068137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3946621361324043457453589 184997876312064537068137)
  ·
    refine ⟨138748407234048402801103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184997876312064537068137 138748407234048402801103)
    ·
      refine ⟨208122610851072604201655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138748407234048402801103 208122610851072604201655)
      ·
        refine ⟨312183916276608906302483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208122610851072604201655 312183916276608906302483)
        ·
          refine ⟨468275874414913359453725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312183916276608906302483 468275874414913359453725)
          ·
            refine ⟨175603452905592509795147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 468275874414913359453725 175603452905592509795147)
            ·
              refine ⟨263405179358388764692721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175603452905592509795147 263405179358388764692721)
              ·
                refine ⟨197553884518791573519541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263405179358388764692721 197553884518791573519541)
                ·
                  refine ⟨18520676673636710017457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 197553884518791573519541 18520676673636710017457)
                  ·
                    rfl

theorem cell22_162310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_162310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162310 prefixEnd_162310 := by exact prefixLift 162310
  have htrace : WordTrace (prefixWord ++ tailWord_162310) baseStart_162310 baseEnd_162310 := by
    simpa [prefixWord, tailWord_162310, baseEnd_162310] using wordTrace_append hprefix tailTrace_162310
  have hstable : (prefixWord ++ tailWord_162310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162310).length < 2 ^ (prefixWord ++ tailWord_162310).sum := by decide
  have hdescent : baseEnd_162310 < baseStart_162310 := by decide
  rcases family_descends (prefixWord ++ tailWord_162310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162336 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 1, 5]
def baseStart_162336 : Nat := 118140960795 + 162336 * 2 ^ 59
def prefixEnd_162336 : Nat := 4983230072969 + 3 ^ 40 * 162336 * 2
def baseEnd_162336 : Nat := 55570930352254728902291

theorem tailTrace_162336 : CollatzResearch.WordTrace tailWord_162336 prefixEnd_162336 55570930352254728902291 := by
  unfold tailWord_162336
  simp only [CollatzResearch.WordTrace]
  refine ⟨2960440169945935813313431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3947253559927914417751241 2960440169945935813313431)
  ·
    refine ⟨4440660254918903719970147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2960440169945935813313431 4440660254918903719970147)
    ·
      refine ⟨6660990382378355579955221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4440660254918903719970147 6660990382378355579955221)
      ·
        refine ⟨312233924173985417810401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6660990382378355579955221 312233924173985417810401)
        ·
          refine ⟨234175443130489063357801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312233924173985417810401 234175443130489063357801)
          ·
            refine ⟨175631582347866797518351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234175443130489063357801 175631582347866797518351)
            ·
              refine ⟨263447373521800196277527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175631582347866797518351 263447373521800196277527)
              ·
                refine ⟨395171060282700294416291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263447373521800196277527 395171060282700294416291)
                ·
                  refine ⟨592756590424050441624437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395171060282700294416291 592756590424050441624437)
                  ·
                    refine ⟨55570930352254728902291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 592756590424050441624437 55570930352254728902291)
                    ·
                      rfl

theorem cell22_162336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 1, 5].length) (baseStart_162336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162336 prefixEnd_162336 := by exact prefixLift 162336
  have htrace : WordTrace (prefixWord ++ tailWord_162336) baseStart_162336 baseEnd_162336 := by
    simpa [prefixWord, tailWord_162336, baseEnd_162336] using wordTrace_append hprefix tailTrace_162336
  have hstable : (prefixWord ++ tailWord_162336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162336).length < 2 ^ (prefixWord ++ tailWord_162336).sum := by decide
  have hdescent : baseEnd_162336 < baseStart_162336 := by decide
  rcases family_descends (prefixWord ++ tailWord_162336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162366 : List Nat := [4, 2, 1, 4, 1, 2, 8]
def baseStart_162366 : Nat := 118140960795 + 162366 * 2 ^ 59
def prefixEnd_162366 : Nat := 4983230072969 + 3 ^ 40 * 162366 * 2
def baseEnd_162366 : Nat := 2058562961679431505637

theorem tailTrace_162366 : CollatzResearch.WordTrace tailWord_162366 prefixEnd_162366 2058562961679431505637 := by
  unfold tailWord_162366
  simp only [CollatzResearch.WordTrace]
  refine ⟨740246816222898343777369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3947983019855457833479301 740246816222898343777369)
  ·
    refine ⟨555185112167173757833027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 740246816222898343777369 555185112167173757833027)
    ·
      refine ⟨832777668250760636749541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 555185112167173757833027 832777668250760636749541)
      ·
        refine ⟨156145812797017619390539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 832777668250760636749541 156145812797017619390539)
        ·
          refine ⟨234218719195526429085809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156145812797017619390539 234218719195526429085809)
          ·
            refine ⟨175664039396644821814357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234218719195526429085809 175664039396644821814357)
            ·
              refine ⟨2058562961679431505637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 175664039396644821814357 2058562961679431505637)
              ·
                rfl

theorem cell22_162366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 8].length) (baseStart_162366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162366 prefixEnd_162366 := by exact prefixLift 162366
  have htrace : WordTrace (prefixWord ++ tailWord_162366) baseStart_162366 baseEnd_162366 := by
    simpa [prefixWord, tailWord_162366, baseEnd_162366] using wordTrace_append hprefix tailTrace_162366
  have hstable : (prefixWord ++ tailWord_162366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162366).length < 2 ^ (prefixWord ++ tailWord_162366).sum := by decide
  have hdescent : baseEnd_162366 < baseStart_162366 := by decide
  rcases family_descends (prefixWord ++ tailWord_162366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162372 : List Nat := [2, 3, 5, 1, 1, 1, 3, 2, 4]
def baseStart_162372 : Nat := 118140960795 + 162372 * 2 ^ 59
def prefixEnd_162372 : Nat := 4983230072969 + 3 ^ 40 * 162372 * 2
def baseEnd_162372 : Nat := 18527751295987545000727

theorem tailTrace_162372 : CollatzResearch.WordTrace tailWord_162372 prefixEnd_162372 18527751295987545000727 := by
  unfold tailWord_162372
  simp only [CollatzResearch.WordTrace]
  refine ⟨2961096683880724887468685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3948128911840966516624913 2961096683880724887468685)
  ·
    refine ⟨1110411256455271832800757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2961096683880724887468685 1110411256455271832800757)
    ·
      refine ⟨104101055292681734325071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1110411256455271832800757 104101055292681734325071)
      ·
        refine ⟨156151582939022601487607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104101055292681734325071 156151582939022601487607)
        ·
          refine ⟨234227374408533902231411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156151582939022601487607 234227374408533902231411)
          ·
            refine ⟨351341061612800853347117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234227374408533902231411 351341061612800853347117)
            ·
              refine ⟨131752898104800320005169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 351341061612800853347117 131752898104800320005169)
              ·
                refine ⟨98814673578600240003877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131752898104800320005169 98814673578600240003877)
                ·
                  refine ⟨18527751295987545000727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98814673578600240003877 18527751295987545000727)
                  ·
                    rfl

theorem cell22_162372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_162372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162372 prefixEnd_162372 := by exact prefixLift 162372
  have htrace : WordTrace (prefixWord ++ tailWord_162372) baseStart_162372 baseEnd_162372 := by
    simpa [prefixWord, tailWord_162372, baseEnd_162372] using wordTrace_append hprefix tailTrace_162372
  have hstable : (prefixWord ++ tailWord_162372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162372).length < 2 ^ (prefixWord ++ tailWord_162372).sum := by decide
  have hdescent : baseEnd_162372 < baseStart_162372 := by decide
  rcases family_descends (prefixWord ++ tailWord_162372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162392 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 2, 5]
def baseStart_162392 : Nat := 118140960795 + 162392 * 2 ^ 59
def prefixEnd_162392 : Nat := 4983230072969 + 3 ^ 40 * 162392 * 2
def baseEnd_162392 : Nat := 55590100296689249502119

theorem tailTrace_162392 : CollatzResearch.WordTrace tailWord_162392 prefixEnd_162392 55590100296689249502119 := by
  unfold tailWord_162392
  simp only [CollatzResearch.WordTrace]
  refine ⟨2961461413844496595332715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3948615218459328793776953 2961461413844496595332715)
  ·
    refine ⟨4442192120766744892999073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2961461413844496595332715 4442192120766744892999073)
    ·
      refine ⟨3331644090575058669749305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4442192120766744892999073 3331644090575058669749305)
      ·
        refine ⟨2498733067931294002311979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3331644090575058669749305 2498733067931294002311979)
        ·
          refine ⟨3748099601896941003467969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498733067931294002311979 3748099601896941003467969)
          ·
            refine ⟨2811074701422705752600977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3748099601896941003467969 2811074701422705752600977)
            ·
              refine ⟨2108306026067029314450733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2811074701422705752600977 2108306026067029314450733)
              ·
                refine ⟨790614759775135992919025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2108306026067029314450733 790614759775135992919025)
                ·
                  refine ⟨592961069831351994689269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 790614759775135992919025 592961069831351994689269)
                  ·
                    refine ⟨55590100296689249502119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 592961069831351994689269 55590100296689249502119)
                    ·
                      rfl

theorem cell22_162392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_162392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162392 prefixEnd_162392 := by exact prefixLift 162392
  have htrace : WordTrace (prefixWord ++ tailWord_162392) baseStart_162392 baseEnd_162392 := by
    simpa [prefixWord, tailWord_162392, baseEnd_162392] using wordTrace_append hprefix tailTrace_162392
  have hstable : (prefixWord ++ tailWord_162392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162392).length < 2 ^ (prefixWord ++ tailWord_162392).sum := by decide
  have hdescent : baseEnd_162392 < baseStart_162392 := by decide
  rcases family_descends (prefixWord ++ tailWord_162392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162529 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 7]
def baseStart_162529 : Nat := 118140960795 + 162529 * 2 ^ 59
def prefixEnd_162529 : Nat := 4983230072969 + 3 ^ 40 * 162529 * 2
def baseEnd_162529 : Nat := 18545666065488852942233

theorem tailTrace_162529 : CollatzResearch.WordTrace tailWord_162529 prefixEnd_162529 18545666065488852942233 := by
  unfold tailWord_162529
  simp only [CollatzResearch.WordTrace]
  refine ⟨5927919628192665588402641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3951946418795110392268427 5927919628192665588402641)
  ·
    refine ⟨4445939721144499191301981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5927919628192665588402641 4445939721144499191301981)
    ·
      refine ⟨1667227395429187196738243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4445939721144499191301981 1667227395429187196738243)
      ·
        refine ⟨2500841093143780795107365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1667227395429187196738243 2500841093143780795107365)
        ·
          refine ⟨468907704964458899082631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2500841093143780795107365 468907704964458899082631)
          ·
            refine ⟨703361557446688348623947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468907704964458899082631 703361557446688348623947)
            ·
              refine ⟨1055042336170032522935921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703361557446688348623947 1055042336170032522935921)
              ·
                refine ⟨791281752127524392201941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1055042336170032522935921 791281752127524392201941)
                ·
                  refine ⟨18545666065488852942233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 791281752127524392201941 18545666065488852942233)
                  ·
                    rfl

theorem cell22_162529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 7].length) (baseStart_162529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162529 prefixEnd_162529 := by exact prefixLift 162529
  have htrace : WordTrace (prefixWord ++ tailWord_162529) baseStart_162529 baseEnd_162529 := by
    simpa [prefixWord, tailWord_162529, baseEnd_162529] using wordTrace_append hprefix tailTrace_162529
  have hstable : (prefixWord ++ tailWord_162529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162529).length < 2 ^ (prefixWord ++ tailWord_162529).sum := by decide
  have hdescent : baseEnd_162529 < baseStart_162529 := by decide
  rcases family_descends (prefixWord ++ tailWord_162529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162559 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 3, 4]
def baseStart_162559 : Nat := 118140960795 + 162559 * 2 ^ 59
def prefixEnd_162559 : Nat := 4983230072969 + 3 ^ 40 * 162559 * 2
def baseEnd_162559 : Nat := 55647267809556480576607

theorem tailTrace_162559 : CollatzResearch.WordTrace tailWord_162559 prefixEnd_162559 55647267809556480576607 := by
  unfold tailWord_162559
  simp only [CollatzResearch.WordTrace]
  refine ⟨5929013818083980711994731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3952675878722653807996487 5929013818083980711994731)
  ·
    refine ⟨8893520727125971067992097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5929013818083980711994731 8893520727125971067992097)
    ·
      refine ⟨6670140545344478300994073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8893520727125971067992097 6670140545344478300994073)
      ·
        refine ⟨5002605409008358725745555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6670140545344478300994073 5002605409008358725745555)
        ·
          refine ⟨7503908113512538088618333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5002605409008358725745555 7503908113512538088618333)
          ·
            refine ⟨2813965542567201783231875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7503908113512538088618333 2813965542567201783231875)
            ·
              refine ⟨4220948313850802674847813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2813965542567201783231875 4220948313850802674847813)
              ·
                refine ⟨791427808847025501533965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4220948313850802674847813 791427808847025501533965)
                ·
                  refine ⟨296785428317634563075237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791427808847025501533965 296785428317634563075237)
                  ·
                    refine ⟨55647267809556480576607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 296785428317634563075237 55647267809556480576607)
                    ·
                      rfl

theorem cell22_162559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_162559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162559 prefixEnd_162559 := by exact prefixLift 162559
  have htrace : WordTrace (prefixWord ++ tailWord_162559) baseStart_162559 baseEnd_162559 := by
    simpa [prefixWord, tailWord_162559, baseEnd_162559] using wordTrace_append hprefix tailTrace_162559
  have hstable : (prefixWord ++ tailWord_162559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162559).length < 2 ^ (prefixWord ++ tailWord_162559).sum := by decide
  have hdescent : baseEnd_162559 < baseStart_162559 := by decide
  rcases family_descends (prefixWord ++ tailWord_162559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162574 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 8]
def baseStart_162574 : Nat := 118140960795 + 162574 * 2 ^ 59
def prefixEnd_162574 : Nat := 4983230072969 + 3 ^ 40 * 162574 * 2
def baseEnd_162574 : Nat := 18550800872033813817187

theorem tailTrace_162574 : CollatzResearch.WordTrace tailWord_162574 prefixEnd_162574 18550800872033813817187 := by
  unfold tailWord_162574
  simp only [CollatzResearch.WordTrace]
  refine ⟨741195114128704784223847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3953040608686425515860517 741195114128704784223847)
  ·
    refine ⟨1111792671193057176335771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 741195114128704784223847 1111792671193057176335771)
    ·
      refine ⟨1667689006789585764503657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1111792671193057176335771 1667689006789585764503657)
      ·
        refine ⟨1250766755092189323377743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1667689006789585764503657 1250766755092189323377743)
        ·
          refine ⟨1876150132638283985066615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250766755092189323377743 1876150132638283985066615)
          ·
            refine ⟨2814225198957425977599923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1876150132638283985066615 2814225198957425977599923)
            ·
              refine ⟨4221337798436138966399885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2814225198957425977599923 4221337798436138966399885)
              ·
                refine ⟨1583001674413552112399957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4221337798436138966399885 1583001674413552112399957)
                ·
                  refine ⟨18550800872033813817187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1583001674413552112399957 18550800872033813817187)
                  ·
                    rfl

theorem cell22_162574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_162574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162574 prefixEnd_162574 := by exact prefixLift 162574
  have htrace : WordTrace (prefixWord ++ tailWord_162574) baseStart_162574 baseEnd_162574 := by
    simpa [prefixWord, tailWord_162574, baseEnd_162574] using wordTrace_append hprefix tailTrace_162574
  have hstable : (prefixWord ++ tailWord_162574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162574).length < 2 ^ (prefixWord ++ tailWord_162574).sum := by decide
  have hdescent : baseEnd_162574 < baseStart_162574 := by decide
  rcases family_descends (prefixWord ++ tailWord_162574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162593 : List Nat := [1, 2, 3, 2, 1, 2, 5, 1, 1, 4]
def baseStart_162593 : Nat := 118140960795 + 162593 * 2 ^ 59
def prefixEnd_162593 : Nat := 4983230072969 + 3 ^ 40 * 162593 * 2
def baseEnd_162593 : Nat := 55658906704391725226503

theorem tailTrace_162593 : CollatzResearch.WordTrace tailWord_162593 prefixEnd_162593 55658906704391725226503 := by
  unfold tailWord_162593
  simp only [CollatzResearch.WordTrace]
  refine ⟨5930253899960804518732433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3953502599973869679154955 5930253899960804518732433)
  ·
    refine ⟨4447690424970603389049325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5930253899960804518732433 4447690424970603389049325)
    ·
      refine ⟨1667883909363976270893497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4447690424970603389049325 1667883909363976270893497)
      ·
        refine ⟨1250912932022982203170123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1667883909363976270893497 1250912932022982203170123)
        ·
          refine ⟨1876369398034473304755185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250912932022982203170123 1876369398034473304755185)
          ·
            refine ⟨1407277048525854978566389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1876369398034473304755185 1407277048525854978566389)
            ·
              refine ⟨131932223299298904240599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1407277048525854978566389 131932223299298904240599)
              ·
                refine ⟨197898334948948356360899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131932223299298904240599 197898334948948356360899)
                ·
                  refine ⟨296847502423422534541349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197898334948948356360899 296847502423422534541349)
                  ·
                    refine ⟨55658906704391725226503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 296847502423422534541349 55658906704391725226503)
                    ·
                      rfl

theorem cell22_162593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_162593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162593 prefixEnd_162593 := by exact prefixLift 162593
  have htrace : WordTrace (prefixWord ++ tailWord_162593) baseStart_162593 baseEnd_162593 := by
    simpa [prefixWord, tailWord_162593, baseEnd_162593] using wordTrace_append hprefix tailTrace_162593
  have hstable : (prefixWord ++ tailWord_162593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162593).length < 2 ^ (prefixWord ++ tailWord_162593).sum := by decide
  have hdescent : baseEnd_162593 < baseStart_162593 := by decide
  rcases family_descends (prefixWord ++ tailWord_162593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162623 : List Nat := [1, 1, 2, 2, 5, 1, 2, 3, 2, 3]
def baseStart_162623 : Nat := 118140960795 + 162623 * 2 ^ 59
def prefixEnd_162623 : Nat := 4983230072969 + 3 ^ 40 * 162623 * 2
def baseEnd_162623 : Nat := 55669176317481646976411

theorem tailTrace_162623 : CollatzResearch.WordTrace tailWord_162623 prefixEnd_162623 55669176317481646976411 := by
  unfold tailWord_162623
  simp only [CollatzResearch.WordTrace]
  refine ⟨5931348089852119642324523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3954232059901413094883015 5931348089852119642324523)
  ·
    refine ⟨8897022134778179463486785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5931348089852119642324523 8897022134778179463486785)
    ·
      refine ⟨6672766601083634597615089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8897022134778179463486785 6672766601083634597615089)
      ·
        refine ⟨5004574950812725948211317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6672766601083634597615089 5004574950812725948211317)
        ·
          refine ⟨469178901638693057644811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5004574950812725948211317 469178901638693057644811)
          ·
            refine ⟨703768352458039586467217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469178901638693057644811 703768352458039586467217)
            ·
              refine ⟨527826264343529689850413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 703768352458039586467217 527826264343529689850413)
              ·
                refine ⟨197934849128823633693905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 527826264343529689850413 197934849128823633693905)
                ·
                  refine ⟨148451136846617725270429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197934849128823633693905 148451136846617725270429)
                  ·
                    refine ⟨55669176317481646976411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 148451136846617725270429 55669176317481646976411)
                    ·
                      rfl

theorem cell22_162623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 3].length) (baseStart_162623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162623 prefixEnd_162623 := by exact prefixLift 162623
  have htrace : WordTrace (prefixWord ++ tailWord_162623) baseStart_162623 baseEnd_162623 := by
    simpa [prefixWord, tailWord_162623, baseEnd_162623] using wordTrace_append hprefix tailTrace_162623
  have hstable : (prefixWord ++ tailWord_162623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162623).length < 2 ^ (prefixWord ++ tailWord_162623).sum := by decide
  have hdescent : baseEnd_162623 < baseStart_162623 := by decide
  rcases family_descends (prefixWord ++ tailWord_162623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162634 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 1, 9]
def baseStart_162634 : Nat := 118140960795 + 162634 * 2 ^ 59
def prefixEnd_162634 : Nat := 4983230072969 + 3 ^ 40 * 162634 * 2
def baseEnd_162634 : Nat := 55672941842281284951377

theorem tailTrace_162634 : CollatzResearch.WordTrace tailWord_162634 prefixEnd_162634 55672941842281284951377 := by
  unfold tailWord_162634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1482937323203067130243739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3954499528541512347316637 1482937323203067130243739)
  ·
    refine ⟨2224405984804600695365609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1482937323203067130243739 2224405984804600695365609)
    ·
      refine ⟨1668304488603450521524207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2224405984804600695365609 1668304488603450521524207)
      ·
        refine ⟨2502456732905175782286311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1668304488603450521524207 2502456732905175782286311)
        ·
          refine ⟨3753685099357763673429467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2502456732905175782286311 3753685099357763673429467)
          ·
            refine ⟨5630527649036645510144201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3753685099357763673429467 5630527649036645510144201)
            ·
              refine ⟨4222895736777484132608151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5630527649036645510144201 4222895736777484132608151)
              ·
                refine ⟨6334343605166226198912227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4222895736777484132608151 6334343605166226198912227)
                ·
                  refine ⟨9501515407749339298368341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6334343605166226198912227 9501515407749339298368341)
                  ·
                    refine ⟨55672941842281284951377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 9501515407749339298368341 55672941842281284951377)
                    ·
                      rfl

theorem cell22_162634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_162634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162634 prefixEnd_162634 := by exact prefixLift 162634
  have htrace : WordTrace (prefixWord ++ tailWord_162634) baseStart_162634 baseEnd_162634 := by
    simpa [prefixWord, tailWord_162634, baseEnd_162634] using wordTrace_append hprefix tailTrace_162634
  have hstable : (prefixWord ++ tailWord_162634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162634).length < 2 ^ (prefixWord ++ tailWord_162634).sum := by decide
  have hdescent : baseEnd_162634 < baseStart_162634 := by decide
  rcases family_descends (prefixWord ++ tailWord_162634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162668 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 3, 3]
def baseStart_162668 : Nat := 118140960795 + 162668 * 2 ^ 59
def prefixEnd_162668 : Nat := 4983230072969 + 3 ^ 40 * 162668 * 2
def baseEnd_162668 : Nat := 55684580737116529601273

theorem tailTrace_162668 : CollatzResearch.WordTrace tailWord_162668 prefixEnd_162668 55684580737116529601273 := by
  unfold tailWord_162668
  simp only [CollatzResearch.WordTrace]
  refine ⟨2966494687344546163856329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3955326249792728218475105 2966494687344546163856329)
  ·
    refine ⟨2224871015508409622892247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2966494687344546163856329 2224871015508409622892247)
    ·
      refine ⟨3337306523262614434338371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2224871015508409622892247 3337306523262614434338371)
      ·
        refine ⟨5005959784893921651507557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3337306523262614434338371 5005959784893921651507557)
        ·
          refine ⟨938617459667610309657667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5005959784893921651507557 938617459667610309657667)
          ·
            refine ⟨1407926189501415464486501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938617459667610309657667 1407926189501415464486501)
            ·
              refine ⟨263986160531515399591219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1407926189501415464486501 263986160531515399591219)
              ·
                refine ⟨395979240797273099386829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263986160531515399591219 395979240797273099386829)
                ·
                  refine ⟨148492215298977412270061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395979240797273099386829 148492215298977412270061)
                  ·
                    refine ⟨55684580737116529601273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 148492215298977412270061 55684580737116529601273)
                    ·
                      rfl

theorem cell22_162668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_162668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162668 prefixEnd_162668 := by exact prefixLift 162668
  have htrace : WordTrace (prefixWord ++ tailWord_162668) baseStart_162668 baseEnd_162668 := by
    simpa [prefixWord, tailWord_162668, baseEnd_162668] using wordTrace_append hprefix tailTrace_162668
  have hstable : (prefixWord ++ tailWord_162668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162668).length < 2 ^ (prefixWord ++ tailWord_162668).sum := by decide
  have hdescent : baseEnd_162668 < baseStart_162668 := by decide
  rcases family_descends (prefixWord ++ tailWord_162668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162745 : List Nat := [1, 2, 1, 4, 2, 4, 1, 2, 1, 4]
def baseStart_162745 : Nat := 118140960795 + 162745 * 2 ^ 59
def prefixEnd_162745 : Nat := 4983230072969 + 3 ^ 40 * 162745 * 2
def baseEnd_162745 : Nat := 55710939410713995426037

theorem tailTrace_162745 : CollatzResearch.WordTrace tailWord_162745 prefixEnd_162745 55710939410713995426037 := by
  unfold tailWord_162745
  simp only [CollatzResearch.WordTrace]
  refine ⟨5935797795410134478265689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3957198530273422985510459 5935797795410134478265689)
  ·
    refine ⟨4451848346557600858699267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5935797795410134478265689 4451848346557600858699267)
    ·
      refine ⟨6677772519836401288048901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4451848346557600858699267 6677772519836401288048901)
      ·
        refine ⟨1252082347469325241509169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6677772519836401288048901 1252082347469325241509169)
        ·
          refine ⟨939061760601993931131877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1252082347469325241509169 939061760601993931131877)
          ·
            refine ⟨176074080112873862087227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 939061760601993931131877 176074080112873862087227)
            ·
              refine ⟨264111120169310793130841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176074080112873862087227 264111120169310793130841)
              ·
                refine ⟨198083340126983094848131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264111120169310793130841 198083340126983094848131)
                ·
                  refine ⟨297125010190474642272197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198083340126983094848131 297125010190474642272197)
                  ·
                    refine ⟨55710939410713995426037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 297125010190474642272197 55710939410713995426037)
                    ·
                      rfl

theorem cell22_162745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 4].length) (baseStart_162745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162745 prefixEnd_162745 := by exact prefixLift 162745
  have htrace : WordTrace (prefixWord ++ tailWord_162745) baseStart_162745 baseEnd_162745 := by
    simpa [prefixWord, tailWord_162745, baseEnd_162745] using wordTrace_append hprefix tailTrace_162745
  have hstable : (prefixWord ++ tailWord_162745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162745).length < 2 ^ (prefixWord ++ tailWord_162745).sum := by decide
  have hdescent : baseEnd_162745 < baseStart_162745 := by decide
  rcases family_descends (prefixWord ++ tailWord_162745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162777 : List Nat := [1, 2, 1, 2, 5, 3, 2, 2, 4]
def baseStart_162777 : Nat := 118140960795 + 162777 * 2 ^ 59
def prefixEnd_162777 : Nat := 4983230072969 + 3 ^ 40 * 162777 * 2
def baseEnd_162777 : Nat := 18573964554892192875313

theorem tailTrace_162777 : CollatzResearch.WordTrace tailWord_162777 prefixEnd_162777 18573964554892192875313 := by
  unfold tailWord_162777
  simp only [CollatzResearch.WordTrace]
  refine ⟨5936964931294203943430585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3957976620862802628953723 5936964931294203943430585)
  ·
    refine ⟨4452723698470652957572939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5936964931294203943430585 4452723698470652957572939)
    ·
      refine ⟨6679085547705979436359409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4452723698470652957572939 6679085547705979436359409)
      ·
        refine ⟨5009314160779484577269557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6679085547705979436359409 5009314160779484577269557)
        ·
          refine ⟨469623202573076679119021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5009314160779484577269557 469623202573076679119021)
          ·
            refine ⟨176108700964903754669633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 469623202573076679119021 176108700964903754669633)
            ·
              refine ⟨132081525723677816002225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176108700964903754669633 132081525723677816002225)
              ·
                refine ⟨99061144292758362001669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132081525723677816002225 99061144292758362001669)
                ·
                  refine ⟨18573964554892192875313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99061144292758362001669 18573964554892192875313)
                  ·
                    rfl

theorem cell22_162777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 4].length) (baseStart_162777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162777 prefixEnd_162777 := by exact prefixLift 162777
  have htrace : WordTrace (prefixWord ++ tailWord_162777) baseStart_162777 baseEnd_162777 := by
    simpa [prefixWord, tailWord_162777, baseEnd_162777] using wordTrace_append hprefix tailTrace_162777
  have hstable : (prefixWord ++ tailWord_162777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162777).length < 2 ^ (prefixWord ++ tailWord_162777).sum := by decide
  have hdescent : baseEnd_162777 < baseStart_162777 := by decide
  rcases family_descends (prefixWord ++ tailWord_162777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162837 : List Nat := [1, 3, 2, 1, 4, 1, 2, 4, 1, 3]
def baseStart_162837 : Nat := 118140960795 + 162837 * 2 ^ 59
def prefixEnd_162837 : Nat := 4983230072969 + 3 ^ 40 * 162837 * 2
def baseEnd_162837 : Nat := 55742432890856422125755

theorem tailTrace_162837 : CollatzResearch.WordTrace tailWord_162837 prefixEnd_162837 55742432890856422125755 := by
  unfold tailWord_162837
  simp only [CollatzResearch.WordTrace]
  refine ⟨5939153311076834190614765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3959435540717889460409843 5939153311076834190614765)
  ·
    refine ⟨2227182491653812821480537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5939153311076834190614765 2227182491653812821480537)
    ·
      refine ⟨1670386868740359616110403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2227182491653812821480537 1670386868740359616110403)
      ·
        refine ⟨2505580303110539424165605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1670386868740359616110403 2505580303110539424165605)
        ·
          refine ⟨469796306833226142031051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2505580303110539424165605 469796306833226142031051)
          ·
            refine ⟨704694460249839213046577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469796306833226142031051 704694460249839213046577)
            ·
              refine ⟨528520845187379409784933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 704694460249839213046577 528520845187379409784933)
              ·
                refine ⟨99097658472633639334675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 528520845187379409784933 99097658472633639334675)
                ·
                  refine ⟨148646487708950459002013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99097658472633639334675 148646487708950459002013)
                  ·
                    refine ⟨55742432890856422125755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 148646487708950459002013 55742432890856422125755)
                    ·
                      rfl

theorem cell22_162837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_162837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162837 prefixEnd_162837 := by exact prefixLift 162837
  have htrace : WordTrace (prefixWord ++ tailWord_162837) baseStart_162837 baseEnd_162837 := by
    simpa [prefixWord, tailWord_162837, baseEnd_162837] using wordTrace_append hprefix tailTrace_162837
  have hstable : (prefixWord ++ tailWord_162837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162837).length < 2 ^ (prefixWord ++ tailWord_162837).sum := by decide
  have hdescent : baseEnd_162837 < baseStart_162837 := by decide
  rcases family_descends (prefixWord ++ tailWord_162837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162914 : List Nat := [3, 3, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_162914 : Nat := 118140960795 + 162914 * 2 ^ 59
def prefixEnd_162914 : Nat := 4983230072969 + 3 ^ 40 * 162914 * 2
def baseEnd_162914 : Nat := 55768791564453887950519

theorem tailTrace_162914 : CollatzResearch.WordTrace tailWord_162914 prefixEnd_162914 55768791564453887950519 := by
  unfold tailWord_162914
  simp only [CollatzResearch.WordTrace]
  refine ⟨1485490432949469085291949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3961307821198584227445197 1485490432949469085291949)
  ·
    refine ⟨557058912356050906984481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1485490432949469085291949 557058912356050906984481)
    ·
      refine ⟨417794184267038180238361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 557058912356050906984481 417794184267038180238361)
      ·
        refine ⟨313345638200278635178771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417794184267038180238361 313345638200278635178771)
        ·
          refine ⟨470018457300417952768157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313345638200278635178771 470018457300417952768157)
          ·
            refine ⟨176256921487656732288059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 470018457300417952768157 176256921487656732288059)
            ·
              refine ⟨264385382231485098432089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176256921487656732288059 264385382231485098432089)
              ·
                refine ⟨198289036673613823824067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264385382231485098432089 198289036673613823824067)
                ·
                  refine ⟨297433555010420735736101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198289036673613823824067 297433555010420735736101)
                  ·
                    refine ⟨55768791564453887950519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 297433555010420735736101 55768791564453887950519)
                    ·
                      rfl

theorem cell22_162914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_162914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162914 prefixEnd_162914 := by exact prefixLift 162914
  have htrace : WordTrace (prefixWord ++ tailWord_162914) baseStart_162914 baseEnd_162914 := by
    simpa [prefixWord, tailWord_162914, baseEnd_162914] using wordTrace_append hprefix tailTrace_162914
  have hstable : (prefixWord ++ tailWord_162914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162914).length < 2 ^ (prefixWord ++ tailWord_162914).sum := by decide
  have hdescent : baseEnd_162914 < baseStart_162914 := by decide
  rcases family_descends (prefixWord ++ tailWord_162914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162925 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_162925 : Nat := 118140960795 + 162925 * 2 ^ 59
def prefixEnd_162925 : Nat := 4983230072969 + 3 ^ 40 * 162925 * 2
def baseEnd_162925 : Nat := 55772557089253525925485

theorem tailTrace_162925 : CollatzResearch.WordTrace tailWord_162925 prefixEnd_162925 55772557089253525925485 := by
  unfold tailWord_162925
  simp only [CollatzResearch.WordTrace]
  refine ⟨5942362934758025219818229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3961575289838683479878819 5942362934758025219818229)
  ·
    refine ⟨557096525133564864357959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5942362934758025219818229 557096525133564864357959)
    ·
      refine ⟨835644787700347296536939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 557096525133564864357959 835644787700347296536939)
      ·
        refine ⟨1253467181550520944805409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835644787700347296536939 1253467181550520944805409)
        ·
          refine ⟨940100386162890708604057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1253467181550520944805409 940100386162890708604057)
          ·
            refine ⟨705075289622168031453043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 940100386162890708604057 705075289622168031453043)
            ·
              refine ⟨1057612934433252047179565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 705075289622168031453043 1057612934433252047179565)
              ·
                refine ⟨396604850412469517692337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1057612934433252047179565 396604850412469517692337)
                ·
                  refine ⟨297453637809352138269253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396604850412469517692337 297453637809352138269253)
                  ·
                    refine ⟨55772557089253525925485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 297453637809352138269253 55772557089253525925485)
                    ·
                      rfl

theorem cell22_162925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_162925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162925 prefixEnd_162925 := by exact prefixLift 162925
  have htrace : WordTrace (prefixWord ++ tailWord_162925) baseStart_162925 baseEnd_162925 := by
    simpa [prefixWord, tailWord_162925, baseEnd_162925] using wordTrace_append hprefix tailTrace_162925
  have hstable : (prefixWord ++ tailWord_162925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162925).length < 2 ^ (prefixWord ++ tailWord_162925).sum := by decide
  have hdescent : baseEnd_162925 < baseStart_162925 := by decide
  rcases family_descends (prefixWord ++ tailWord_162925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162953 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 2, 6]
def baseStart_162953 : Nat := 118140960795 + 162953 * 2 ^ 59
def prefixEnd_162953 : Nat := 4983230072969 + 3 ^ 40 * 162953 * 2
def baseEnd_162953 : Nat := 55782142061470786225399

theorem tailTrace_162953 : CollatzResearch.WordTrace tailWord_162953 prefixEnd_162953 55782142061470786225399 := by
  unfold tailWord_162953
  simp only [CollatzResearch.WordTrace]
  refine ⟨5943384178656586001837513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3962256119104390667891675 5943384178656586001837513)
  ·
    refine ⟨4457538133992439501378135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5943384178656586001837513 4457538133992439501378135)
    ·
      refine ⟨6686307200988659252067203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4457538133992439501378135 6686307200988659252067203)
      ·
        refine ⟨10029460801482988878100805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6686307200988659252067203 10029460801482988878100805)
        ·
          refine ⟨1880523900278060414643901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10029460801482988878100805 1880523900278060414643901)
          ·
            refine ⟨705196462604272655491463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1880523900278060414643901 705196462604272655491463)
            ·
              refine ⟨1057794693906408983237195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 705196462604272655491463 1057794693906408983237195)
              ·
                refine ⟨1586692040859613474855793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057794693906408983237195 1586692040859613474855793)
                ·
                  refine ⟨1190019030644710106141845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1586692040859613474855793 1190019030644710106141845)
                  ·
                    refine ⟨55782142061470786225399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1190019030644710106141845 55782142061470786225399)
                    ·
                      rfl

theorem cell22_162953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_162953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162953 prefixEnd_162953 := by exact prefixLift 162953
  have htrace : WordTrace (prefixWord ++ tailWord_162953) baseStart_162953 baseEnd_162953 := by
    simpa [prefixWord, tailWord_162953, baseEnd_162953] using wordTrace_append hprefix tailTrace_162953
  have hstable : (prefixWord ++ tailWord_162953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162953).length < 2 ^ (prefixWord ++ tailWord_162953).sum := by decide
  have hdescent : baseEnd_162953 < baseStart_162953 := by decide
  rcases family_descends (prefixWord ++ tailWord_162953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162972 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 3, 3]
def baseStart_162972 : Nat := 118140960795 + 162972 * 2 ^ 59
def prefixEnd_162972 : Nat := 4983230072969 + 3 ^ 40 * 162972 * 2
def baseEnd_162972 : Nat := 55788646149761070000341

theorem tailTrace_162972 : CollatzResearch.WordTrace tailWord_162972 prefixEnd_162972 55788646149761070000341 := by
  unfold tailWord_162972
  simp only [CollatzResearch.WordTrace]
  refine ⟨2972038582793876123389585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3962718110391834831186113 2972038582793876123389585)
  ·
    refine ⟨2229028937095407092542189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2972038582793876123389585 2229028937095407092542189)
    ·
      refine ⟨835885851410777659703321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2229028937095407092542189 835885851410777659703321)
      ·
        refine ⟨626914388558083244777491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 835885851410777659703321 626914388558083244777491)
        ·
          refine ⟨940371582837124867166237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626914388558083244777491 940371582837124867166237)
          ·
            refine ⟨352639343563921825187339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 940371582837124867166237 352639343563921825187339)
            ·
              refine ⟨528959015345882737781009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352639343563921825187339 528959015345882737781009)
              ·
                refine ⟨396719261509412053335757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 528959015345882737781009 396719261509412053335757)
                ·
                  refine ⟨148769723066029520000909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396719261509412053335757 148769723066029520000909)
                  ·
                    refine ⟨55788646149761070000341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 148769723066029520000909 55788646149761070000341)
                    ·
                      rfl

theorem cell22_162972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_162972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_162972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_162972 prefixEnd_162972 := by exact prefixLift 162972
  have htrace : WordTrace (prefixWord ++ tailWord_162972) baseStart_162972 baseEnd_162972 := by
    simpa [prefixWord, tailWord_162972, baseEnd_162972] using wordTrace_append hprefix tailTrace_162972
  have hstable : (prefixWord ++ tailWord_162972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162972).length < 2 ^ (prefixWord ++ tailWord_162972).sum := by decide
  have hdescent : baseEnd_162972 < baseStart_162972 := by decide
  rcases family_descends (prefixWord ++ tailWord_162972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163075 : List Nat := [1, 1, 1, 3, 2, 5, 2, 7]
def baseStart_163075 : Nat := 118140960795 + 163075 * 2 ^ 59
def prefixEnd_163075 : Nat := 4983230072969 + 3 ^ 40 * 163075 * 2
def baseEnd_163075 : Nat := 6202656128300348297225

theorem tailTrace_163075 : CollatzResearch.WordTrace tailWord_163075 prefixEnd_163075 6202656128300348297225 := by
  unfold tailWord_163075
  simp only [CollatzResearch.WordTrace]
  refine ⟨5947833884214600837778679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3965222589476400558519119 5947833884214600837778679)
  ·
    refine ⟨8921750826321901256668019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5947833884214600837778679 8921750826321901256668019)
    ·
      refine ⟨13382626239482851885002029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8921750826321901256668019 13382626239482851885002029)
      ·
        refine ⟨5018484839806069456875761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13382626239482851885002029 5018484839806069456875761)
        ·
          refine ⟨3763863629854552092656821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5018484839806069456875761 3763863629854552092656821)
          ·
            refine ⟨352862215298864258686577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3763863629854552092656821 352862215298864258686577)
            ·
              refine ⟨264646661474148194014933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352862215298864258686577 264646661474148194014933)
              ·
                refine ⟨6202656128300348297225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 264646661474148194014933 6202656128300348297225)
                ·
                  rfl

theorem cell22_163075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 7].length) (baseStart_163075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163075 prefixEnd_163075 := by exact prefixLift 163075
  have htrace : WordTrace (prefixWord ++ tailWord_163075) baseStart_163075 baseEnd_163075 := by
    simpa [prefixWord, tailWord_163075, baseEnd_163075] using wordTrace_append hprefix tailTrace_163075
  have hstable : (prefixWord ++ tailWord_163075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163075).length < 2 ^ (prefixWord ++ tailWord_163075).sum := by decide
  have hdescent : baseEnd_163075 < baseStart_163075 := by decide
  rcases family_descends (prefixWord ++ tailWord_163075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163124 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_163124 : Nat := 118140960795 + 163124 * 2 ^ 59
def prefixEnd_163124 : Nat := 4983230072969 + 3 ^ 40 * 163124 * 2
def baseEnd_163124 : Nat := 55840678856083340199875

theorem tailTrace_163124 : CollatzResearch.WordTrace tailWord_163124 prefixEnd_163124 55840678856083340199875 := by
  unfold tailWord_163124
  simp only [CollatzResearch.WordTrace]
  refine ⟨2974810530518541103156213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3966414040691388137541617 2974810530518541103156213)
  ·
    refine ⟨278888487236113228420895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2974810530518541103156213 278888487236113228420895)
    ·
      refine ⟨418332730854169842631343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278888487236113228420895 418332730854169842631343)
      ·
        refine ⟨627499096281254763947015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418332730854169842631343 627499096281254763947015)
        ·
          refine ⟨941248644421882145920523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627499096281254763947015 941248644421882145920523)
          ·
            refine ⟨1411872966632823218880785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941248644421882145920523 1411872966632823218880785)
            ·
              refine ⟨1058904724974617414160589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1411872966632823218880785 1058904724974617414160589)
              ·
                refine ⟨397089271865481530310221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1058904724974617414160589 397089271865481530310221)
                ·
                  refine ⟨148908476949555573866333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397089271865481530310221 148908476949555573866333)
                  ·
                    refine ⟨55840678856083340199875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 148908476949555573866333 55840678856083340199875)
                    ·
                      rfl

theorem cell22_163124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_163124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163124 prefixEnd_163124 := by exact prefixLift 163124
  have htrace : WordTrace (prefixWord ++ tailWord_163124) baseStart_163124 baseEnd_163124 := by
    simpa [prefixWord, tailWord_163124, baseEnd_163124] using wordTrace_append hprefix tailTrace_163124
  have hstable : (prefixWord ++ tailWord_163124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163124).length < 2 ^ (prefixWord ++ tailWord_163124).sum := by decide
  have hdescent : baseEnd_163124 < baseStart_163124 := by decide
  rcases family_descends (prefixWord ++ tailWord_163124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163126 : List Nat := [5, 1, 2, 3, 1, 2, 1, 7]
def baseStart_163126 : Nat := 118140960795 + 163126 * 2 ^ 59
def prefixEnd_163126 : Nat := 4983230072969 + 3 ^ 40 * 163126 * 2
def baseEnd_163126 : Nat := 6204595944106222405541

theorem tailTrace_163126 : CollatzResearch.WordTrace tailWord_163126 prefixEnd_163126 6204595944106222405541 := by
  unfold tailWord_163126
  simp only [CollatzResearch.WordTrace]
  refine ⟨371855875439364784242827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3966462671353224365256821 371855875439364784242827)
  ·
    refine ⟨557783813159047176364241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 371855875439364784242827 557783813159047176364241)
    ·
      refine ⟨418337859869285382273181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 557783813159047176364241 418337859869285382273181)
      ·
        refine ⟨156876697450982018352443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 418337859869285382273181 156876697450982018352443)
        ·
          refine ⟨235315046176473027528665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156876697450982018352443 235315046176473027528665)
          ·
            refine ⟨176486284632354770646499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235315046176473027528665 176486284632354770646499)
            ·
              refine ⟨264729426948532155969749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176486284632354770646499 264729426948532155969749)
              ·
                refine ⟨6204595944106222405541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 264729426948532155969749 6204595944106222405541)
                ·
                  rfl

theorem cell22_163126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_163126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163126 prefixEnd_163126 := by exact prefixLift 163126
  have htrace : WordTrace (prefixWord ++ tailWord_163126) baseStart_163126 baseEnd_163126 := by
    simpa [prefixWord, tailWord_163126, baseEnd_163126] using wordTrace_append hprefix tailTrace_163126
  have hstable : (prefixWord ++ tailWord_163126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163126).length < 2 ^ (prefixWord ++ tailWord_163126).sum := by decide
  have hdescent : baseEnd_163126 < baseStart_163126 := by decide
  rcases family_descends (prefixWord ++ tailWord_163126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163135 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 1, 7]
def baseStart_163135 : Nat := 118140960795 + 163135 * 2 ^ 59
def prefixEnd_163135 : Nat := 4983230072969 + 3 ^ 40 * 163135 * 2
def baseEnd_163135 : Nat := 55844444380882978174841

theorem tailTrace_163135 : CollatzResearch.WordTrace tailWord_163135 prefixEnd_163135 55844444380882978174841 := by
  unfold tailWord_163135
  simp only [CollatzResearch.WordTrace]
  refine ⟨5950022263997231084962859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3966681509331487389975239 5950022263997231084962859)
  ·
    refine ⟨8925033395995846627444289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5950022263997231084962859 8925033395995846627444289)
    ·
      refine ⟨6693775046996884970583217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8925033395995846627444289 6693775046996884970583217)
      ·
        refine ⟨5020331285247663727937413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6693775046996884970583217 5020331285247663727937413)
        ·
          refine ⟨941312115983936948988265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5020331285247663727937413 941312115983936948988265)
          ·
            refine ⟨705984086987952711741199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 941312115983936948988265 705984086987952711741199)
            ·
              refine ⟨1058976130481929067611799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 705984086987952711741199 1058976130481929067611799)
              ·
                refine ⟨1588464195722893601417699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1058976130481929067611799 1588464195722893601417699)
                ·
                  refine ⟨2382696293584340402126549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1588464195722893601417699 2382696293584340402126549)
                  ·
                    refine ⟨55844444380882978174841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2382696293584340402126549 55844444380882978174841)
                    ·
                      rfl

theorem cell22_163135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_163135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163135 prefixEnd_163135 := by exact prefixLift 163135
  have htrace : WordTrace (prefixWord ++ tailWord_163135) baseStart_163135 baseEnd_163135 := by
    simpa [prefixWord, tailWord_163135, baseEnd_163135] using wordTrace_append hprefix tailTrace_163135
  have hstable : (prefixWord ++ tailWord_163135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163135).length < 2 ^ (prefixWord ++ tailWord_163135).sum := by decide
  have hdescent : baseEnd_163135 < baseStart_163135 := by decide
  rcases family_descends (prefixWord ++ tailWord_163135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163195 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 3, 6]
def baseStart_163195 : Nat := 118140960795 + 163195 * 2 ^ 59
def prefixEnd_163195 : Nat := 4983230072969 + 3 ^ 40 * 163195 * 2
def baseEnd_163195 : Nat := 55864983607062821674657

theorem tailTrace_163195 : CollatzResearch.WordTrace tailWord_163195 prefixEnd_163195 55864983607062821674657 := by
  unfold tailWord_163195
  simp only [CollatzResearch.WordTrace]
  refine ⟨5952210643779861332147039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3968140429186574221431359 5952210643779861332147039)
  ·
    refine ⟨8928315965669791998220559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5952210643779861332147039 8928315965669791998220559)
    ·
      refine ⟨13392473948504687997330839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8928315965669791998220559 13392473948504687997330839)
      ·
        refine ⟨20088710922757031995996259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13392473948504687997330839 20088710922757031995996259)
        ·
          refine ⟨30133066384135547993994389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20088710922757031995996259 30133066384135547993994389)
          ·
            refine ⟨1412487486756353812218487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30133066384135547993994389 1412487486756353812218487)
            ·
              refine ⟨2118731230134530718327731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1412487486756353812218487 2118731230134530718327731)
              ·
                refine ⟨3178096845201796077491597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2118731230134530718327731 3178096845201796077491597)
                ·
                  refine ⟨1191786316950673529059349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3178096845201796077491597 1191786316950673529059349)
                  ·
                    refine ⟨55864983607062821674657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1191786316950673529059349 55864983607062821674657)
                    ·
                      rfl

theorem cell22_163195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 6].length) (baseStart_163195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163195 prefixEnd_163195 := by exact prefixLift 163195
  have htrace : WordTrace (prefixWord ++ tailWord_163195) baseStart_163195 baseEnd_163195 := by
    simpa [prefixWord, tailWord_163195, baseEnd_163195] using wordTrace_append hprefix tailTrace_163195
  have hstable : (prefixWord ++ tailWord_163195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163195).length < 2 ^ (prefixWord ++ tailWord_163195).sum := by decide
  have hdescent : baseEnd_163195 < baseStart_163195 := by decide
  rcases family_descends (prefixWord ++ tailWord_163195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163201 : List Nat := [1, 2, 4, 3, 2, 1, 2, 2, 1, 4]
def baseStart_163201 : Nat := 118140960795 + 163201 * 2 ^ 59
def prefixEnd_163201 : Nat := 4983230072969 + 3 ^ 40 * 163201 * 2
def baseEnd_163201 : Nat := 55867037529680806024639

theorem tailTrace_163201 : CollatzResearch.WordTrace tailWord_163201 prefixEnd_163201 55867037529680806024639 := by
  unfold tailWord_163201
  simp only [CollatzResearch.WordTrace]
  refine ⟨5952429481758124356865457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3968286321172082904576971 5952429481758124356865457)
  ·
    refine ⟨4464322111318593267649093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5952429481758124356865457 4464322111318593267649093)
    ·
      refine ⟨837060395872236237684205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4464322111318593267649093 837060395872236237684205)
      ·
        refine ⟨313897648452088589131577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 837060395872236237684205 313897648452088589131577)
        ·
          refine ⟨235423236339066441848683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313897648452088589131577 235423236339066441848683)
          ·
            refine ⟨353134854508599662773025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235423236339066441848683 353134854508599662773025)
            ·
              refine ⟨264851140881449747079769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353134854508599662773025 264851140881449747079769)
              ·
                refine ⟨198638355661087310309827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264851140881449747079769 198638355661087310309827)
                ·
                  refine ⟨297957533491630965464741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198638355661087310309827 297957533491630965464741)
                  ·
                    refine ⟨55867037529680806024639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 297957533491630965464741 55867037529680806024639)
                    ·
                      rfl

theorem cell22_163201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_163201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163201 prefixEnd_163201 := by exact prefixLift 163201
  have htrace : WordTrace (prefixWord ++ tailWord_163201) baseStart_163201 baseEnd_163201 := by
    simpa [prefixWord, tailWord_163201, baseEnd_163201] using wordTrace_append hprefix tailTrace_163201
  have hstable : (prefixWord ++ tailWord_163201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163201).length < 2 ^ (prefixWord ++ tailWord_163201).sum := by decide
  have hdescent : baseEnd_163201 < baseStart_163201 := by decide
  rcases family_descends (prefixWord ++ tailWord_163201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163212 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 2, 4]
def baseStart_163212 : Nat := 118140960795 + 163212 * 2 ^ 59
def prefixEnd_163212 : Nat := 4983230072969 + 3 ^ 40 * 163212 * 2
def baseEnd_163212 : Nat := 55870803054480443999605

theorem tailTrace_163212 : CollatzResearch.WordTrace tailWord_163212 prefixEnd_163212 55870803054480443999605 := by
  unfold tailWord_163212
  simp only [CollatzResearch.WordTrace]
  refine ⟨2976415342359136617757945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3968553789812182157010593 2976415342359136617757945)
  ·
    refine ⟨2232311506769352463318459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2976415342359136617757945 2232311506769352463318459)
    ·
      refine ⟨3348467260154028694977689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2232311506769352463318459 3348467260154028694977689)
      ·
        refine ⟨2511350445115521521233267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3348467260154028694977689 2511350445115521521233267)
        ·
          refine ⟨3767025667673282281849901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2511350445115521521233267 3767025667673282281849901)
          ·
            refine ⟨1412634625377480855693713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3767025667673282281849901 1412634625377480855693713)
            ·
              refine ⟨1059475969033110641770285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1412634625377480855693713 1059475969033110641770285)
              ·
                refine ⟨397303488387416490663857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1059475969033110641770285 397303488387416490663857)
                ·
                  refine ⟨297977616290562367997893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397303488387416490663857 297977616290562367997893)
                  ·
                    refine ⟨55870803054480443999605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 297977616290562367997893 55870803054480443999605)
                    ·
                      rfl

theorem cell22_163212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_163212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163212 prefixEnd_163212 := by exact prefixLift 163212
  have htrace : WordTrace (prefixWord ++ tailWord_163212) baseStart_163212 baseEnd_163212 := by
    simpa [prefixWord, tailWord_163212, baseEnd_163212] using wordTrace_append hprefix tailTrace_163212
  have hstable : (prefixWord ++ tailWord_163212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163212).length < 2 ^ (prefixWord ++ tailWord_163212).sum := by decide
  have hdescent : baseEnd_163212 < baseStart_163212 := by decide
  rcases family_descends (prefixWord ++ tailWord_163212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163229 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_163229 : Nat := 118140960795 + 163229 * 2 ^ 59
def prefixEnd_163229 : Nat := 4983230072969 + 3 ^ 40 * 163229 * 2
def baseEnd_163229 : Nat := 55876622501898066324553

theorem tailTrace_163229 : CollatzResearch.WordTrace tailWord_163229 prefixEnd_163229 55876622501898066324553 := by
  unfold tailWord_163229
  simp only [CollatzResearch.WordTrace]
  refine ⟨5953450725656685138884741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3968967150437790092589827 5953450725656685138884741)
  ·
    refine ⟨1116272011060628463540889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5953450725656685138884741 1116272011060628463540889)
    ·
      refine ⟨837204008295471347655667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1116272011060628463540889 837204008295471347655667)
      ·
        refine ⟨1255806012443207021483501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 837204008295471347655667 1255806012443207021483501)
        ·
          refine ⟨470927254666202633056313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1255806012443207021483501 470927254666202633056313)
          ·
            refine ⟨353195440999651974792235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470927254666202633056313 353195440999651974792235)
            ·
              refine ⟨529793161499477962188353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353195440999651974792235 529793161499477962188353)
              ·
                refine ⟨397344871124608471641265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 529793161499477962188353 397344871124608471641265)
                ·
                  refine ⟨298008653343456353730949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397344871124608471641265 298008653343456353730949)
                  ·
                    refine ⟨55876622501898066324553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 298008653343456353730949 55876622501898066324553)
                    ·
                      rfl

theorem cell22_163229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_163229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163229 prefixEnd_163229 := by exact prefixLift 163229
  have htrace : WordTrace (prefixWord ++ tailWord_163229) baseStart_163229 baseEnd_163229 := by
    simpa [prefixWord, tailWord_163229, baseEnd_163229] using wordTrace_append hprefix tailTrace_163229
  have hstable : (prefixWord ++ tailWord_163229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163229).length < 2 ^ (prefixWord ++ tailWord_163229).sum := by decide
  have hdescent : baseEnd_163229 < baseStart_163229 := by decide
  rcases family_descends (prefixWord ++ tailWord_163229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163289 : List Nat := [1, 2, 1, 2, 4, 3, 2, 2, 5]
def baseStart_163289 : Nat := 118140960795 + 163289 * 2 ^ 59
def prefixEnd_163289 : Nat := 4983230072969 + 3 ^ 40 * 163289 * 2
def baseEnd_163289 : Nat := 18632387242692636608123

theorem tailTrace_163289 : CollatzResearch.WordTrace tailWord_163289 prefixEnd_163289 18632387242692636608123 := by
  unfold tailWord_163289
  simp only [CollatzResearch.WordTrace]
  refine ⟨5955639105439315386068921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3970426070292876924045947 5955639105439315386068921)
  ·
    refine ⟨4466729329079486539551691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5955639105439315386068921 4466729329079486539551691)
    ·
      refine ⟨6700093993619229809327537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4466729329079486539551691 6700093993619229809327537)
      ·
        refine ⟨5025070495214422356995653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6700093993619229809327537 5025070495214422356995653)
        ·
          refine ⟨942200717852704191936685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5025070495214422356995653 942200717852704191936685)
          ·
            refine ⟨353325269194764071976257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 942200717852704191936685 353325269194764071976257)
            ·
              refine ⟨264993951896073053982193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353325269194764071976257 264993951896073053982193)
              ·
                refine ⟨198745463922054790486645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264993951896073053982193 198745463922054790486645)
                ·
                  refine ⟨18632387242692636608123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 198745463922054790486645 18632387242692636608123)
                  ·
                    rfl

theorem cell22_163289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 5].length) (baseStart_163289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163289 prefixEnd_163289 := by exact prefixLift 163289
  have htrace : WordTrace (prefixWord ++ tailWord_163289) baseStart_163289 baseEnd_163289 := by
    simpa [prefixWord, tailWord_163289, baseEnd_163289] using wordTrace_append hprefix tailTrace_163289
  have hstable : (prefixWord ++ tailWord_163289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163289).length < 2 ^ (prefixWord ++ tailWord_163289).sum := by decide
  have hdescent : baseEnd_163289 < baseStart_163289 := by decide
  rcases family_descends (prefixWord ++ tailWord_163289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163293 : List Nat := [1, 4, 3, 1, 1, 3, 1, 4, 1, 3]
def baseStart_163293 : Nat := 118140960795 + 163293 * 2 ^ 59
def prefixEnd_163293 : Nat := 4983230072969 + 3 ^ 40 * 163293 * 2
def baseEnd_163293 : Nat := 55898531009823232724357

theorem tailTrace_163293 : CollatzResearch.WordTrace tailWord_163293 prefixEnd_163293 55898531009823232724357 := by
  unfold tailWord_163293
  simp only [CollatzResearch.WordTrace]
  refine ⟨5955784997424824069214533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3970523331616549379476355 5955784997424824069214533)
  ·
    refine ⟨1116709687017154512977725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5955784997424824069214533 1116709687017154512977725)
    ·
      refine ⟨418766132631432942366647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1116709687017154512977725 418766132631432942366647)
      ·
        refine ⟨628149198947149413549971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418766132631432942366647 628149198947149413549971)
        ·
          refine ⟨942223798420724120324957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628149198947149413549971 942223798420724120324957)
          ·
            refine ⟨353333924407771545121859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 942223798420724120324957 353333924407771545121859)
            ·
              refine ⟨530000886611657317682789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353333924407771545121859 530000886611657317682789)
              ·
                refine ⟨99375166239685747065523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 530000886611657317682789 99375166239685747065523)
                ·
                  refine ⟨149062749359528620598285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99375166239685747065523 149062749359528620598285)
                  ·
                    refine ⟨55898531009823232724357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149062749359528620598285 55898531009823232724357)
                    ·
                      rfl

theorem cell22_163293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_163293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163293 prefixEnd_163293 := by exact prefixLift 163293
  have htrace : WordTrace (prefixWord ++ tailWord_163293) baseStart_163293 baseEnd_163293 := by
    simpa [prefixWord, tailWord_163293, baseEnd_163293] using wordTrace_append hprefix tailTrace_163293
  have hstable : (prefixWord ++ tailWord_163293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163293).length < 2 ^ (prefixWord ++ tailWord_163293).sum := by decide
  have hdescent : baseEnd_163293 < baseStart_163293 := by decide
  rcases family_descends (prefixWord ++ tailWord_163293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163336 : List Nat := [2, 1, 3, 2, 1, 1, 6, 1, 1, 4]
def baseStart_163336 : Nat := 118140960795 + 163336 * 2 ^ 59
def prefixEnd_163336 : Nat := 4983230072969 + 3 ^ 40 * 163336 * 2
def baseEnd_163336 : Nat := 55913250788585453899225

theorem tailTrace_163336 : CollatzResearch.WordTrace tailWord_163336 prefixEnd_163336 55913250788585453899225 := by
  unfold tailWord_163336
  simp only [CollatzResearch.WordTrace]
  refine ⟨2978676668134521206514931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3971568890846028275353241 2978676668134521206514931)
  ·
    refine ⟨4468015002201781809772397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2978676668134521206514931 4468015002201781809772397)
    ·
      refine ⟨1675505625825668178664649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4468015002201781809772397 1675505625825668178664649)
      ·
        refine ⟨1256629219369251133998487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1675505625825668178664649 1256629219369251133998487)
        ·
          refine ⟨1884943829053876700997731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1256629219369251133998487 1884943829053876700997731)
          ·
            refine ⟨2827415743580815051496597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1884943829053876700997731 2827415743580815051496597)
            ·
              refine ⟨132535112980350705538903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2827415743580815051496597 132535112980350705538903)
              ·
                refine ⟨198802669470526058308355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132535112980350705538903 198802669470526058308355)
                ·
                  refine ⟨298204004205789087462533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198802669470526058308355 298204004205789087462533)
                  ·
                    refine ⟨55913250788585453899225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 298204004205789087462533 55913250788585453899225)
                    ·
                      rfl

theorem cell22_163336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_163336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163336 prefixEnd_163336 := by exact prefixLift 163336
  have htrace : WordTrace (prefixWord ++ tailWord_163336) baseStart_163336 baseEnd_163336 := by
    simpa [prefixWord, tailWord_163336, baseEnd_163336] using wordTrace_append hprefix tailTrace_163336
  have hstable : (prefixWord ++ tailWord_163336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163336).length < 2 ^ (prefixWord ++ tailWord_163336).sum := by decide
  have hdescent : baseEnd_163336 < baseStart_163336 := by decide
  rcases family_descends (prefixWord ++ tailWord_163336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163377 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 1, 9]
def baseStart_163377 : Nat := 118140960795 + 163377 * 2 ^ 59
def prefixEnd_163377 : Nat := 4983230072969 + 3 ^ 40 * 163377 * 2
def baseEnd_163377 : Nat := 55927285926475013624099

theorem tailTrace_163377 : CollatzResearch.WordTrace tailWord_163377 prefixEnd_163377 55927285926475013624099 := by
  unfold tailWord_163377
  simp only [CollatzResearch.WordTrace]
  refine ⟨5958848729120506415272385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3972565819413670943514923 5958848729120506415272385)
  ·
    refine ⟨4469136546840379811454289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5958848729120506415272385 4469136546840379811454289)
    ·
      refine ⟨3351852410130284858590717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4469136546840379811454289 3351852410130284858590717)
      ·
        refine ⟨1256944653798856821971519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3351852410130284858590717 1256944653798856821971519)
        ·
          refine ⟨1885416980698285232957279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1256944653798856821971519 1885416980698285232957279)
          ·
            refine ⟨2828125471047427849435919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1885416980698285232957279 2828125471047427849435919)
            ·
              refine ⟨4242188206571141774153879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2828125471047427849435919 4242188206571141774153879)
              ·
                refine ⟨6363282309856712661230819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4242188206571141774153879 6363282309856712661230819)
                ·
                  refine ⟨9544923464785068991846229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6363282309856712661230819 9544923464785068991846229)
                  ·
                    refine ⟨55927285926475013624099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 9544923464785068991846229 55927285926475013624099)
                    ·
                      rfl

theorem cell22_163377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_163377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163377 prefixEnd_163377 := by exact prefixLift 163377
  have htrace : WordTrace (prefixWord ++ tailWord_163377) baseStart_163377 baseEnd_163377 := by
    simpa [prefixWord, tailWord_163377, baseEnd_163377] using wordTrace_append hprefix tailTrace_163377
  have hstable : (prefixWord ++ tailWord_163377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163377).length < 2 ^ (prefixWord ++ tailWord_163377).sum := by decide
  have hdescent : baseEnd_163377 < baseStart_163377 := by decide
  rcases family_descends (prefixWord ++ tailWord_163377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163379 : List Nat := [1, 1, 1, 2, 4, 3, 4, 6]
def baseStart_163379 : Nat := 118140960795 + 163379 * 2 ^ 59
def prefixEnd_163379 : Nat := 4983230072969 + 3 ^ 40 * 163379 * 2
def baseEnd_163379 : Nat := 6214218951927519452677

theorem tailTrace_163379 : CollatzResearch.WordTrace tailWord_163379 prefixEnd_163379 6214218951927519452677 := by
  unfold tailWord_163379
  simp only [CollatzResearch.WordTrace]
  refine ⟨5958921675113260756845191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3972614450075507171230127 5958921675113260756845191)
  ·
    refine ⟨8938382512669891135267787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5958921675113260756845191 8938382512669891135267787)
    ·
      refine ⟨13407573769004836702901681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8938382512669891135267787 13407573769004836702901681)
      ·
        refine ⟨10055680326753627527176261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13407573769004836702901681 10055680326753627527176261)
        ·
          refine ⟨1885440061266305161345549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10055680326753627527176261 1885440061266305161345549)
          ·
            refine ⟨707040022974864435504581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1885440061266305161345549 707040022974864435504581)
            ·
              refine ⟨132570004307787081657109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 707040022974864435504581 132570004307787081657109)
              ·
                refine ⟨6214218951927519452677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 132570004307787081657109 6214218951927519452677)
                ·
                  rfl

theorem cell22_163379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 6].length) (baseStart_163379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163379 prefixEnd_163379 := by exact prefixLift 163379
  have htrace : WordTrace (prefixWord ++ tailWord_163379) baseStart_163379 baseEnd_163379 := by
    simpa [prefixWord, tailWord_163379, baseEnd_163379] using wordTrace_append hprefix tailTrace_163379
  have hstable : (prefixWord ++ tailWord_163379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163379).length < 2 ^ (prefixWord ++ tailWord_163379).sum := by decide
  have hdescent : baseEnd_163379 < baseStart_163379 := by decide
  rcases family_descends (prefixWord ++ tailWord_163379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163392 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 1, 8]
def baseStart_163392 : Nat := 118140960795 + 163392 * 2 ^ 59
def prefixEnd_163392 : Nat := 4983230072969 + 3 ^ 40 * 163392 * 2
def baseEnd_163392 : Nat := 55932420733019974499053

theorem tailTrace_163392 : CollatzResearch.WordTrace tailWord_163392 prefixEnd_163392 55932420733019974499053 := by
  unfold tailWord_163392
  simp only [CollatzResearch.WordTrace]
  refine ⟨2979697912033081988534215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3972930549377442651378953 2979697912033081988534215)
  ·
    refine ⟨4469546868049622982801323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2979697912033081988534215 4469546868049622982801323)
    ·
      refine ⟨6704320302074434474201985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4469546868049622982801323 6704320302074434474201985)
      ·
        refine ⟨5028240226555825855651489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6704320302074434474201985 5028240226555825855651489)
        ·
          refine ⟨3771180169916869391738617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5028240226555825855651489 3771180169916869391738617)
          ·
            refine ⟨2828385127437652043803963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3771180169916869391738617 2828385127437652043803963)
            ·
              refine ⟨4242577691156478065705945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2828385127437652043803963 4242577691156478065705945)
              ·
                refine ⟨3181933268367358549279459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4242577691156478065705945 3181933268367358549279459)
                ·
                  refine ⟨4772899902551037823919189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3181933268367358549279459 4772899902551037823919189)
                  ·
                    refine ⟨55932420733019974499053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4772899902551037823919189 55932420733019974499053)
                    ·
                      rfl

theorem cell22_163392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_163392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163392 prefixEnd_163392 := by exact prefixLift 163392
  have htrace : WordTrace (prefixWord ++ tailWord_163392) baseStart_163392 baseEnd_163392 := by
    simpa [prefixWord, tailWord_163392, baseEnd_163392] using wordTrace_append hprefix tailTrace_163392
  have hstable : (prefixWord ++ tailWord_163392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163392).length < 2 ^ (prefixWord ++ tailWord_163392).sum := by decide
  have hdescent : baseEnd_163392 < baseStart_163392 := by decide
  rcases family_descends (prefixWord ++ tailWord_163392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163486 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 8]
def baseStart_163486 : Nat := 118140960795 + 163486 * 2 ^ 59
def prefixEnd_163486 : Nat := 4983230072969 + 3 ^ 40 * 163486 * 2
def baseEnd_163486 : Nat := 18654866284678354216255

theorem tailTrace_163486 : CollatzResearch.WordTrace tailWord_163486 prefixEnd_163486 18654866284678354216255 := by
  unfold tailWord_163486
  simp only [CollatzResearch.WordTrace]
  refine ⟨745353035715702253873789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3975216190483745353993541 745353035715702253873789)
  ·
    refine ⟨279507388393388345202671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 745353035715702253873789 279507388393388345202671)
    ·
      refine ⟨419261082590082517804007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279507388393388345202671 419261082590082517804007)
      ·
        refine ⟨628891623885123776706011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419261082590082517804007 628891623885123776706011)
        ·
          refine ⟨943337435827685665059017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628891623885123776706011 943337435827685665059017)
          ·
            refine ⟨707503076870764248794263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 943337435827685665059017 707503076870764248794263)
            ·
              refine ⟨1061254615306146373191395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707503076870764248794263 1061254615306146373191395)
              ·
                refine ⟨1591881922959219559787093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1061254615306146373191395 1591881922959219559787093)
                ·
                  refine ⟨18654866284678354216255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1591881922959219559787093 18654866284678354216255)
                  ·
                    rfl

theorem cell22_163486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_163486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163486 prefixEnd_163486 := by exact prefixLift 163486
  have htrace : WordTrace (prefixWord ++ tailWord_163486) baseStart_163486 baseEnd_163486 := by
    simpa [prefixWord, tailWord_163486, baseEnd_163486] using wordTrace_append hprefix tailTrace_163486
  have hstable : (prefixWord ++ tailWord_163486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163486).length < 2 ^ (prefixWord ++ tailWord_163486).sum := by decide
  have hdescent : baseEnd_163486 < baseStart_163486 := by decide
  rcases family_descends (prefixWord ++ tailWord_163486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163501 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_163501 : Nat := 118140960795 + 163501 * 2 ^ 59
def prefixEnd_163501 : Nat := 4983230072969 + 3 ^ 40 * 163501 * 2
def baseEnd_163501 : Nat := 55969733660580023523719

theorem tailTrace_163501 : CollatzResearch.WordTrace tailWord_163501 prefixEnd_163501 55969733660580023523719 := by
  unfold tailWord_163501
  simp only [CollatzResearch.WordTrace]
  refine ⟨5963371380671275592786357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3975580920447517061857571 5963371380671275592786357)
  ·
    refine ⟨559066066937932086823721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5963371380671275592786357 559066066937932086823721)
    ·
      refine ⟨419299550203449065117791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 559066066937932086823721 419299550203449065117791)
      ·
        refine ⟨628949325305173597676687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419299550203449065117791 628949325305173597676687)
        ·
          refine ⟨943423987957760396515031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628949325305173597676687 943423987957760396515031)
          ·
            refine ⟨1415135981936640594772547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943423987957760396515031 1415135981936640594772547)
            ·
              refine ⟨2122703972904960892158821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415135981936640594772547 2122703972904960892158821)
              ·
                refine ⟨398006994919680167279779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2122703972904960892158821 398006994919680167279779)
                ·
                  refine ⟨597010492379520250919669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398006994919680167279779 597010492379520250919669)
                  ·
                    refine ⟨55969733660580023523719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 597010492379520250919669 55969733660580023523719)
                    ·
                      rfl

theorem cell22_163501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_163501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163501 prefixEnd_163501 := by exact prefixLift 163501
  have htrace : WordTrace (prefixWord ++ tailWord_163501) baseStart_163501 baseEnd_163501 := by
    simpa [prefixWord, tailWord_163501, baseEnd_163501] using wordTrace_append hprefix tailTrace_163501
  have hstable : (prefixWord ++ tailWord_163501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163501).length < 2 ^ (prefixWord ++ tailWord_163501).sum := by decide
  have hdescent : baseEnd_163501 < baseStart_163501 := by decide
  rcases family_descends (prefixWord ++ tailWord_163501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163514 : List Nat := [3, 1, 1, 1, 2, 5, 9]
def baseStart_163514 : Nat := 118140960795 + 163514 * 2 ^ 59
def prefixEnd_163514 : Nat := 4983230072969 + 3 ^ 40 * 163514 * 2
def baseEnd_163514 : Nat := 2073117919490826775877

theorem tailTrace_163514 : CollatzResearch.WordTrace tailWord_163514 prefixEnd_163514 2073117919490826775877 := by
  unfold tailWord_163514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1490961382406044703252399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3975897019749452542006397 1490961382406044703252399)
  ·
    refine ⟨2236442073609067054878599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1490961382406044703252399 2236442073609067054878599)
    ·
      refine ⟨3354663110413600582317899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2236442073609067054878599 3354663110413600582317899)
      ·
        refine ⟨5031994665620400873476849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3354663110413600582317899 5031994665620400873476849)
        ·
          refine ⟨3773995999215300655107637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5031994665620400873476849 3773995999215300655107637)
          ·
            refine ⟨353812124926434436416341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3773995999215300655107637 353812124926434436416341)
            ·
              refine ⟨2073117919490826775877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 353812124926434436416341 2073117919490826775877)
              ·
                rfl

theorem cell22_163514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 9].length) (baseStart_163514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163514 prefixEnd_163514 := by exact prefixLift 163514
  have htrace : WordTrace (prefixWord ++ tailWord_163514) baseStart_163514 baseEnd_163514 := by
    simpa [prefixWord, tailWord_163514, baseEnd_163514] using wordTrace_append hprefix tailTrace_163514
  have hstable : (prefixWord ++ tailWord_163514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163514).length < 2 ^ (prefixWord ++ tailWord_163514).sum := by decide
  have hdescent : baseEnd_163514 < baseStart_163514 := by decide
  rcases family_descends (prefixWord ++ tailWord_163514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163518 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_163518 : Nat := 118140960795 + 163518 * 2 ^ 59
def prefixEnd_163518 : Nat := 4983230072969 + 3 ^ 40 * 163518 * 2
def baseEnd_163518 : Nat := 55975553107997645848667

theorem tailTrace_163518 : CollatzResearch.WordTrace tailWord_163518 prefixEnd_163518 55975553107997645848667 := by
  unfold tailWord_163518
  simp only [CollatzResearch.WordTrace]
  refine ⟨745498927701210937019401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3975994281073124997436805 745498927701210937019401)
  ·
    refine ⟨559124195775908202764551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 745498927701210937019401 559124195775908202764551)
    ·
      refine ⟨838686293663862304146827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 559124195775908202764551 838686293663862304146827)
      ·
        refine ⟨1258029440495793456220241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 838686293663862304146827 1258029440495793456220241)
        ·
          refine ⟨943522080371845092165181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1258029440495793456220241 943522080371845092165181)
          ·
            refine ⟨353820780139441909561943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 943522080371845092165181 353820780139441909561943)
            ·
              refine ⟨530731170209162864342915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353820780139441909561943 530731170209162864342915)
              ·
                refine ⟨796096755313744296514373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530731170209162864342915 796096755313744296514373)
                ·
                  refine ⟨149268141621327055596445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 796096755313744296514373 149268141621327055596445)
                  ·
                    refine ⟨55975553107997645848667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149268141621327055596445 55975553107997645848667)
                    ·
                      rfl

theorem cell22_163518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_163518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163518 prefixEnd_163518 := by exact prefixLift 163518
  have htrace : WordTrace (prefixWord ++ tailWord_163518) baseStart_163518 baseEnd_163518 := by
    simpa [prefixWord, tailWord_163518, baseEnd_163518] using wordTrace_append hprefix tailTrace_163518
  have hstable : (prefixWord ++ tailWord_163518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163518).length < 2 ^ (prefixWord ++ tailWord_163518).sum := by decide
  have hdescent : baseEnd_163518 < baseStart_163518 := by decide
  rcases family_descends (prefixWord ++ tailWord_163518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163533 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_163533 : Nat := 118140960795 + 163533 * 2 ^ 59
def prefixEnd_163533 : Nat := 4983230072969 + 3 ^ 40 * 163533 * 2
def baseEnd_163533 : Nat := 55980687914542606723621

theorem tailTrace_163533 : CollatzResearch.WordTrace tailWord_163533 prefixEnd_163533 55980687914542606723621 := by
  unfold tailWord_163533
  simp only [CollatzResearch.WordTrace]
  refine ⟨5964538516555345057951253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3976359011036896705300835 5964538516555345057951253)
  ·
    refine ⟨279587742963531799591465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5964538516555345057951253 279587742963531799591465)
    ·
      refine ⟨209690807222648849693599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279587742963531799591465 209690807222648849693599)
      ·
        refine ⟨314536210833973274540399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209690807222648849693599 314536210833973274540399)
        ·
          refine ⟨471804316250959911810599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314536210833973274540399 471804316250959911810599)
          ·
            refine ⟨707706474376439867715899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471804316250959911810599 707706474376439867715899)
            ·
              refine ⟨1061559711564659801573849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707706474376439867715899 1061559711564659801573849)
              ·
                refine ⟨796169783673494851180387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1061559711564659801573849 796169783673494851180387)
                ·
                  refine ⟨1194254675510242276770581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796169783673494851180387 1194254675510242276770581)
                  ·
                    refine ⟨55980687914542606723621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1194254675510242276770581 55980687914542606723621)
                    ·
                      rfl

theorem cell22_163533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_163533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163533 prefixEnd_163533 := by exact prefixLift 163533
  have htrace : WordTrace (prefixWord ++ tailWord_163533) baseStart_163533 baseEnd_163533 := by
    simpa [prefixWord, tailWord_163533, baseEnd_163533] using wordTrace_append hprefix tailTrace_163533
  have hstable : (prefixWord ++ tailWord_163533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163533).length < 2 ^ (prefixWord ++ tailWord_163533).sum := by decide
  have hdescent : baseEnd_163533 < baseStart_163533 := by decide
  rcases family_descends (prefixWord ++ tailWord_163533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163548 : List Nat := [2, 2, 5, 1, 2, 1, 1, 8]
def baseStart_163548 : Nat := 118140960795 + 163548 * 2 ^ 59
def prefixEnd_163548 : Nat := 4983230072969 + 3 ^ 40 * 163548 * 2
def baseEnd_163548 : Nat := 6220646969009729733175

theorem tailTrace_163548 : CollatzResearch.WordTrace tailWord_163548 prefixEnd_163548 6220646969009729733175 := by
  unfold tailWord_163548
  simp only [CollatzResearch.WordTrace]
  refine ⟨2982542805750501309873649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3976723741000668413164865 2982542805750501309873649)
  ·
    refine ⟨2236907104312875982405237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2982542805750501309873649 2236907104312875982405237)
    ·
      refine ⟨209710041029332123350491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2236907104312875982405237 209710041029332123350491)
      ·
        refine ⟨314565061543998185025737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209710041029332123350491 314565061543998185025737)
        ·
          refine ⟨235923796157998638769303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314565061543998185025737 235923796157998638769303)
          ·
            refine ⟨353885694236997958153955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235923796157998638769303 353885694236997958153955)
            ·
              refine ⟨530828541355496937230933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353885694236997958153955 530828541355496937230933)
              ·
                refine ⟨6220646969009729733175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 530828541355496937230933 6220646969009729733175)
                ·
                  rfl

theorem cell22_163548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 8].length) (baseStart_163548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163548 prefixEnd_163548 := by exact prefixLift 163548
  have htrace : WordTrace (prefixWord ++ tailWord_163548) baseStart_163548 baseEnd_163548 := by
    simpa [prefixWord, tailWord_163548, baseEnd_163548] using wordTrace_append hprefix tailTrace_163548
  have hstable : (prefixWord ++ tailWord_163548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163548).length < 2 ^ (prefixWord ++ tailWord_163548).sum := by decide
  have hdescent : baseEnd_163548 < baseStart_163548 := by decide
  rcases family_descends (prefixWord ++ tailWord_163548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163589 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 1, 10]
def baseStart_163589 : Nat := 118140960795 + 163589 * 2 ^ 59
def prefixEnd_163589 : Nat := 4983230072969 + 3 ^ 40 * 163589 * 2
def baseEnd_163589 : Nat := 55999857858977127323449

theorem tailTrace_163589 : CollatzResearch.WordTrace tailWord_163589 prefixEnd_163589 55999857858977127323449 := by
  unfold tailWord_163589
  simp only [CollatzResearch.WordTrace]
  refine ⟨5966581004352466621989821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3977720669568311081326547 5966581004352466621989821)
  ·
    refine ⟨2237467876632174983246183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5966581004352466621989821 2237467876632174983246183)
    ·
      refine ⟨3356201814948262474869275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2237467876632174983246183 3356201814948262474869275)
      ·
        refine ⟨5034302722422393712303913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3356201814948262474869275 5034302722422393712303913)
        ·
          refine ⟨3775727041816795284227935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5034302722422393712303913 3775727041816795284227935)
          ·
            refine ⟨5663590562725192926341903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3775727041816795284227935 5663590562725192926341903)
            ·
              refine ⟨8495385844087789389512855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5663590562725192926341903 8495385844087789389512855)
              ·
                refine ⟨12743078766131684084269283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8495385844087789389512855 12743078766131684084269283)
                ·
                  refine ⟨19114618149197526126403925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12743078766131684084269283 19114618149197526126403925)
                  ·
                    refine ⟨55999857858977127323449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 19114618149197526126403925 55999857858977127323449)
                    ·
                      rfl

theorem cell22_163589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_163589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163589 prefixEnd_163589 := by exact prefixLift 163589
  have htrace : WordTrace (prefixWord ++ tailWord_163589) baseStart_163589 baseEnd_163589 := by
    simpa [prefixWord, tailWord_163589, baseEnd_163589] using wordTrace_append hprefix tailTrace_163589
  have hstable : (prefixWord ++ tailWord_163589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163589).length < 2 ^ (prefixWord ++ tailWord_163589).sum := by decide
  have hdescent : baseEnd_163589 < baseStart_163589 := by decide
  rcases family_descends (prefixWord ++ tailWord_163589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163653 : List Nat := [1, 3, 1, 1, 1, 2, 3, 5, 2, 3]
def baseStart_163653 : Nat := 118140960795 + 163653 * 2 ^ 59
def prefixEnd_163653 : Nat := 4983230072969 + 3 ^ 40 * 163653 * 2
def baseEnd_163653 : Nat := 56021766366902293723253

theorem tailTrace_163653 : CollatzResearch.WordTrace tailWord_163653 prefixEnd_163653 56021766366902293723253 := by
  unfold tailWord_163653
  simp only [CollatzResearch.WordTrace]
  refine ⟨5968915276120605552319613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3979276850747070368213075 5968915276120605552319613)
  ·
    refine ⟨2238343228545227082119855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5968915276120605552319613 2238343228545227082119855)
    ·
      refine ⟨3357514842817840623179783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2238343228545227082119855 3357514842817840623179783)
      ·
        refine ⟨5036272264226760934769675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3357514842817840623179783 5036272264226760934769675)
        ·
          refine ⟨7554408396340141402154513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5036272264226760934769675 7554408396340141402154513)
          ·
            refine ⟨5665806297255106051615885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7554408396340141402154513 5665806297255106051615885)
            ·
              refine ⟨2124677361470664769355957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5665806297255106051615885 2124677361470664769355957)
              ·
                refine ⟨199188502637874822127121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2124677361470664769355957 199188502637874822127121)
                ·
                  refine ⟨149391376978406116595341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199188502637874822127121 149391376978406116595341)
                  ·
                    refine ⟨56021766366902293723253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149391376978406116595341 56021766366902293723253)
                    ·
                      rfl

theorem cell22_163653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_163653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163653 prefixEnd_163653 := by exact prefixLift 163653
  have htrace : WordTrace (prefixWord ++ tailWord_163653) baseStart_163653 baseEnd_163653 := by
    simpa [prefixWord, tailWord_163653, baseEnd_163653] using wordTrace_append hprefix tailTrace_163653
  have hstable : (prefixWord ++ tailWord_163653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163653).length < 2 ^ (prefixWord ++ tailWord_163653).sum := by decide
  have hdescent : baseEnd_163653 < baseStart_163653 := by decide
  rcases family_descends (prefixWord ++ tailWord_163653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163668 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_163668 : Nat := 118140960795 + 163668 * 2 ^ 59
def prefixEnd_163668 : Nat := 4983230072969 + 3 ^ 40 * 163668 * 2
def baseEnd_163668 : Nat := 56026901173447254598207

theorem tailTrace_163668 : CollatzResearch.WordTrace tailWord_163668 prefixEnd_163668 56026901173447254598207 := by
  unfold tailWord_163668
  simp only [CollatzResearch.WordTrace]
  refine ⟨2984731185533131557057829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3979641580710842076077105 2984731185533131557057829)
  ·
    refine ⟨559637097287462166948343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2984731185533131557057829 559637097287462166948343)
    ·
      refine ⟨839455645931193250422515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 559637097287462166948343 839455645931193250422515)
      ·
        refine ⟨1259183468896789875633773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839455645931193250422515 1259183468896789875633773)
        ·
          refine ⟨472193800836296203362665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1259183468896789875633773 472193800836296203362665)
          ·
            refine ⟨354145350627222152521999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 472193800836296203362665 354145350627222152521999)
            ·
              refine ⟨531218025940833228782999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354145350627222152521999 531218025940833228782999)
              ·
                refine ⟨796827038911249843174499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531218025940833228782999 796827038911249843174499)
                ·
                  refine ⟨1195240558366874764761749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796827038911249843174499 1195240558366874764761749)
                  ·
                    refine ⟨56026901173447254598207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1195240558366874764761749 56026901173447254598207)
                    ·
                      rfl

theorem cell22_163668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_163668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163668 prefixEnd_163668 := by exact prefixLift 163668
  have htrace : WordTrace (prefixWord ++ tailWord_163668) baseStart_163668 baseEnd_163668 := by
    simpa [prefixWord, tailWord_163668, baseEnd_163668] using wordTrace_append hprefix tailTrace_163668
  have hstable : (prefixWord ++ tailWord_163668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163668).length < 2 ^ (prefixWord ++ tailWord_163668).sum := by decide
  have hdescent : baseEnd_163668 < baseStart_163668 := by decide
  rcases family_descends (prefixWord ++ tailWord_163668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163734 : List Nat := [5, 3, 1, 1, 3, 1, 8]
def baseStart_163734 : Nat := 118140960795 + 163734 * 2 ^ 59
def prefixEnd_163734 : Nat := 4983230072969 + 3 ^ 40 * 163734 * 2
def baseEnd_163734 : Nat := 2075907197120188238815

theorem tailTrace_163734 : CollatzResearch.WordTrace tailWord_163734 prefixEnd_163734 2075907197120188238815 := by
  unfold tailWord_163734
  simp only [CollatzResearch.WordTrace]
  refine ⟨373241849301697274126141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3981246392551437590678837 373241849301697274126141)
  ·
    refine ⟨139965693488136477797303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 373241849301697274126141 139965693488136477797303)
    ·
      refine ⟨209948540232204716695955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139965693488136477797303 209948540232204716695955)
      ·
        refine ⟨314922810348307075043933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209948540232204716695955 314922810348307075043933)
        ·
          refine ⟨118096053880615153141475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 314922810348307075043933 118096053880615153141475)
          ·
            refine ⟨177144080820922729712213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118096053880615153141475 177144080820922729712213)
            ·
              refine ⟨2075907197120188238815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 177144080820922729712213 2075907197120188238815)
              ·
                rfl

theorem cell22_163734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 8].length) (baseStart_163734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163734 prefixEnd_163734 := by exact prefixLift 163734
  have htrace : WordTrace (prefixWord ++ tailWord_163734) baseStart_163734 baseEnd_163734 := by
    simpa [prefixWord, tailWord_163734, baseEnd_163734] using wordTrace_append hprefix tailTrace_163734
  have hstable : (prefixWord ++ tailWord_163734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163734).length < 2 ^ (prefixWord ++ tailWord_163734).sum := by decide
  have hdescent : baseEnd_163734 < baseStart_163734 := by decide
  rcases family_descends (prefixWord ++ tailWord_163734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163788 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 3, 5]
def baseStart_163788 : Nat := 118140960795 + 163788 * 2 ^ 59
def prefixEnd_163788 : Nat := 4983230072969 + 3 ^ 40 * 163788 * 2
def baseEnd_163788 : Nat := 56067979625806941597839

theorem tailTrace_163788 : CollatzResearch.WordTrace tailWord_163788 prefixEnd_163788 56067979625806941597839 := by
  unfold tailWord_163788
  simp only [CollatzResearch.WordTrace]
  refine ⟨2986919565315761804242009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3982559420421015738989345 2986919565315761804242009)
  ·
    refine ⟨2240189673986821353181507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2986919565315761804242009 2240189673986821353181507)
    ·
      refine ⟨3360284510980232029772261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2240189673986821353181507 3360284510980232029772261)
      ·
        refine ⟨630053345808793505582299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3360284510980232029772261 630053345808793505582299)
        ·
          refine ⟨945080018713190258373449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630053345808793505582299 945080018713190258373449)
          ·
            refine ⟨708810014034892693780087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 945080018713190258373449 708810014034892693780087)
            ·
              refine ⟨1063215021052339040670131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708810014034892693780087 1063215021052339040670131)
              ·
                refine ⟨1594822531578508561005197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1063215021052339040670131 1594822531578508561005197)
                ·
                  refine ⟨598058449341940710376949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1594822531578508561005197 598058449341940710376949)
                  ·
                    refine ⟨56067979625806941597839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 598058449341940710376949 56067979625806941597839)
                    ·
                      rfl

theorem cell22_163788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_163788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163788 prefixEnd_163788 := by exact prefixLift 163788
  have htrace : WordTrace (prefixWord ++ tailWord_163788) baseStart_163788 baseEnd_163788 := by
    simpa [prefixWord, tailWord_163788, baseEnd_163788] using wordTrace_append hprefix tailTrace_163788
  have hstable : (prefixWord ++ tailWord_163788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163788).length < 2 ^ (prefixWord ++ tailWord_163788).sum := by decide
  have hdescent : baseEnd_163788 < baseStart_163788 := by decide
  rcases family_descends (prefixWord ++ tailWord_163788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163790 : List Nat := [4, 1, 1, 1, 2, 2, 2, 5, 4]
def baseStart_163790 : Nat := 118140960795 + 163790 * 2 ^ 59
def prefixEnd_163790 : Nat := 4983230072969 + 3 ^ 40 * 163790 * 2
def baseEnd_163790 : Nat := 18689554755559867682611

theorem tailTrace_163790 : CollatzResearch.WordTrace tailWord_163790 prefixEnd_163790 18689554755559867682611 := by
  unfold tailWord_163790
  simp only [CollatzResearch.WordTrace]
  refine ⟨746739009578034743757103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3982608051082851966704549 746739009578034743757103)
  ·
    refine ⟨1120108514367052115635655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 746739009578034743757103 1120108514367052115635655)
    ·
      refine ⟨1680162771550578173453483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1120108514367052115635655 1680162771550578173453483)
      ·
        refine ⟨2520244157325867260180225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1680162771550578173453483 2520244157325867260180225)
        ·
          refine ⟨1890183117994400445135169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2520244157325867260180225 1890183117994400445135169)
          ·
            refine ⟨1417637338495800333851377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1890183117994400445135169 1417637338495800333851377)
            ·
              refine ⟨1063228003871850250388533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1417637338495800333851377 1063228003871850250388533)
              ·
                refine ⟨99677625362985960973925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1063228003871850250388533 99677625362985960973925)
                ·
                  refine ⟨18689554755559867682611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99677625362985960973925 18689554755559867682611)
                  ·
                    rfl

theorem cell22_163790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_163790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163790 prefixEnd_163790 := by exact prefixLift 163790
  have htrace : WordTrace (prefixWord ++ tailWord_163790) baseStart_163790 baseEnd_163790 := by
    simpa [prefixWord, tailWord_163790, baseEnd_163790] using wordTrace_append hprefix tailTrace_163790
  have hstable : (prefixWord ++ tailWord_163790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163790).length < 2 ^ (prefixWord ++ tailWord_163790).sum := by decide
  have hdescent : baseEnd_163790 < baseStart_163790 := by decide
  rcases family_descends (prefixWord ++ tailWord_163790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163801 : List Nat := [1, 2, 1, 2, 16]
def baseStart_163801 : Nat := 118140960795 + 163801 * 2 ^ 59
def prefixEnd_163801 : Nat := 4983230072969 + 3 ^ 40 * 163801 * 2
def baseEnd_163801 : Nat := 230750739882630621493

theorem tailTrace_163801 : CollatzResearch.WordTrace tailWord_163801 prefixEnd_163801 230750739882630621493 := by
  unfold tailWord_163801
  simp only [CollatzResearch.WordTrace]
  refine ⟨5974313279584426828707257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3982875519722951219138171 5974313279584426828707257)
  ·
    refine ⟨4480734959688320121530443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5974313279584426828707257 4480734959688320121530443)
    ·
      refine ⟨6721102439532480182295665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4480734959688320121530443 6721102439532480182295665)
      ·
        refine ⟨5040826829649360136721749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6721102439532480182295665 5040826829649360136721749)
        ·
          refine ⟨230750739882630621493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 5040826829649360136721749 230750739882630621493)
          ·
            rfl

theorem cell22_163801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 16].length) (baseStart_163801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163801 prefixEnd_163801 := by exact prefixLift 163801
  have htrace : WordTrace (prefixWord ++ tailWord_163801) baseStart_163801 baseEnd_163801 := by
    simpa [prefixWord, tailWord_163801, baseEnd_163801] using wordTrace_append hprefix tailTrace_163801
  have hstable : (prefixWord ++ tailWord_163801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163801).length < 2 ^ (prefixWord ++ tailWord_163801).sum := by decide
  have hdescent : baseEnd_163801 < baseStart_163801 := by decide
  rcases family_descends (prefixWord ++ tailWord_163801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163807 : List Nat := [1, 1, 2, 3, 4, 1, 4, 2, 4]
def baseStart_163807 : Nat := 118140960795 + 163807 * 2 ^ 59
def prefixEnd_163807 : Nat := 4983230072969 + 3 ^ 40 * 163807 * 2
def baseEnd_163807 : Nat := 18691494571365741790927

theorem tailTrace_163807 : CollatzResearch.WordTrace tailWord_163807 prefixEnd_163807 18691494571365741790927 := by
  unfold tailWord_163807
  simp only [CollatzResearch.WordTrace]
  refine ⟨5974532117562689853425675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3983021411708459902283783 5974532117562689853425675)
  ·
    refine ⟨8961798176344034780138513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5974532117562689853425675 8961798176344034780138513)
    ·
      refine ⟨6721348632258026085103885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8961798176344034780138513 6721348632258026085103885)
      ·
        refine ⟨2520505737096759781913957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6721348632258026085103885 2520505737096759781913957)
        ·
          refine ⟨472594825705642459108867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2520505737096759781913957 472594825705642459108867)
          ·
            refine ⟨708892238558463688663301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472594825705642459108867 708892238558463688663301)
            ·
              refine ⟨132917294729711941624369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 708892238558463688663301 132917294729711941624369)
              ·
                refine ⟨99687971047283956218277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132917294729711941624369 99687971047283956218277)
                ·
                  refine ⟨18691494571365741790927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99687971047283956218277 18691494571365741790927)
                  ·
                    rfl

theorem cell22_163807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 4].length) (baseStart_163807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163807 prefixEnd_163807 := by exact prefixLift 163807
  have htrace : WordTrace (prefixWord ++ tailWord_163807) baseStart_163807 baseEnd_163807 := by
    simpa [prefixWord, tailWord_163807, baseEnd_163807] using wordTrace_append hprefix tailTrace_163807
  have hstable : (prefixWord ++ tailWord_163807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163807).length < 2 ^ (prefixWord ++ tailWord_163807).sum := by decide
  have hdescent : baseEnd_163807 < baseStart_163807 := by decide
  rcases family_descends (prefixWord ++ tailWord_163807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163822 : List Nat := [4, 1, 2, 1, 3, 1, 2, 3, 2, 3]
def baseStart_163822 : Nat := 118140960795 + 163822 * 2 ^ 59
def prefixEnd_163822 : Nat := 4983230072969 + 3 ^ 40 * 163822 * 2
def baseEnd_163822 : Nat := 56079618520642186247735

theorem tailTrace_163822 : CollatzResearch.WordTrace tailWord_163822 prefixEnd_163822 56079618520642186247735 := by
  unfold tailWord_163822
  simp only [CollatzResearch.WordTrace]
  refine ⟨746884901563543426902715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3983386141672231610147813 746884901563543426902715)
  ·
    refine ⟨1120327352345315140354073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 746884901563543426902715 1120327352345315140354073)
    ·
      refine ⟨840245514258986355265555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1120327352345315140354073 840245514258986355265555)
      ·
        refine ⟨1260368271388479532898333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840245514258986355265555 1260368271388479532898333)
        ·
          refine ⟨472638101770679824836875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1260368271388479532898333 472638101770679824836875)
          ·
            refine ⟨708957152656019737255313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472638101770679824836875 708957152656019737255313)
            ·
              refine ⟨531717864492014802941485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708957152656019737255313 531717864492014802941485)
              ·
                refine ⟨199394199184505551103057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 531717864492014802941485 199394199184505551103057)
                ·
                  refine ⟨149545649388379163327293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199394199184505551103057 149545649388379163327293)
                  ·
                    refine ⟨56079618520642186247735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149545649388379163327293 56079618520642186247735)
                    ·
                      rfl

theorem cell22_163822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_163822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163822 prefixEnd_163822 := by exact prefixLift 163822
  have htrace : WordTrace (prefixWord ++ tailWord_163822) baseStart_163822 baseEnd_163822 := by
    simpa [prefixWord, tailWord_163822, baseEnd_163822] using wordTrace_append hprefix tailTrace_163822
  have hstable : (prefixWord ++ tailWord_163822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163822).length < 2 ^ (prefixWord ++ tailWord_163822).sum := by decide
  have hdescent : baseEnd_163822 < baseStart_163822 := by decide
  rcases family_descends (prefixWord ++ tailWord_163822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163925 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 6]
def baseStart_163925 : Nat := 118140960795 + 163925 * 2 ^ 59
def prefixEnd_163925 : Nat := 4983230072969 + 3 ^ 40 * 163925 * 2
def baseEnd_163925 : Nat := 18704959175194750307473

theorem tailTrace_163925 : CollatzResearch.WordTrace tailWord_163925 prefixEnd_163925 18704959175194750307473 := by
  unfold tailWord_163925
  simp only [CollatzResearch.WordTrace]
  refine ⟨5978835931135196006221229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3985890620756797337480819 5978835931135196006221229)
  ·
    refine ⟨2242063474175698502332961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5978835931135196006221229 2242063474175698502332961)
    ·
      refine ⟨1681547605631773876749721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2242063474175698502332961 1681547605631773876749721)
      ·
        refine ⟨1261160704223830407562291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1681547605631773876749721 1261160704223830407562291)
        ·
          refine ⟨1891741056335745611343437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1261160704223830407562291 1891741056335745611343437)
          ·
            refine ⟨709402896125904604253789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1891741056335745611343437 709402896125904604253789)
            ·
              refine ⟨266026086047214226595171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 709402896125904604253789 266026086047214226595171)
              ·
                refine ⟨399039129070821339892757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266026086047214226595171 399039129070821339892757)
                ·
                  refine ⟨18704959175194750307473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 399039129070821339892757 18704959175194750307473)
                  ·
                    rfl

theorem cell22_163925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_163925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163925 prefixEnd_163925 := by exact prefixLift 163925
  have htrace : WordTrace (prefixWord ++ tailWord_163925) baseStart_163925 baseEnd_163925 := by
    simpa [prefixWord, tailWord_163925, baseEnd_163925] using wordTrace_append hprefix tailTrace_163925
  have hstable : (prefixWord ++ tailWord_163925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163925).length < 2 ^ (prefixWord ++ tailWord_163925).sum := by decide
  have hdescent : baseEnd_163925 < baseStart_163925 := by decide
  rcases family_descends (prefixWord ++ tailWord_163925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163953 : List Nat := [1, 2, 2, 2, 1, 1, 3, 10]
def baseStart_163953 : Nat := 118140960795 + 163953 * 2 ^ 59
def prefixEnd_163953 : Nat := 4983230072969 + 3 ^ 40 * 163953 * 2
def baseEnd_163953 : Nat := 6236051388644612358037

theorem tailTrace_163953 : CollatzResearch.WordTrace tailWord_163953 prefixEnd_163953 6236051388644612358037 := by
  unfold tailWord_163953
  simp only [CollatzResearch.WordTrace]
  refine ⟨5979857175033756788240513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3986571450022504525493675 5979857175033756788240513)
  ·
    refine ⟨4484892881275317591180385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5979857175033756788240513 4484892881275317591180385)
    ·
      refine ⟨3363669660956488193385289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4484892881275317591180385 3363669660956488193385289)
      ·
        refine ⟨2522752245717366145038967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3363669660956488193385289 2522752245717366145038967)
        ·
          refine ⟨3784128368576049217558451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2522752245717366145038967 3784128368576049217558451)
          ·
            refine ⟨5676192552864073826337677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3784128368576049217558451 5676192552864073826337677)
            ·
              refine ⟨2128572207324027684876629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5676192552864073826337677 2128572207324027684876629)
              ·
                refine ⟨6236051388644612358037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2128572207324027684876629 6236051388644612358037)
                ·
                  rfl

theorem cell22_163953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 10].length) (baseStart_163953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163953 prefixEnd_163953 := by exact prefixLift 163953
  have htrace : WordTrace (prefixWord ++ tailWord_163953) baseStart_163953 baseEnd_163953 := by
    simpa [prefixWord, tailWord_163953, baseEnd_163953] using wordTrace_append hprefix tailTrace_163953
  have hstable : (prefixWord ++ tailWord_163953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163953).length < 2 ^ (prefixWord ++ tailWord_163953).sum := by decide
  have hdescent : baseEnd_163953 < baseStart_163953 := by decide
  rcases family_descends (prefixWord ++ tailWord_163953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163976 : List Nat := [2, 1, 3, 4, 1, 3, 2, 2, 4]
def baseStart_163976 : Nat := 118140960795 + 163976 * 2 ^ 59
def prefixEnd_163976 : Nat := 4983230072969 + 3 ^ 40 * 163976 * 2
def baseEnd_163976 : Nat := 18710778622612372632421

theorem tailTrace_163976 : CollatzResearch.WordTrace tailWord_163976 prefixEnd_163976 18710778622612372632421 := by
  unfold tailWord_163976
  simp only [CollatzResearch.WordTrace]
  refine ⟨2990348026975215858163891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3987130702633621144218521 2990348026975215858163891)
  ·
    refine ⟨4485522040462823787245837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2990348026975215858163891 4485522040462823787245837)
    ·
      refine ⟨1682070765173558920217189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4485522040462823787245837 1682070765173558920217189)
      ·
        refine ⟨315388268470042297540723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1682070765173558920217189 315388268470042297540723)
        ·
          refine ⟨473082402705063446311085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315388268470042297540723 473082402705063446311085)
          ·
            refine ⟨177405901014398792366657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 473082402705063446311085 177405901014398792366657)
            ·
              refine ⟨133054425760799094274993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177405901014398792366657 133054425760799094274993)
              ·
                refine ⟨99790819320599320706245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133054425760799094274993 99790819320599320706245)
                ·
                  refine ⟨18710778622612372632421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99790819320599320706245 18710778622612372632421)
                  ·
                    rfl

theorem cell22_163976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 4].length) (baseStart_163976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163976 prefixEnd_163976 := by exact prefixLift 163976
  have htrace : WordTrace (prefixWord ++ tailWord_163976) baseStart_163976 baseEnd_163976 := by
    simpa [prefixWord, tailWord_163976, baseEnd_163976] using wordTrace_append hprefix tailTrace_163976
  have hstable : (prefixWord ++ tailWord_163976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163976).length < 2 ^ (prefixWord ++ tailWord_163976).sum := by decide
  have hdescent : baseEnd_163976 < baseStart_163976 := by decide
  rcases family_descends (prefixWord ++ tailWord_163976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163985 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 9, 3]
def baseStart_163985 : Nat := 118140960795 + 163985 * 2 ^ 59
def prefixEnd_163985 : Nat := 4983230072969 + 3 ^ 40 * 163985 * 2
def baseEnd_163985 : Nat := 56135416751764094422235

theorem tailTrace_163985 : CollatzResearch.WordTrace tailWord_163985 prefixEnd_163985 56135416751764094422235 := by
  unfold tailWord_163985
  simp only [CollatzResearch.WordTrace]
  refine ⟨5981024310917826253405409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3987349540611884168936939 5981024310917826253405409)
  ·
    refine ⟨4485768233188369690054057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5981024310917826253405409 4485768233188369690054057)
    ·
      refine ⟨3364326174891277267540543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4485768233188369690054057 3364326174891277267540543)
      ·
        refine ⟨5046489262336915901310815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3364326174891277267540543 5046489262336915901310815)
        ·
          refine ⟨7569733893505373851966223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5046489262336915901310815 7569733893505373851966223)
          ·
            refine ⟨11354600840258060777949335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7569733893505373851966223 11354600840258060777949335)
            ·
              refine ⟨17031901260387091166924003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11354600840258060777949335 17031901260387091166924003)
              ·
                refine ⟨25547851890580636750386005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17031901260387091166924003 25547851890580636750386005)
                ·
                  refine ⟨149694444671370918459293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25547851890580636750386005 149694444671370918459293)
                  ·
                    refine ⟨56135416751764094422235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149694444671370918459293 56135416751764094422235)
                    ·
                      rfl

theorem cell22_163985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_163985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_163985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_163985 prefixEnd_163985 := by exact prefixLift 163985
  have htrace : WordTrace (prefixWord ++ tailWord_163985) baseStart_163985 baseEnd_163985 := by
    simpa [prefixWord, tailWord_163985, baseEnd_163985] using wordTrace_append hprefix tailTrace_163985
  have hstable : (prefixWord ++ tailWord_163985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163985).length < 2 ^ (prefixWord ++ tailWord_163985).sum := by decide
  have hdescent : baseEnd_163985 < baseStart_163985 := by decide
  rcases family_descends (prefixWord ++ tailWord_163985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164032 : List Nat := [2, 1, 1, 2, 5, 1, 3, 2, 5]
def baseStart_164032 : Nat := 118140960795 + 164032 * 2 ^ 59
def prefixEnd_164032 : Nat := 4983230072969 + 3 ^ 40 * 164032 * 2
def baseEnd_164032 : Nat := 18717168604090546165697

theorem tailTrace_164032 : CollatzResearch.WordTrace tailWord_164032 prefixEnd_164032 18717168604090546165697 := by
  unfold tailWord_164032
  simp only [CollatzResearch.WordTrace]
  refine ⟨2991369270873776640183175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3988492361165035520244233 2991369270873776640183175)
  ·
    refine ⟨4487053906310664960274763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2991369270873776640183175 4487053906310664960274763)
    ·
      refine ⟨6730580859465997440412145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4487053906310664960274763 6730580859465997440412145)
      ·
        refine ⟨5047935644599498080309109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6730580859465997440412145 5047935644599498080309109)
        ·
          refine ⟨473243966681202945028979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5047935644599498080309109 473243966681202945028979)
          ·
            refine ⟨709865950021804417543469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473243966681202945028979 709865950021804417543469)
            ·
              refine ⟨266199731258176656578801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 709865950021804417543469 266199731258176656578801)
              ·
                refine ⟨199649798443632492434101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266199731258176656578801 199649798443632492434101)
                ·
                  refine ⟨18717168604090546165697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 199649798443632492434101 18717168604090546165697)
                  ·
                    rfl

theorem cell22_164032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 5].length) (baseStart_164032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164032 prefixEnd_164032 := by exact prefixLift 164032
  have htrace : WordTrace (prefixWord ++ tailWord_164032) baseStart_164032 baseEnd_164032 := by
    simpa [prefixWord, tailWord_164032, baseEnd_164032] using wordTrace_append hprefix tailTrace_164032
  have hstable : (prefixWord ++ tailWord_164032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164032).length < 2 ^ (prefixWord ++ tailWord_164032).sum := by decide
  have hdescent : baseEnd_164032 < baseStart_164032 := by decide
  rcases family_descends (prefixWord ++ tailWord_164032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164036 : List Nat := [2, 3, 3, 1, 2, 1, 2, 4, 1, 3]
def baseStart_164036 : Nat := 118140960795 + 164036 * 2 ^ 59
def prefixEnd_164036 : Nat := 4983230072969 + 3 ^ 40 * 164036 * 2
def baseEnd_164036 : Nat := 56152875094016961397079

theorem tailTrace_164036 : CollatzResearch.WordTrace tailWord_164036 prefixEnd_164036 56152875094016961397079 := by
  unfold tailWord_164036
  simp only [CollatzResearch.WordTrace]
  refine ⟨2991442216866530981755981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3988589622488707975674641 2991442216866530981755981)
  ·
    refine ⟨1121790831324949118158493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2991442216866530981755981 1121790831324949118158493)
    ·
      refine ⟨420671561746855919309435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1121790831324949118158493 420671561746855919309435)
      ·
        refine ⟨631007342620283878964153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420671561746855919309435 631007342620283878964153)
        ·
          refine ⟨473255506965212909223115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 631007342620283878964153 473255506965212909223115)
          ·
            refine ⟨709883260447819363834673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473255506965212909223115 709883260447819363834673)
            ·
              refine ⟨532412445335864522876005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 709883260447819363834673 532412445335864522876005)
              ·
                refine ⟨99827333500474598039251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 532412445335864522876005 99827333500474598039251)
                ·
                  refine ⟨149741000250711897058877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99827333500474598039251 149741000250711897058877)
                  ·
                    refine ⟨56152875094016961397079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149741000250711897058877 56152875094016961397079)
                    ·
                      rfl

theorem cell22_164036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_164036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164036 prefixEnd_164036 := by exact prefixLift 164036
  have htrace : WordTrace (prefixWord ++ tailWord_164036) baseStart_164036 baseEnd_164036 := by
    simpa [prefixWord, tailWord_164036, baseEnd_164036] using wordTrace_append hprefix tailTrace_164036
  have hstable : (prefixWord ++ tailWord_164036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164036).length < 2 ^ (prefixWord ++ tailWord_164036).sum := by decide
  have hdescent : baseEnd_164036 < baseStart_164036 := by decide
  rcases family_descends (prefixWord ++ tailWord_164036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164075 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 3, 5]
def baseStart_164075 : Nat := 118140960795 + 164075 * 2 ^ 59
def prefixEnd_164075 : Nat := 4983230072969 + 3 ^ 40 * 164075 * 2
def baseEnd_164075 : Nat := 56166225591033859671959

theorem tailTrace_164075 : CollatzResearch.WordTrace tailWord_164075 prefixEnd_164075 56166225591033859671959 := by
  unfold tailWord_164075
  simp only [CollatzResearch.WordTrace]
  refine ⟨5984306880591771624181679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3989537920394514416121119 5984306880591771624181679)
  ·
    refine ⟨8976460320887657436272519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5984306880591771624181679 8976460320887657436272519)
    ·
      refine ⟨13464690481331486154408779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8976460320887657436272519 13464690481331486154408779)
      ·
        refine ⟨20197035721997229231613169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13464690481331486154408779 20197035721997229231613169)
        ·
          refine ⟨15147776791497921923709877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20197035721997229231613169 15147776791497921923709877)
          ·
            refine ⟨1420104074202930180347801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15147776791497921923709877 1420104074202930180347801)
            ·
              refine ⟨1065078055652197635260851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1420104074202930180347801 1065078055652197635260851)
              ·
                refine ⟨1597617083478296452891277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065078055652197635260851 1597617083478296452891277)
                ·
                  refine ⟨599106406304361169834229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1597617083478296452891277 599106406304361169834229)
                  ·
                    refine ⟨56166225591033859671959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 599106406304361169834229 56166225591033859671959)
                    ·
                      rfl

theorem cell22_164075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 5].length) (baseStart_164075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164075 prefixEnd_164075 := by exact prefixLift 164075
  have htrace : WordTrace (prefixWord ++ tailWord_164075) baseStart_164075 baseEnd_164075 := by
    simpa [prefixWord, tailWord_164075, baseEnd_164075] using wordTrace_append hprefix tailTrace_164075
  have hstable : (prefixWord ++ tailWord_164075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164075).length < 2 ^ (prefixWord ++ tailWord_164075).sum := by decide
  have hdescent : baseEnd_164075 < baseStart_164075 := by decide
  rcases family_descends (prefixWord ++ tailWord_164075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164105 : List Nat := [1, 2, 1, 1, 3, 4, 1, 9]
def baseStart_164105 : Nat := 118140960795 + 164105 * 2 ^ 59
def prefixEnd_164105 : Nat := 4983230072969 + 3 ^ 40 * 164105 * 2
def baseEnd_164105 : Nat := 6241832800458197935763

theorem tailTrace_164105 : CollatzResearch.WordTrace tailWord_164105 prefixEnd_164105 6241832800458197935763 := by
  unfold tailWord_164105
  simp only [CollatzResearch.WordTrace]
  refine ⟨5985401070483086747773769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3990267380322057831849179 5985401070483086747773769)
  ·
    refine ⟨4489050802862315060830327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5985401070483086747773769 4489050802862315060830327)
    ·
      refine ⟨6733576204293472591245491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4489050802862315060830327 6733576204293472591245491)
      ·
        refine ⟨10100364306440208886868237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6733576204293472591245491 10100364306440208886868237)
        ·
          refine ⟨3787636614915078332575589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10100364306440208886868237 3787636614915078332575589)
          ·
            refine ⟨710181865296577187357923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3787636614915078332575589 710181865296577187357923)
            ·
              refine ⟨1065272797944865781036885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710181865296577187357923 1065272797944865781036885)
              ·
                refine ⟨6241832800458197935763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1065272797944865781036885 6241832800458197935763)
                ·
                  rfl

theorem cell22_164105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 9].length) (baseStart_164105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164105 prefixEnd_164105 := by exact prefixLift 164105
  have htrace : WordTrace (prefixWord ++ tailWord_164105) baseStart_164105 baseEnd_164105 := by
    simpa [prefixWord, tailWord_164105, baseEnd_164105] using wordTrace_append hprefix tailTrace_164105
  have hstable : (prefixWord ++ tailWord_164105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164105).length < 2 ^ (prefixWord ++ tailWord_164105).sum := by decide
  have hdescent : baseEnd_164105 < baseStart_164105 := by decide
  rcases family_descends (prefixWord ++ tailWord_164105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164126 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_164126 : Nat := 118140960795 + 164126 * 2 ^ 59
def prefixEnd_164126 : Nat := 4983230072969 + 3 ^ 40 * 164126 * 2
def baseEnd_164126 : Nat := 56183683933286726646803

theorem tailTrace_164126 : CollatzResearch.WordTrace tailWord_164126 prefixEnd_164126 56183683933286726646803 := by
  unfold tailWord_164126
  simp only [CollatzResearch.WordTrace]
  refine ⟨748270875425875916786029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3990778002271338222858821 748270875425875916786029)
  ·
    refine ⟨280601578284703468794761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 748270875425875916786029 280601578284703468794761)
    ·
      refine ⟨210451183713527601596071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280601578284703468794761 210451183713527601596071)
      ·
        refine ⟨315676775570291402394107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210451183713527601596071 315676775570291402394107)
        ·
          refine ⟨473515163355437103591161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315676775570291402394107 473515163355437103591161)
          ·
            refine ⟨355136372516577827693371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473515163355437103591161 355136372516577827693371)
            ·
              refine ⟨532704558774866741540057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355136372516577827693371 532704558774866741540057)
              ·
                refine ⟨399528419081150056155043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532704558774866741540057 399528419081150056155043)
                ·
                  refine ⟨599292628621725084232565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 399528419081150056155043 599292628621725084232565)
                  ·
                    refine ⟨56183683933286726646803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 599292628621725084232565 56183683933286726646803)
                    ·
                      rfl

theorem cell22_164126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_164126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164126 prefixEnd_164126 := by exact prefixLift 164126
  have htrace : WordTrace (prefixWord ++ tailWord_164126) baseStart_164126 baseEnd_164126 := by
    simpa [prefixWord, tailWord_164126, baseEnd_164126] using wordTrace_append hprefix tailTrace_164126
  have hstable : (prefixWord ++ tailWord_164126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164126).length < 2 ^ (prefixWord ++ tailWord_164126).sum := by decide
  have hdescent : baseEnd_164126 < baseStart_164126 := by decide
  rcases family_descends (prefixWord ++ tailWord_164126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164167 : List Nat := [1, 1, 4, 1, 2, 2, 1, 5, 5]
def baseStart_164167 : Nat := 118140960795 + 164167 * 2 ^ 59
def prefixEnd_164167 : Nat := 4983230072969 + 3 ^ 40 * 164167 * 2
def baseEnd_164167 : Nat := 18732573023725428790559

theorem tailTrace_164167 : CollatzResearch.WordTrace tailWord_164167 prefixEnd_164167 18732573023725428790559 := by
  unfold tailWord_164167
  simp only [CollatzResearch.WordTrace]
  refine ⟨5987662396258471336530755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3991774930838980891020503 5987662396258471336530755)
  ·
    refine ⟨8981493594387707004796133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5987662396258471336530755 8981493594387707004796133)
    ·
      refine ⟨1684030048947695063399275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8981493594387707004796133 1684030048947695063399275)
      ·
        refine ⟨2526045073421542595098913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1684030048947695063399275 2526045073421542595098913)
        ·
          refine ⟨1894533805066156946324185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2526045073421542595098913 1894533805066156946324185)
          ·
            refine ⟨1420900353799617709743139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1894533805066156946324185 1420900353799617709743139)
            ·
              refine ⟨2131350530699426564614709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1420900353799617709743139 2131350530699426564614709)
              ·
                refine ⟨199814112253071240432629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2131350530699426564614709 199814112253071240432629)
                ·
                  refine ⟨18732573023725428790559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 199814112253071240432629 18732573023725428790559)
                  ·
                    rfl

theorem cell22_164167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 5].length) (baseStart_164167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164167 prefixEnd_164167 := by exact prefixLift 164167
  have htrace : WordTrace (prefixWord ++ tailWord_164167) baseStart_164167 baseEnd_164167 := by
    simpa [prefixWord, tailWord_164167, baseEnd_164167] using wordTrace_append hprefix tailTrace_164167
  have hstable : (prefixWord ++ tailWord_164167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164167).length < 2 ^ (prefixWord ++ tailWord_164167).sum := by decide
  have hdescent : baseEnd_164167 < baseStart_164167 := by decide
  rcases family_descends (prefixWord ++ tailWord_164167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164259 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 2, 4]
def baseStart_164259 : Nat := 118140960795 + 164259 * 2 ^ 59
def prefixEnd_164259 : Nat := 4983230072969 + 3 ^ 40 * 164259 * 2
def baseEnd_164259 : Nat := 56229212551318713071395

theorem tailTrace_164259 : CollatzResearch.WordTrace tailWord_164259 prefixEnd_164259 56229212551318713071395 := by
  unfold tailWord_164259
  simp only [CollatzResearch.WordTrace]
  refine ⟨5991017911925171048879831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3994011941283447365919887 5991017911925171048879831)
  ·
    refine ⟨8986526867887756573319747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5991017911925171048879831 8986526867887756573319747)
    ·
      refine ⟨13479790301831634859979621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8986526867887756573319747 13479790301831634859979621)
      ·
        refine ⟨2527460681593431536246179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13479790301831634859979621 2527460681593431536246179)
        ·
          refine ⟨3791191022390147304369269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2527460681593431536246179 3791191022390147304369269)
          ·
            refine ⟨355424158349076309784619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3791191022390147304369269 355424158349076309784619)
            ·
              refine ⟨533136237523614464676929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355424158349076309784619 533136237523614464676929)
              ·
                refine ⟨399852178142710848507697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 533136237523614464676929 399852178142710848507697)
                ·
                  refine ⟨299889133607033136380773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399852178142710848507697 299889133607033136380773)
                  ·
                    refine ⟨56229212551318713071395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 299889133607033136380773 56229212551318713071395)
                    ·
                      rfl

theorem cell22_164259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 4].length) (baseStart_164259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164259 prefixEnd_164259 := by exact prefixLift 164259
  have htrace : WordTrace (prefixWord ++ tailWord_164259) baseStart_164259 baseEnd_164259 := by
    simpa [prefixWord, tailWord_164259, baseEnd_164259] using wordTrace_append hprefix tailTrace_164259
  have hstable : (prefixWord ++ tailWord_164259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164259).length < 2 ^ (prefixWord ++ tailWord_164259).sum := by decide
  have hdescent : baseEnd_164259 < baseStart_164259 := by decide
  rcases family_descends (prefixWord ++ tailWord_164259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164263 : List Nat := [1, 1, 6, 1, 1, 3, 3, 2, 4]
def baseStart_164263 : Nat := 118140960795 + 164263 * 2 ^ 59
def prefixEnd_164263 : Nat := 4983230072969 + 3 ^ 40 * 164263 * 2
def baseEnd_164263 : Nat := 18743527277688011990461

theorem tailTrace_164263 : CollatzResearch.WordTrace tailWord_164263 prefixEnd_164263 18743527277688011990461 := by
  unfold tailWord_164263
  simp only [CollatzResearch.WordTrace]
  refine ⟨5991163803910679732025443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3994109202607119821350295 5991163803910679732025443)
  ·
    refine ⟨8986745705866019598038165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5991163803910679732025443 8986745705866019598038165)
    ·
      refine ⟨421253704962469668658039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8986745705866019598038165 421253704962469668658039)
      ·
        refine ⟨631880557443704502987059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421253704962469668658039 631880557443704502987059)
        ·
          refine ⟨947820836165556754480589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631880557443704502987059 947820836165556754480589)
          ·
            refine ⟨355432813562083782930221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 947820836165556754480589 355432813562083782930221)
            ·
              refine ⟨133287305085781418598833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 355432813562083782930221 133287305085781418598833)
              ·
                refine ⟨99965478814336063949125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133287305085781418598833 99965478814336063949125)
                ·
                  refine ⟨18743527277688011990461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99965478814336063949125 18743527277688011990461)
                  ·
                    rfl

theorem cell22_164263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 4].length) (baseStart_164263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164263 prefixEnd_164263 := by exact prefixLift 164263
  have htrace : WordTrace (prefixWord ++ tailWord_164263) baseStart_164263 baseEnd_164263 := by
    simpa [prefixWord, tailWord_164263, baseEnd_164263] using wordTrace_append hprefix tailTrace_164263
  have hstable : (prefixWord ++ tailWord_164263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164263).length < 2 ^ (prefixWord ++ tailWord_164263).sum := by decide
  have hdescent : baseEnd_164263 < baseStart_164263 := by decide
  rcases family_descends (prefixWord ++ tailWord_164263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164319 : List Nat := [1, 1, 2, 3, 3, 2, 1, 4, 5]
def baseStart_164319 : Nat := 118140960795 + 164319 * 2 ^ 59
def prefixEnd_164319 : Nat := 4983230072969 + 3 ^ 40 * 164319 * 2
def baseEnd_164319 : Nat := 18749917259166185523737

theorem tailTrace_164319 : CollatzResearch.WordTrace tailWord_164319 prefixEnd_164319 18749917259166185523737 := by
  unfold tailWord_164319
  simp only [CollatzResearch.WordTrace]
  refine ⟨5993206291707801296064011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3995470861138534197376007 5993206291707801296064011)
  ·
    refine ⟨8989809437561701944096017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5993206291707801296064011 8989809437561701944096017)
    ·
      refine ⟨6742357078171276458072013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8989809437561701944096017 6742357078171276458072013)
      ·
        refine ⟨2528383904314228671777005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6742357078171276458072013 2528383904314228671777005)
        ·
          refine ⟨948143964117835751916377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2528383904314228671777005 948143964117835751916377)
          ·
            refine ⟨711107973088376813937283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 948143964117835751916377 711107973088376813937283)
            ·
              refine ⟨1066661959632565220905925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711107973088376813937283 1066661959632565220905925)
              ·
                refine ⟨199999117431105978919861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1066661959632565220905925 199999117431105978919861)
                ·
                  refine ⟨18749917259166185523737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 199999117431105978919861 18749917259166185523737)
                  ·
                    rfl

theorem cell22_164319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 5].length) (baseStart_164319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164319 prefixEnd_164319 := by exact prefixLift 164319
  have htrace : WordTrace (prefixWord ++ tailWord_164319) baseStart_164319 baseEnd_164319 := by
    simpa [prefixWord, tailWord_164319, baseEnd_164319] using wordTrace_append hprefix tailTrace_164319
  have hstable : (prefixWord ++ tailWord_164319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164319).length < 2 ^ (prefixWord ++ tailWord_164319).sum := by decide
  have hdescent : baseEnd_164319 < baseStart_164319 := by decide
  rcases family_descends (prefixWord ++ tailWord_164319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164334 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_164334 : Nat := 118140960795 + 164334 * 2 ^ 59
def prefixEnd_164334 : Nat := 4983230072969 + 3 ^ 40 * 164334 * 2
def baseEnd_164334 : Nat := 56254886584043517446165

theorem tailTrace_164334 : CollatzResearch.WordTrace tailWord_164334 prefixEnd_164334 56254886584043517446165 := by
  unfold tailWord_164334
  simp only [CollatzResearch.WordTrace]
  refine ⟨749219173331682357232507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3995835591102305905240037 749219173331682357232507)
  ·
    refine ⟨1123828759997523535848761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 749219173331682357232507 1123828759997523535848761)
    ·
      refine ⟨842871569998142651886571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1123828759997523535848761 842871569998142651886571)
      ·
        refine ⟨1264307354997213977829857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842871569998142651886571 1264307354997213977829857)
        ·
          refine ⟨948230516247910483372393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1264307354997213977829857 948230516247910483372393)
          ·
            refine ⟨711172887185932862529295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 948230516247910483372393 711172887185932862529295)
            ·
              refine ⟨1066759330778899293793943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711172887185932862529295 1066759330778899293793943)
              ·
                refine ⟨1600138996168348940690915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066759330778899293793943 1600138996168348940690915)
                ·
                  refine ⟨2400208494252523411036373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600138996168348940690915 2400208494252523411036373)
                  ·
                    refine ⟨56254886584043517446165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2400208494252523411036373 56254886584043517446165)
                    ·
                      rfl

theorem cell22_164334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_164334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164334 prefixEnd_164334 := by exact prefixLift 164334
  have htrace : WordTrace (prefixWord ++ tailWord_164334) baseStart_164334 baseEnd_164334 := by
    simpa [prefixWord, tailWord_164334, baseEnd_164334] using wordTrace_append hprefix tailTrace_164334
  have hstable : (prefixWord ++ tailWord_164334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164334).length < 2 ^ (prefixWord ++ tailWord_164334).sum := by decide
  have hdescent : baseEnd_164334 < baseStart_164334 := by decide
  rcases family_descends (prefixWord ++ tailWord_164334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164349 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_164349 : Nat := 118140960795 + 164349 * 2 ^ 59
def prefixEnd_164349 : Nat := 4983230072969 + 3 ^ 40 * 164349 * 2
def baseEnd_164349 : Nat := 56260021390588478321119

theorem tailTrace_164349 : CollatzResearch.WordTrace tailWord_164349 prefixEnd_164349 56260021390588478321119 := by
  unfold tailWord_164349
  simp only [CollatzResearch.WordTrace]
  refine ⟨5994300481599116419656101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3996200321066077613104067 5994300481599116419656101)
  ·
    refine ⟨1123931340299834328685519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5994300481599116419656101 1123931340299834328685519)
    ·
      refine ⟨1685897010449751493028279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1123931340299834328685519 1685897010449751493028279)
      ·
        refine ⟨2528845515674627239542419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1685897010449751493028279 2528845515674627239542419)
        ·
          refine ⟨3793268273511940859313629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2528845515674627239542419 3793268273511940859313629)
          ·
            refine ⟨1422475602566977822242611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3793268273511940859313629 1422475602566977822242611)
            ·
              refine ⟨2133713403850466733363917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422475602566977822242611 2133713403850466733363917)
              ·
                refine ⟨800142526443925025011469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2133713403850466733363917 800142526443925025011469)
                ·
                  refine ⟨300053447416471884379301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 800142526443925025011469 300053447416471884379301)
                  ·
                    refine ⟨56260021390588478321119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 300053447416471884379301 56260021390588478321119)
                    ·
                      rfl

theorem cell22_164349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_164349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164349 prefixEnd_164349 := by exact prefixLift 164349
  have htrace : WordTrace (prefixWord ++ tailWord_164349) baseStart_164349 baseEnd_164349 := by
    simpa [prefixWord, tailWord_164349, baseEnd_164349] using wordTrace_append hprefix tailTrace_164349
  have hstable : (prefixWord ++ tailWord_164349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164349).length < 2 ^ (prefixWord ++ tailWord_164349).sum := by decide
  have hdescent : baseEnd_164349 < baseStart_164349 := by decide
  rcases family_descends (prefixWord ++ tailWord_164349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164381 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 6]
def baseStart_164381 : Nat := 118140960795 + 164381 * 2 ^ 59
def prefixEnd_164381 : Nat := 4983230072969 + 3 ^ 40 * 164381 * 2
def baseEnd_164381 : Nat := 18756991881517020507007

theorem tailTrace_164381 : CollatzResearch.WordTrace tailWord_164381 prefixEnd_164381 18756991881517020507007 := by
  unfold tailWord_164381
  simp only [CollatzResearch.WordTrace]
  refine ⟨5995467617483185884820997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3996978411655457256547331 5995467617483185884820997)
  ·
    refine ⟨1124150178278097353403937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5995467617483185884820997 1124150178278097353403937)
    ·
      refine ⟨843112633708573015052953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1124150178278097353403937 843112633708573015052953)
      ·
        refine ⟨632334475281429761289715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 843112633708573015052953 632334475281429761289715)
        ·
          refine ⟨948501712922144641934573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632334475281429761289715 948501712922144641934573)
          ·
            refine ⟨355688142345804240725465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 948501712922144641934573 355688142345804240725465)
            ·
              refine ⟨266766106759353180544099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355688142345804240725465 266766106759353180544099)
              ·
                refine ⟨400149160139029770816149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266766106759353180544099 400149160139029770816149)
                ·
                  refine ⟨18756991881517020507007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 400149160139029770816149 18756991881517020507007)
                  ·
                    rfl

theorem cell22_164381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_164381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164381 prefixEnd_164381 := by exact prefixLift 164381
  have htrace : WordTrace (prefixWord ++ tailWord_164381) baseStart_164381 baseEnd_164381 := by
    simpa [prefixWord, tailWord_164381, baseEnd_164381] using wordTrace_append hprefix tailTrace_164381
  have hstable : (prefixWord ++ tailWord_164381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164381).length < 2 ^ (prefixWord ++ tailWord_164381).sum := by decide
  have hdescent : baseEnd_164381 < baseStart_164381 := by decide
  rcases family_descends (prefixWord ++ tailWord_164381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164396 : List Nat := [2, 2, 1, 1, 1, 2, 1, 7, 2, 3]
def baseStart_164396 : Nat := 118140960795 + 164396 * 2 ^ 59
def prefixEnd_164396 : Nat := 4983230072969 + 3 ^ 40 * 164396 * 2
def baseEnd_164396 : Nat := 56276110451096022395975

theorem tailTrace_164396 : CollatzResearch.WordTrace tailWord_164396 prefixEnd_164396 56276110451096022395975 := by
  unfold tailWord_164396
  simp only [CollatzResearch.WordTrace]
  refine ⟨2998007356214421723308521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3997343141619228964411361 2998007356214421723308521)
  ·
    refine ⟨2248505517160816292481391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2998007356214421723308521 2248505517160816292481391)
    ·
      refine ⟨3372758275741224438722087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2248505517160816292481391 3372758275741224438722087)
      ·
        refine ⟨5059137413611836658083131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3372758275741224438722087 5059137413611836658083131)
        ·
          refine ⟨7588706120417754987124697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5059137413611836658083131 7588706120417754987124697)
          ·
            refine ⟨5691529590313316240343523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7588706120417754987124697 5691529590313316240343523)
            ·
              refine ⟨8537294385469974360515285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5691529590313316240343523 8537294385469974360515285)
              ·
                refine ⟨200092837159452524074577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8537294385469974360515285 200092837159452524074577)
                ·
                  refine ⟨150069627869589393055933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200092837159452524074577 150069627869589393055933)
                  ·
                    refine ⟨56276110451096022395975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 150069627869589393055933 56276110451096022395975)
                    ·
                      rfl

theorem cell22_164396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_164396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164396 prefixEnd_164396 := by exact prefixLift 164396
  have htrace : WordTrace (prefixWord ++ tailWord_164396) baseStart_164396 baseEnd_164396 := by
    simpa [prefixWord, tailWord_164396, baseEnd_164396] using wordTrace_append hprefix tailTrace_164396
  have hstable : (prefixWord ++ tailWord_164396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164396).length < 2 ^ (prefixWord ++ tailWord_164396).sum := by decide
  have hdescent : baseEnd_164396 < baseStart_164396 := by decide
  rcases family_descends (prefixWord ++ tailWord_164396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164409 : List Nat := [1, 2, 1, 5, 1, 1, 3, 8]
def baseStart_164409 : Nat := 118140960795 + 164409 * 2 ^ 59
def prefixEnd_164409 : Nat := 4983230072969 + 3 ^ 40 * 164409 * 2
def baseEnd_164409 : Nat := 6253395624085369091215

theorem tailTrace_164409 : CollatzResearch.WordTrace tailWord_164409 prefixEnd_164409 6253395624085369091215 := by
  unfold tailWord_164409
  simp only [CollatzResearch.WordTrace]
  refine ⟨5996488861381746666840281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3997659240921164444560187 5996488861381746666840281)
  ·
    refine ⟨4497366646036310000130211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5996488861381746666840281 4497366646036310000130211)
    ·
      refine ⟨6746049969054465000195317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4497366646036310000130211 6746049969054465000195317)
      ·
        refine ⟨632442184598856093768311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6746049969054465000195317 632442184598856093768311)
        ·
          refine ⟨948663276898284140652467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632442184598856093768311 948663276898284140652467)
          ·
            refine ⟨1422994915347426210978701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948663276898284140652467 1422994915347426210978701)
            ·
              refine ⟨533623093255284829117013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1422994915347426210978701 533623093255284829117013)
              ·
                refine ⟨6253395624085369091215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 533623093255284829117013 6253395624085369091215)
                ·
                  rfl

theorem cell22_164409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 8].length) (baseStart_164409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164409 prefixEnd_164409 := by exact prefixLift 164409
  have htrace : WordTrace (prefixWord ++ tailWord_164409) baseStart_164409 baseEnd_164409 := by
    simpa [prefixWord, tailWord_164409, baseEnd_164409] using wordTrace_append hprefix tailTrace_164409
  have hstable : (prefixWord ++ tailWord_164409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164409).length < 2 ^ (prefixWord ++ tailWord_164409).sum := by decide
  have hdescent : baseEnd_164409 < baseStart_164409 := by decide
  rcases family_descends (prefixWord ++ tailWord_164409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164439 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 2, 6]
def baseStart_164439 : Nat := 118140960795 + 164439 * 2 ^ 59
def prefixEnd_164439 : Nat := 4983230072969 + 3 ^ 40 * 164439 * 2
def baseEnd_164439 : Nat := 56290830229858243570843

theorem tailTrace_164439 : CollatzResearch.WordTrace tailWord_164439 prefixEnd_164439 56290830229858243570843 := by
  unfold tailWord_164439
  simp only [CollatzResearch.WordTrace]
  refine ⟨5997583051273061790432371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3998388700848707860288247 5997583051273061790432371)
  ·
    refine ⟨8996374576909592685648557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5997583051273061790432371 8996374576909592685648557)
    ·
      refine ⟨3373640466341097257118209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8996374576909592685648557 3373640466341097257118209)
      ·
        refine ⟨2530230349755822942838657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3373640466341097257118209 2530230349755822942838657)
        ·
          refine ⟨1897672762316867207128993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2530230349755822942838657 1897672762316867207128993)
          ·
            refine ⟨1423254571737650405346745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1897672762316867207128993 1423254571737650405346745)
            ·
              refine ⟨1067440928803237804010059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1423254571737650405346745 1067440928803237804010059)
              ·
                refine ⟨1601161393204856706015089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067440928803237804010059 1601161393204856706015089)
                ·
                  refine ⟨1200871044903642529511317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1601161393204856706015089 1200871044903642529511317)
                  ·
                    refine ⟨56290830229858243570843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1200871044903642529511317 56290830229858243570843)
                    ·
                      rfl

theorem cell22_164439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_164439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164439 prefixEnd_164439 := by exact prefixLift 164439
  have htrace : WordTrace (prefixWord ++ tailWord_164439) baseStart_164439 baseEnd_164439 := by
    simpa [prefixWord, tailWord_164439, baseEnd_164439] using wordTrace_append hprefix tailTrace_164439
  have hstable : (prefixWord ++ tailWord_164439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164439).length < 2 ^ (prefixWord ++ tailWord_164439).sum := by decide
  have hdescent : baseEnd_164439 < baseStart_164439 := by decide
  rcases family_descends (prefixWord ++ tailWord_164439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164516 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 6]
def baseStart_164516 : Nat := 118140960795 + 164516 * 2 ^ 59
def prefixEnd_164516 : Nat := 4983230072969 + 3 ^ 40 * 164516 * 2
def baseEnd_164516 : Nat := 18772396301151903131869

theorem tailTrace_164516 : CollatzResearch.WordTrace tailWord_164516 prefixEnd_164516 18772396301151903131869 := by
  unfold tailWord_164516
  simp only [CollatzResearch.WordTrace]
  refine ⟨3000195735997051970492701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4000260981329402627323601 3000195735997051970492701)
  ·
    refine ⟨1125073400998894488934763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3000195735997051970492701 1125073400998894488934763)
    ·
      refine ⟨1687610101498341733402145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1125073400998894488934763 1687610101498341733402145)
      ·
        refine ⟨1265707576123756300051609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1687610101498341733402145 1265707576123756300051609)
        ·
          refine ⟨949280682092817225038707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1265707576123756300051609 949280682092817225038707)
          ·
            refine ⟨1423921023139225837558061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949280682092817225038707 1423921023139225837558061)
            ·
              refine ⟨533970383677209689084273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1423921023139225837558061 533970383677209689084273)
              ·
                refine ⟨400477787757907266813205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 533970383677209689084273 400477787757907266813205)
                ·
                  refine ⟨18772396301151903131869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 400477787757907266813205 18772396301151903131869)
                  ·
                    rfl

theorem cell22_164516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_164516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164516 prefixEnd_164516 := by exact prefixLift 164516
  have htrace : WordTrace (prefixWord ++ tailWord_164516) baseStart_164516 baseEnd_164516 := by
    simpa [prefixWord, tailWord_164516, baseEnd_164516] using wordTrace_append hprefix tailTrace_164516
  have hstable : (prefixWord ++ tailWord_164516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164516).length < 2 ^ (prefixWord ++ tailWord_164516).sum := by decide
  have hdescent : baseEnd_164516 < baseStart_164516 := by decide
  rcases family_descends (prefixWord ++ tailWord_164516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164531 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 1, 5]
def baseStart_164531 : Nat := 118140960795 + 164531 * 2 ^ 59
def prefixEnd_164531 : Nat := 4983230072969 + 3 ^ 40 * 164531 * 2
def baseEnd_164531 : Nat := 56322323710000670270561

theorem tailTrace_164531 : CollatzResearch.WordTrace tailWord_164531 prefixEnd_164531 56322323710000670270561 := by
  unfold tailWord_164531
  simp only [CollatzResearch.WordTrace]
  refine ⟨6000938566939761502781447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4000625711293174335187631 6000938566939761502781447)
  ·
    refine ⟨9001407850409642254172171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6000938566939761502781447 9001407850409642254172171)
    ·
      refine ⟨13502111775614463381258257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9001407850409642254172171 13502111775614463381258257)
      ·
        refine ⟨10126583831710847535943693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13502111775614463381258257 10126583831710847535943693)
        ·
          refine ⟨3797468936891567825978885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10126583831710847535943693 3797468936891567825978885)
          ·
            refine ⟨712025425667168967371041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3797468936891567825978885 712025425667168967371041)
            ·
              refine ⟨534019069250376725528281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712025425667168967371041 534019069250376725528281)
              ·
                refine ⟨400514301937782544146211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534019069250376725528281 400514301937782544146211)
                ·
                  refine ⟨600771452906673816219317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400514301937782544146211 600771452906673816219317)
                  ·
                    refine ⟨56322323710000670270561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 600771452906673816219317 56322323710000670270561)
                    ·
                      rfl

theorem cell22_164531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 5].length) (baseStart_164531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164531 prefixEnd_164531 := by exact prefixLift 164531
  have htrace : WordTrace (prefixWord ++ tailWord_164531) baseStart_164531 baseEnd_164531 := by
    simpa [prefixWord, tailWord_164531, baseEnd_164531] using wordTrace_append hprefix tailTrace_164531
  have hstable : (prefixWord ++ tailWord_164531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164531).length < 2 ^ (prefixWord ++ tailWord_164531).sum := by decide
  have hdescent : baseEnd_164531 < baseStart_164531 := by decide
  rcases family_descends (prefixWord ++ tailWord_164531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164696 : List Nat := [2, 1, 2, 2, 1, 1, 1, 12]
def baseStart_164696 : Nat := 118140960795 + 164696 * 2 ^ 59
def prefixEnd_164696 : Nat := 4983230072969 + 3 ^ 40 * 164696 * 2
def baseEnd_164696 : Nat := 6264311842443915543895

theorem tailTrace_164696 : CollatzResearch.WordTrace tailWord_164696 prefixEnd_164696 6264311842443915543895 := by
  unfold tailWord_164696
  simp only [CollatzResearch.WordTrace]
  refine ⟨3003478305670997341268971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4004637740894663121691961 3003478305670997341268971)
  ·
    refine ⟨4505217458506496011903457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3003478305670997341268971 4505217458506496011903457)
    ·
      refine ⟨3378913093879872008927593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4505217458506496011903457 3378913093879872008927593)
      ·
        refine ⟨2534184820409904006695695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3378913093879872008927593 2534184820409904006695695)
        ·
          refine ⟨3801277230614856010043543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2534184820409904006695695 3801277230614856010043543)
          ·
            refine ⟨5701915845922284015065315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3801277230614856010043543 5701915845922284015065315)
            ·
              refine ⟨8552873768883426022597973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5701915845922284015065315 8552873768883426022597973)
              ·
                refine ⟨6264311842443915543895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 8552873768883426022597973 6264311842443915543895)
                ·
                  rfl

theorem cell22_164696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 12].length) (baseStart_164696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164696 prefixEnd_164696 := by exact prefixLift 164696
  have htrace : WordTrace (prefixWord ++ tailWord_164696) baseStart_164696 baseEnd_164696 := by
    simpa [prefixWord, tailWord_164696, baseEnd_164696] using wordTrace_append hprefix tailTrace_164696
  have hstable : (prefixWord ++ tailWord_164696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164696).length < 2 ^ (prefixWord ++ tailWord_164696).sum := by decide
  have hdescent : baseEnd_164696 < baseStart_164696 := by decide
  rcases family_descends (prefixWord ++ tailWord_164696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164698 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 1, 6]
def baseStart_164698 : Nat := 118140960795 + 164698 * 2 ^ 59
def prefixEnd_164698 : Nat := 4983230072969 + 3 ^ 40 * 164698 * 2
def baseEnd_164698 : Nat := 56379491222867901345049

theorem tailTrace_164698 : CollatzResearch.WordTrace tailWord_164698 prefixEnd_164698 56379491222867901345049 := by
  unfold tailWord_164698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1501757389333687256027687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4004686371556499349407165 1501757389333687256027687)
  ·
    refine ⟨2252636084000530884041531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1501757389333687256027687 2252636084000530884041531)
    ·
      refine ⟨3378954126000796326062297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2252636084000530884041531 3378954126000796326062297)
      ·
        refine ⟨2534215594500597244546723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3378954126000796326062297 2534215594500597244546723)
        ·
          refine ⟨3801323391750895866820085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2534215594500597244546723 3801323391750895866820085)
          ·
            refine ⟨356374067976646487514383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3801323391750895866820085 356374067976646487514383)
            ·
              refine ⟨534561101964969731271575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356374067976646487514383 534561101964969731271575)
              ·
                refine ⟨801841652947454596907363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534561101964969731271575 801841652947454596907363)
                ·
                  refine ⟨1202762479421181895361045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801841652947454596907363 1202762479421181895361045)
                  ·
                    refine ⟨56379491222867901345049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1202762479421181895361045 56379491222867901345049)
                    ·
                      rfl

theorem cell22_164698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_164698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164698 prefixEnd_164698 := by exact prefixLift 164698
  have htrace : WordTrace (prefixWord ++ tailWord_164698) baseStart_164698 baseEnd_164698 := by
    simpa [prefixWord, tailWord_164698, baseEnd_164698] using wordTrace_append hprefix tailTrace_164698
  have hstable : (prefixWord ++ tailWord_164698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164698).length < 2 ^ (prefixWord ++ tailWord_164698).sum := by decide
  have hdescent : baseEnd_164698 < baseStart_164698 := by decide
  rcases family_descends (prefixWord ++ tailWord_164698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164700 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 1, 5]
def baseStart_164700 : Nat := 118140960795 + 164700 * 2 ^ 59
def prefixEnd_164700 : Nat := 4983230072969 + 3 ^ 40 * 164700 * 2
def baseEnd_164700 : Nat := 56380175863740562795043

theorem tailTrace_164700 : CollatzResearch.WordTrace tailWord_164700 prefixEnd_164700 56380175863740562795043 := by
  unfold tailWord_164700
  simp only [CollatzResearch.WordTrace]
  refine ⟨3003551251663751682841777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4004735002218335577122369 3003551251663751682841777)
  ·
    refine ⟨2252663438747813762131333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3003551251663751682841777 2252663438747813762131333)
    ·
      refine ⟨422374394765215080399625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2252663438747813762131333 422374394765215080399625)
      ·
        refine ⟨316780796073911310299719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422374394765215080399625 316780796073911310299719)
        ·
          refine ⟨475171194110866965449579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316780796073911310299719 475171194110866965449579)
          ·
            refine ⟨712756791166300448174369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475171194110866965449579 712756791166300448174369)
            ·
              refine ⟨534567593374725336130777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712756791166300448174369 534567593374725336130777)
              ·
                refine ⟨400925695031044002098083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534567593374725336130777 400925695031044002098083)
                ·
                  refine ⟨601388542546566003147125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400925695031044002098083 601388542546566003147125)
                  ·
                    refine ⟨56380175863740562795043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 601388542546566003147125 56380175863740562795043)
                    ·
                      rfl

theorem cell22_164700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_164700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164700 prefixEnd_164700 := by exact prefixLift 164700
  have htrace : WordTrace (prefixWord ++ tailWord_164700) baseStart_164700 baseEnd_164700 := by
    simpa [prefixWord, tailWord_164700, baseEnd_164700] using wordTrace_append hprefix tailTrace_164700
  have hstable : (prefixWord ++ tailWord_164700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164700).length < 2 ^ (prefixWord ++ tailWord_164700).sum := by decide
  have hdescent : baseEnd_164700 < baseStart_164700 := by decide
  rcases family_descends (prefixWord ++ tailWord_164700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164734 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_164734 : Nat := 118140960795 + 164734 * 2 ^ 59
def prefixEnd_164734 : Nat := 4983230072969 + 3 ^ 40 * 164734 * 2
def baseEnd_164734 : Nat := 56391814758575807444939

theorem tailTrace_164734 : CollatzResearch.WordTrace tailWord_164734 prefixEnd_164734 56391814758575807444939 := by
  unfold tailWord_164734
  simp only [CollatzResearch.WordTrace]
  refine ⟨751042823150540896552657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4005561723469551448280837 751042823150540896552657)
  ·
    refine ⟨563282117362905672414493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 751042823150540896552657 563282117362905672414493)
    ·
      refine ⟨211230794011089627155435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 563282117362905672414493 211230794011089627155435)
      ·
        refine ⟨316846191016634440733153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211230794011089627155435 316846191016634440733153)
        ·
          refine ⟨237634643262475830549865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316846191016634440733153 237634643262475830549865)
          ·
            refine ⟨178225982446856872912399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237634643262475830549865 178225982446856872912399)
            ·
              refine ⟨267338973670285309368599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178225982446856872912399 267338973670285309368599)
              ·
                refine ⟨401008460505427964052899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267338973670285309368599 401008460505427964052899)
                ·
                  refine ⟨601512690758141946079349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 401008460505427964052899 601512690758141946079349)
                  ·
                    refine ⟨56391814758575807444939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 601512690758141946079349 56391814758575807444939)
                    ·
                      rfl

theorem cell22_164734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_164734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164734 prefixEnd_164734 := by exact prefixLift 164734
  have htrace : WordTrace (prefixWord ++ tailWord_164734) baseStart_164734 baseEnd_164734 := by
    simpa [prefixWord, tailWord_164734, baseEnd_164734] using wordTrace_append hprefix tailTrace_164734
  have hstable : (prefixWord ++ tailWord_164734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164734).length < 2 ^ (prefixWord ++ tailWord_164734).sum := by decide
  have hdescent : baseEnd_164734 < baseStart_164734 := by decide
  rcases family_descends (prefixWord ++ tailWord_164734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164745 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 3, 3]
def baseStart_164745 : Nat := 118140960795 + 164745 * 2 ^ 59
def prefixEnd_164745 : Nat := 4983230072969 + 3 ^ 40 * 164745 * 2
def baseEnd_164745 : Nat := 56395580283375445419905

theorem tailTrace_164745 : CollatzResearch.WordTrace tailWord_164745 prefixEnd_164745 56395580283375445419905 := by
  unfold tailWord_164745
  simp only [CollatzResearch.WordTrace]
  refine ⟨6008743788164476051071689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4005829192109650700714459 6008743788164476051071689)
  ·
    refine ⟨4506557841123357038303767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6008743788164476051071689 4506557841123357038303767)
    ·
      refine ⟨6759836761685035557455651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4506557841123357038303767 6759836761685035557455651)
      ·
        refine ⟨10139755142527553336183477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6759836761685035557455651 10139755142527553336183477)
        ·
          refine ⟨950602044611958125267201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10139755142527553336183477 950602044611958125267201)
          ·
            refine ⟨712951533458968593950401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 950602044611958125267201 712951533458968593950401)
            ·
              refine ⟨534713650094226445462801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712951533458968593950401 534713650094226445462801)
              ·
                refine ⟨401035237570669834097101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534713650094226445462801 401035237570669834097101)
                ·
                  refine ⟨150388214089001187786413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 401035237570669834097101 150388214089001187786413)
                  ·
                    refine ⟨56395580283375445419905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 150388214089001187786413 56395580283375445419905)
                    ·
                      rfl

theorem cell22_164745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 3].length) (baseStart_164745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164745 prefixEnd_164745 := by exact prefixLift 164745
  have htrace : WordTrace (prefixWord ++ tailWord_164745) baseStart_164745 baseEnd_164745 := by
    simpa [prefixWord, tailWord_164745, baseEnd_164745] using wordTrace_append hprefix tailTrace_164745
  have hstable : (prefixWord ++ tailWord_164745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164745).length < 2 ^ (prefixWord ++ tailWord_164745).sum := by decide
  have hdescent : baseEnd_164745 < baseStart_164745 := by decide
  rcases family_descends (prefixWord ++ tailWord_164745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164792 : List Nat := [2, 1, 2, 1, 2, 6, 2, 1, 5]
def baseStart_164792 : Nat := 118140960795 + 164792 * 2 ^ 59
def prefixEnd_164792 : Nat := 4983230072969 + 3 ^ 40 * 164792 * 2
def baseEnd_164792 : Nat := 18803889781294329831587

theorem tailTrace_164792 : CollatzResearch.WordTrace tailWord_164792 prefixEnd_164792 18803889781294329831587 := by
  unfold tailWord_164792
  simp only [CollatzResearch.WordTrace]
  refine ⟨3005229009497101539016315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4006972012662802052021753 3005229009497101539016315)
  ·
    refine ⟨4507843514245652308524473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3005229009497101539016315 4507843514245652308524473)
    ·
      refine ⟨3380882635684239231393355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4507843514245652308524473 3380882635684239231393355)
      ·
        refine ⟨5071323953526358847090033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3380882635684239231393355 5071323953526358847090033)
        ·
          refine ⟨3803492965144769135317525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5071323953526358847090033 3803492965144769135317525)
          ·
            refine ⟨178288732741161053218009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3803492965144769135317525 178288732741161053218009)
            ·
              refine ⟨133716549555870789913507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178288732741161053218009 133716549555870789913507)
              ·
                refine ⟨200574824333806184870261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133716549555870789913507 200574824333806184870261)
                ·
                  refine ⟨18803889781294329831587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 200574824333806184870261 18803889781294329831587)
                  ·
                    rfl

theorem cell22_164792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 5].length) (baseStart_164792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164792 prefixEnd_164792 := by exact prefixLift 164792
  have htrace : WordTrace (prefixWord ++ tailWord_164792) baseStart_164792 baseEnd_164792 := by
    simpa [prefixWord, tailWord_164792, baseEnd_164792] using wordTrace_append hprefix tailTrace_164792
  have hstable : (prefixWord ++ tailWord_164792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164792).length < 2 ^ (prefixWord ++ tailWord_164792).sum := by decide
  have hdescent : baseEnd_164792 < baseStart_164792 := by decide
  rcases family_descends (prefixWord ++ tailWord_164792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164833 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 3, 6]
def baseStart_164833 : Nat := 118140960795 + 164833 * 2 ^ 59
def prefixEnd_164833 : Nat := 4983230072969 + 3 ^ 40 * 164833 * 2
def baseEnd_164833 : Nat := 56425704481772549219635

theorem tailTrace_164833 : CollatzResearch.WordTrace tailWord_164833 prefixEnd_164833 56425704481772549219635 := by
  unfold tailWord_164833
  simp only [CollatzResearch.WordTrace]
  refine ⟨6011953411845667080275153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4007968941230444720183435 6011953411845667080275153)
  ·
    refine ⟨4508965058884250310206365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6011953411845667080275153 4508965058884250310206365)
    ·
      refine ⟨1690861897081593866327387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4508965058884250310206365 1690861897081593866327387)
      ·
        refine ⟨2536292845622390799491081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1690861897081593866327387 2536292845622390799491081)
        ·
          refine ⟨1902219634216793099618311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2536292845622390799491081 1902219634216793099618311)
          ·
            refine ⟨2853329451325189649427467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902219634216793099618311 2853329451325189649427467)
            ·
              refine ⟨4279994176987784474141201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2853329451325189649427467 4279994176987784474141201)
              ·
                refine ⟨3209995632740838355605901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4279994176987784474141201 3209995632740838355605901)
                ·
                  refine ⟨1203748362277814383352213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3209995632740838355605901 1203748362277814383352213)
                  ·
                    refine ⟨56425704481772549219635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1203748362277814383352213 56425704481772549219635)
                    ·
                      rfl

theorem cell22_164833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_164833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164833 prefixEnd_164833 := by exact prefixLift 164833
  have htrace : WordTrace (prefixWord ++ tailWord_164833) baseStart_164833 baseEnd_164833 := by
    simpa [prefixWord, tailWord_164833, baseEnd_164833] using wordTrace_append hprefix tailTrace_164833
  have hstable : (prefixWord ++ tailWord_164833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164833).length < 2 ^ (prefixWord ++ tailWord_164833).sum := by decide
  have hdescent : baseEnd_164833 < baseStart_164833 := by decide
  rcases family_descends (prefixWord ++ tailWord_164833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164897 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 3, 3]
def baseStart_164897 : Nat := 118140960795 + 164897 * 2 ^ 59
def prefixEnd_164897 : Nat := 4983230072969 + 3 ^ 40 * 164897 * 2
def baseEnd_164897 : Nat := 56447612989697715619439

theorem tailTrace_164897 : CollatzResearch.WordTrace tailWord_164897 prefixEnd_164897 56447612989697715619439 := by
  unfold tailWord_164897
  simp only [CollatzResearch.WordTrace]
  refine ⟨6014287683613806010604945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4009525122409204007069963 6014287683613806010604945)
  ·
    refine ⟨4510715762710354507953709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6014287683613806010604945 4510715762710354507953709)
    ·
      refine ⟨1691518411016382940482641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4510715762710354507953709 1691518411016382940482641)
      ·
        refine ⟨1268638808262287205361981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1691518411016382940482641 1268638808262287205361981)
        ·
          refine ⟨475739553098357702010743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1268638808262287205361981 475739553098357702010743)
          ·
            refine ⟨713609329647536553016115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475739553098357702010743 713609329647536553016115)
            ·
              refine ⟨1070413994471304829524173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713609329647536553016115 1070413994471304829524173)
              ·
                refine ⟨401405247926739311071565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1070413994471304829524173 401405247926739311071565)
                ·
                  refine ⟨150526967972527241651837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 401405247926739311071565 150526967972527241651837)
                  ·
                    refine ⟨56447612989697715619439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 150526967972527241651837 56447612989697715619439)
                    ·
                      rfl

theorem cell22_164897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_164897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164897 prefixEnd_164897 := by exact prefixLift 164897
  have htrace : WordTrace (prefixWord ++ tailWord_164897) baseStart_164897 baseEnd_164897 := by
    simpa [prefixWord, tailWord_164897, baseEnd_164897] using wordTrace_append hprefix tailTrace_164897
  have hstable : (prefixWord ++ tailWord_164897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164897).length < 2 ^ (prefixWord ++ tailWord_164897).sum := by decide
  have hdescent : baseEnd_164897 < baseStart_164897 := by decide
  rcases family_descends (prefixWord ++ tailWord_164897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164940 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 5, 4]
def baseStart_164940 : Nat := 118140960795 + 164940 * 2 ^ 59
def prefixEnd_164940 : Nat := 4983230072969 + 3 ^ 40 * 164940 * 2
def baseEnd_164940 : Nat := 56462332768459936794307

theorem tailTrace_164940 : CollatzResearch.WordTrace tailWord_164940 prefixEnd_164940 56462332768459936794307 := by
  unfold tailWord_164940
  simp only [CollatzResearch.WordTrace]
  refine ⟨3007928011229012177210137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4010570681638682902946849 3007928011229012177210137)
  ·
    refine ⟨2255946008421759132907603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3007928011229012177210137 2255946008421759132907603)
    ·
      refine ⟨3383919012632638699361405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2255946008421759132907603 3383919012632638699361405)
      ·
        refine ⟨1268969629737239512260527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3383919012632638699361405 1268969629737239512260527)
        ·
          refine ⟨1903454444605859268390791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268969629737239512260527 1903454444605859268390791)
          ·
            refine ⟨2855181666908788902586187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1903454444605859268390791 2855181666908788902586187)
            ·
              refine ⟨4282772500363183353879281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2855181666908788902586187 4282772500363183353879281)
              ·
                refine ⟨3212079375272387515409461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4282772500363183353879281 3212079375272387515409461)
                ·
                  refine ⟨301132441431786329569637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3212079375272387515409461 301132441431786329569637)
                  ·
                    refine ⟨56462332768459936794307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 301132441431786329569637 56462332768459936794307)
                    ·
                      rfl

theorem cell22_164940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_164940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164940 prefixEnd_164940 := by exact prefixLift 164940
  have htrace : WordTrace (prefixWord ++ tailWord_164940) baseStart_164940 baseEnd_164940 := by
    simpa [prefixWord, tailWord_164940, baseEnd_164940] using wordTrace_append hprefix tailTrace_164940
  have hstable : (prefixWord ++ tailWord_164940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164940).length < 2 ^ (prefixWord ++ tailWord_164940).sum := by decide
  have hdescent : baseEnd_164940 < baseStart_164940 := by decide
  rcases family_descends (prefixWord ++ tailWord_164940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164974 : List Nat := [4, 1, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_164974 : Nat := 118140960795 + 164974 * 2 ^ 59
def prefixEnd_164974 : Nat := 4983230072969 + 3 ^ 40 * 164974 * 2
def baseEnd_164974 : Nat := 56473971663295181444203

theorem tailTrace_164974 : CollatzResearch.WordTrace tailWord_164974 prefixEnd_164974 56473971663295181444203 := by
  unfold tailWord_164974
  simp only [CollatzResearch.WordTrace]
  refine ⟨752137013041856020144747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4011397402889898774105317 752137013041856020144747)
  ·
    refine ⟨1128205519562784030217121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 752137013041856020144747 1128205519562784030217121)
    ·
      refine ⟨846154139672088022662841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1128205519562784030217121 846154139672088022662841)
      ·
        refine ⟨634615604754066016997131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 846154139672088022662841 634615604754066016997131)
        ·
          refine ⟨951923407131099025495697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634615604754066016997131 951923407131099025495697)
          ·
            refine ⟨713942555348324269121773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 951923407131099025495697 713942555348324269121773)
            ·
              refine ⟨267728458255621600920665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 713942555348324269121773 267728458255621600920665)
              ·
                refine ⟨200796343691716200690499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267728458255621600920665 200796343691716200690499)
                ·
                  refine ⟨301194515537574301035749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200796343691716200690499 301194515537574301035749)
                  ·
                    refine ⟨56473971663295181444203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 301194515537574301035749 56473971663295181444203)
                    ·
                      rfl

theorem cell22_164974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_164974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_164974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_164974 prefixEnd_164974 := by exact prefixLift 164974
  have htrace : WordTrace (prefixWord ++ tailWord_164974) baseStart_164974 baseEnd_164974 := by
    simpa [prefixWord, tailWord_164974, baseEnd_164974] using wordTrace_append hprefix tailTrace_164974
  have hstable : (prefixWord ++ tailWord_164974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164974).length < 2 ^ (prefixWord ++ tailWord_164974).sum := by decide
  have hdescent : baseEnd_164974 < baseStart_164974 := by decide
  rcases family_descends (prefixWord ++ tailWord_164974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165000 : List Nat := [2, 1, 3, 4, 12]
def baseStart_165000 : Nat := 118140960795 + 165000 * 2 ^ 59
def prefixEnd_165000 : Nat := 4983230072969 + 3 ^ 40 * 165000 * 2
def baseEnd_165000 : Nat := 232439802447077285161

theorem tailTrace_165000 : CollatzResearch.WordTrace tailWord_165000 prefixEnd_165000 232439802447077285161 := by
  unfold tailWord_165000
  simp only [CollatzResearch.WordTrace]
  refine ⟨3009022201120327300802227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4012029601493769734402969 3009022201120327300802227)
  ·
    refine ⟨4513533301680490951203341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3009022201120327300802227 4513533301680490951203341)
    ·
      refine ⟨1692574988130184106701253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4513533301680490951203341 1692574988130184106701253)
      ·
        refine ⟨317357810274409520006485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1692574988130184106701253 317357810274409520006485)
        ·
          refine ⟨232439802447077285161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 317357810274409520006485 232439802447077285161)
          ·
            rfl

theorem cell22_165000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 12].length) (baseStart_165000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165000 prefixEnd_165000 := by exact prefixLift 165000
  have htrace : WordTrace (prefixWord ++ tailWord_165000) baseStart_165000 baseEnd_165000 := by
    simpa [prefixWord, tailWord_165000, baseEnd_165000] using wordTrace_append hprefix tailTrace_165000
  have hstable : (prefixWord ++ tailWord_165000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165000).length < 2 ^ (prefixWord ++ tailWord_165000).sum := by decide
  have hdescent : baseEnd_165000 < baseStart_165000 := by decide
  rcases family_descends (prefixWord ++ tailWord_165000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165002 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 2, 4]
def baseStart_165002 : Nat := 118140960795 + 165002 * 2 ^ 59
def prefixEnd_165002 : Nat := 4983230072969 + 3 ^ 40 * 165002 * 2
def baseEnd_165002 : Nat := 56483556635512441744117

theorem tailTrace_165002 : CollatzResearch.WordTrace tailWord_165002 prefixEnd_165002 56483556635512441744117 := by
  unfold tailWord_165002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1504529337058352235794315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4012078232155605962118173 1504529337058352235794315)
  ·
    refine ⟨2256794005587528353691473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1504529337058352235794315 2256794005587528353691473)
    ·
      refine ⟨1692595504190646265268605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2256794005587528353691473 1692595504190646265268605)
      ·
        refine ⟨634723314071492349475727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1692595504190646265268605 634723314071492349475727)
        ·
          refine ⟨952084971107238524213591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634723314071492349475727 952084971107238524213591)
          ·
            refine ⟨1428127456660857786320387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952084971107238524213591 1428127456660857786320387)
            ·
              refine ⟨2142191184991286679480581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1428127456660857786320387 2142191184991286679480581)
              ·
                refine ⟨401660847185866252402609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2142191184991286679480581 401660847185866252402609)
                ·
                  refine ⟨301245635389399689301957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401660847185866252402609 301245635389399689301957)
                  ·
                    refine ⟨56483556635512441744117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 301245635389399689301957 56483556635512441744117)
                    ·
                      rfl

theorem cell22_165002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_165002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165002 prefixEnd_165002 := by exact prefixLift 165002
  have htrace : WordTrace (prefixWord ++ tailWord_165002) baseStart_165002 baseEnd_165002 := by
    simpa [prefixWord, tailWord_165002, baseEnd_165002] using wordTrace_append hprefix tailTrace_165002
  have hstable : (prefixWord ++ tailWord_165002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165002).length < 2 ^ (prefixWord ++ tailWord_165002).sum := by decide
  have hdescent : baseEnd_165002 < baseStart_165002 := by decide
  rcases family_descends (prefixWord ++ tailWord_165002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165006 : List Nat := [4, 1, 1, 3, 2, 1, 4, 2, 4]
def baseStart_165006 : Nat := 118140960795 + 165006 * 2 ^ 59
def prefixEnd_165006 : Nat := 4983230072969 + 3 ^ 40 * 165006 * 2
def baseEnd_165006 : Nat := 18828308639085921548035

theorem tailTrace_165006 : CollatzResearch.WordTrace tailWord_165006 prefixEnd_165006 18828308639085921548035 := by
  unfold tailWord_165006
  simp only [CollatzResearch.WordTrace]
  refine ⟨752282905027364703290359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4012175493479278417548581 752282905027364703290359)
  ·
    refine ⟨1128424357541047054935539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 752282905027364703290359 1128424357541047054935539)
    ·
      refine ⟨1692636536311570582403309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1128424357541047054935539 1692636536311570582403309)
      ·
        refine ⟨634738701116838968401241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1692636536311570582403309 634738701116838968401241)
        ·
          refine ⟨476054025837629226300931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 634738701116838968401241 476054025837629226300931)
          ·
            refine ⟨714081038756443839451397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476054025837629226300931 714081038756443839451397)
            ·
              refine ⟨133890194766833219897137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 714081038756443839451397 133890194766833219897137)
              ·
                refine ⟨100417646075124914922853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133890194766833219897137 100417646075124914922853)
                ·
                  refine ⟨18828308639085921548035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100417646075124914922853 18828308639085921548035)
                  ·
                    rfl

theorem cell22_165006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_165006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165006 prefixEnd_165006 := by exact prefixLift 165006
  have htrace : WordTrace (prefixWord ++ tailWord_165006) baseStart_165006 baseEnd_165006 := by
    simpa [prefixWord, tailWord_165006, baseEnd_165006] using wordTrace_append hprefix tailTrace_165006
  have hstable : (prefixWord ++ tailWord_165006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165006).length < 2 ^ (prefixWord ++ tailWord_165006).sum := by decide
  have hdescent : baseEnd_165006 < baseStart_165006 := by decide
  rcases family_descends (prefixWord ++ tailWord_165006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165066 : List Nat := [3, 1, 2, 1, 3, 2, 2, 4, 1, 3]
def baseStart_165066 : Nat := 118140960795 + 165066 * 2 ^ 59
def prefixEnd_165066 : Nat := 4983230072969 + 3 ^ 40 * 165066 * 2
def baseEnd_165066 : Nat := 56505465143437608143921

theorem tailTrace_165066 : CollatzResearch.WordTrace tailWord_165066 prefixEnd_165066 56505465143437608143921 := by
  unfold tailWord_165066
  simp only [CollatzResearch.WordTrace]
  refine ⟨1505112905000386968376763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4013634413334365249004701 1505112905000386968376763)
  ·
    refine ⟨2257669357500580452565145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1505112905000386968376763 2257669357500580452565145)
    ·
      refine ⟨1693252018125435339423859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2257669357500580452565145 1693252018125435339423859)
      ·
        refine ⟨2539878027188153009135789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1693252018125435339423859 2539878027188153009135789)
        ·
          refine ⟨952454260195557378425921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2539878027188153009135789 952454260195557378425921)
          ·
            refine ⟨714340695146668033819441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 952454260195557378425921 714340695146668033819441)
            ·
              refine ⟨535755521360001025364581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 714340695146668033819441 535755521360001025364581)
              ·
                refine ⟨100454160255000192255859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 535755521360001025364581 100454160255000192255859)
                ·
                  refine ⟨150681240382500288383789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100454160255000192255859 150681240382500288383789)
                  ·
                    refine ⟨56505465143437608143921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 150681240382500288383789 56505465143437608143921)
                    ·
                      rfl

theorem cell22_165066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_165066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165066 prefixEnd_165066 := by exact prefixLift 165066
  have htrace : WordTrace (prefixWord ++ tailWord_165066) baseStart_165066 baseEnd_165066 := by
    simpa [prefixWord, tailWord_165066, baseEnd_165066] using wordTrace_append hprefix tailTrace_165066
  have hstable : (prefixWord ++ tailWord_165066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165066).length < 2 ^ (prefixWord ++ tailWord_165066).sum := by decide
  have hdescent : baseEnd_165066 < baseStart_165066 := by decide
  rcases family_descends (prefixWord ++ tailWord_165066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165092 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_165092 : Nat := 118140960795 + 165092 * 2 ^ 59
def prefixEnd_165092 : Nat := 4983230072969 + 3 ^ 40 * 165092 * 2
def baseEnd_165092 : Nat := 56514365474782206993841

theorem tailTrace_165092 : CollatzResearch.WordTrace tailWord_165092 prefixEnd_165092 56514365474782206993841 := by
  unfold tailWord_165092
  simp only [CollatzResearch.WordTrace]
  refine ⟨3010699958953677156976765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4014266611938236209302353 3010699958953677156976765)
  ·
    refine ⟨1129012484607628933866287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3010699958953677156976765 1129012484607628933866287)
    ·
      refine ⟨1693518726911443400799431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1129012484607628933866287 1693518726911443400799431)
      ·
        refine ⟨2540278090367165101199147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1693518726911443400799431 2540278090367165101199147)
        ·
          refine ⟨3810417135550747651798721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2540278090367165101199147 3810417135550747651798721)
          ·
            refine ⟨2857812851663060738849041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3810417135550747651798721 2857812851663060738849041)
            ·
              refine ⟨2143359638747295554136781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2857812851663060738849041 2143359638747295554136781)
              ·
                refine ⟨803759864530235832801293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2143359638747295554136781 803759864530235832801293)
                ·
                  refine ⟨301409949198838437300485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803759864530235832801293 301409949198838437300485)
                  ·
                    refine ⟨56514365474782206993841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 301409949198838437300485 56514365474782206993841)
                    ·
                      rfl

theorem cell22_165092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_165092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165092 prefixEnd_165092 := by exact prefixLift 165092
  have htrace : WordTrace (prefixWord ++ tailWord_165092) baseStart_165092 baseEnd_165092 := by
    simpa [prefixWord, tailWord_165092, baseEnd_165092] using wordTrace_append hprefix tailTrace_165092
  have hstable : (prefixWord ++ tailWord_165092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165092).length < 2 ^ (prefixWord ++ tailWord_165092).sum := by decide
  have hdescent : baseEnd_165092 < baseStart_165092 := by decide
  rcases family_descends (prefixWord ++ tailWord_165092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165124 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 6]
def baseStart_165124 : Nat := 118140960795 + 165124 * 2 ^ 59
def prefixEnd_165124 : Nat := 4983230072969 + 3 ^ 40 * 165124 * 2
def baseEnd_165124 : Nat := 18841773242914930064581

theorem tailTrace_165124 : CollatzResearch.WordTrace tailWord_165124 prefixEnd_165124 18841773242914930064581 := by
  unfold tailWord_165124
  simp only [CollatzResearch.WordTrace]
  refine ⟨3011283526895711889559213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4015044702527615852745617 3011283526895711889559213)
  ·
    refine ⟨1129231322585891958584705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3011283526895711889559213 1129231322585891958584705)
    ·
      refine ⟨846923491939418968938529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1129231322585891958584705 846923491939418968938529)
      ·
        refine ⟨635192618954564226703897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 846923491939418968938529 635192618954564226703897)
        ·
          refine ⟨476394464215923170027923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 635192618954564226703897 476394464215923170027923)
          ·
            refine ⟨714591696323884755041885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476394464215923170027923 714591696323884755041885)
            ·
              refine ⟨267971886121456783140707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 714591696323884755041885 267971886121456783140707)
              ·
                refine ⟨401957829182185174711061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267971886121456783140707 401957829182185174711061)
                ·
                  refine ⟨18841773242914930064581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 401957829182185174711061 18841773242914930064581)
                  ·
                    rfl

theorem cell22_165124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_165124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165124 prefixEnd_165124 := by exact prefixLift 165124
  have htrace : WordTrace (prefixWord ++ tailWord_165124) baseStart_165124 baseEnd_165124 := by
    simpa [prefixWord, tailWord_165124, baseEnd_165124] using wordTrace_append hprefix tailTrace_165124
  have hstable : (prefixWord ++ tailWord_165124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165124).length < 2 ^ (prefixWord ++ tailWord_165124).sum := by decide
  have hdescent : baseEnd_165124 < baseStart_165124 := by decide
  rcases family_descends (prefixWord ++ tailWord_165124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165137 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 4, 4]
def baseStart_165137 : Nat := 118140960795 + 165137 * 2 ^ 59
def prefixEnd_165137 : Nat := 4983230072969 + 3 ^ 40 * 165137 * 2
def baseEnd_165137 : Nat := 56529769894417089618703

theorem tailTrace_165137 : CollatzResearch.WordTrace tailWord_165137 prefixEnd_165137 56529769894417089618703 := by
  unfold tailWord_165137
  simp only [CollatzResearch.WordTrace]
  refine ⟨6023041202744326999341665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4015360801829551332894443 6023041202744326999341665)
  ·
    refine ⟨4517280902058245249506249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6023041202744326999341665 4517280902058245249506249)
    ·
      refine ⟨3387960676543683937129687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4517280902058245249506249 3387960676543683937129687)
      ·
        refine ⟨5081941014815525905694531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3387960676543683937129687 5081941014815525905694531)
        ·
          refine ⟨7622911522223288858541797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5081941014815525905694531 7622911522223288858541797)
          ·
            refine ⟨1429295910416866660976587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7622911522223288858541797 1429295910416866660976587)
            ·
              refine ⟨2143943865625299991464881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1429295910416866660976587 2143943865625299991464881)
              ·
                refine ⟨1607957899218974993598661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2143943865625299991464881 1607957899218974993598661)
                ·
                  refine ⟨301492106103557811299749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1607957899218974993598661 301492106103557811299749)
                  ·
                    refine ⟨56529769894417089618703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 301492106103557811299749 56529769894417089618703)
                    ·
                      rfl

theorem cell22_165137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_165137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165137 prefixEnd_165137 := by exact prefixLift 165137
  have htrace : WordTrace (prefixWord ++ tailWord_165137) baseStart_165137 baseEnd_165137 := by
    simpa [prefixWord, tailWord_165137, baseEnd_165137] using wordTrace_append hprefix tailTrace_165137
  have hstable : (prefixWord ++ tailWord_165137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165137).length < 2 ^ (prefixWord ++ tailWord_165137).sum := by decide
  have hdescent : baseEnd_165137 < baseStart_165137 := by decide
  rcases family_descends (prefixWord ++ tailWord_165137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165184 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 3, 3]
def baseStart_165184 : Nat := 118140960795 + 165184 * 2 ^ 59
def prefixEnd_165184 : Nat := 4983230072969 + 3 ^ 40 * 165184 * 2
def baseEnd_165184 : Nat := 56545858954924633693559

theorem tailTrace_165184 : CollatzResearch.WordTrace tailWord_165184 prefixEnd_165184 56545858954924633693559 := by
  unfold tailWord_165184
  simp only [CollatzResearch.WordTrace]
  refine ⟨3012377716787027013151303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4016503622382702684201737 3012377716787027013151303)
  ·
    refine ⟨4518566575180540519726955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3012377716787027013151303 4518566575180540519726955)
    ·
      refine ⟨6777849862770810779590433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4518566575180540519726955 6777849862770810779590433)
      ·
        refine ⟨5083387397078108084692825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6777849862770810779590433 5083387397078108084692825)
        ·
          refine ⟨3812540547808581063519619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5083387397078108084692825 3812540547808581063519619)
          ·
            refine ⟨5718810821712871595279429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3812540547808581063519619 5718810821712871595279429)
            ·
              refine ⟨1072277029071163424114893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5718810821712871595279429 1072277029071163424114893)
              ·
                refine ⟨402103885901686284043085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1072277029071163424114893 402103885901686284043085)
                ·
                  refine ⟨150788957213132356516157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402103885901686284043085 150788957213132356516157)
                  ·
                    refine ⟨56545858954924633693559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 150788957213132356516157 56545858954924633693559)
                    ·
                      rfl

theorem cell22_165184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 3, 3].length) (baseStart_165184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165184 prefixEnd_165184 := by exact prefixLift 165184
  have htrace : WordTrace (prefixWord ++ tailWord_165184) baseStart_165184 baseEnd_165184 := by
    simpa [prefixWord, tailWord_165184, baseEnd_165184] using wordTrace_append hprefix tailTrace_165184
  have hstable : (prefixWord ++ tailWord_165184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165184).length < 2 ^ (prefixWord ++ tailWord_165184).sum := by decide
  have hdescent : baseEnd_165184 < baseStart_165184 := by decide
  rcases family_descends (prefixWord ++ tailWord_165184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165190 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_165190 : Nat := 118140960795 + 165190 * 2 ^ 59
def prefixEnd_165190 : Nat := 4983230072969 + 3 ^ 40 * 165190 * 2
def baseEnd_165190 : Nat := 56547912877542618043541

theorem tailTrace_165190 : CollatzResearch.WordTrace tailWord_165190 prefixEnd_165190 56547912877542618043541 := by
  unfold tailWord_165190
  simp only [CollatzResearch.WordTrace]
  refine ⟨188280445986009907844407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4016649514368211367347349 188280445986009907844407)
  ·
    refine ⟨282420668979014861766611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188280445986009907844407 282420668979014861766611)
    ·
      refine ⟨423631003468522292649917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282420668979014861766611 423631003468522292649917)
      ·
        refine ⟨158861626300695859743719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 423631003468522292649917 158861626300695859743719)
        ·
          refine ⟨238292439451043789615579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158861626300695859743719 238292439451043789615579)
          ·
            refine ⟨357438659176565684423369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238292439451043789615579 357438659176565684423369)
            ·
              refine ⟨268078994382424263317527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357438659176565684423369 268078994382424263317527)
              ·
                refine ⟨402118491573636394976291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268078994382424263317527 402118491573636394976291)
                ·
                  refine ⟨603177737360454592464437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402118491573636394976291 603177737360454592464437)
                  ·
                    refine ⟨56547912877542618043541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 603177737360454592464437 56547912877542618043541)
                    ·
                      rfl

theorem cell22_165190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_165190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165190 prefixEnd_165190 := by exact prefixLift 165190
  have htrace : WordTrace (prefixWord ++ tailWord_165190) baseStart_165190 baseEnd_165190 := by
    simpa [prefixWord, tailWord_165190, baseEnd_165190] using wordTrace_append hprefix tailTrace_165190
  have hstable : (prefixWord ++ tailWord_165190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165190).length < 2 ^ (prefixWord ++ tailWord_165190).sum := by decide
  have hdescent : baseEnd_165190 < baseStart_165190 := by decide
  rcases family_descends (prefixWord ++ tailWord_165190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165229 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_165229 : Nat := 118140960795 + 165229 * 2 ^ 59
def prefixEnd_165229 : Nat := 4983230072969 + 3 ^ 40 * 165229 * 2
def baseEnd_165229 : Nat := 56561263374559516318421

theorem tailTrace_165229 : CollatzResearch.WordTrace tailWord_165229 prefixEnd_165229 56561263374559516318421 := by
  unfold tailWord_165229
  simp only [CollatzResearch.WordTrace]
  refine ⟨6026396718411026711690741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4017597812274017807793827 6026396718411026711690741)
  ·
    refine ⟨564974692351033754221007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6026396718411026711690741 564974692351033754221007)
    ·
      refine ⟨847462038526550631331511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 564974692351033754221007 847462038526550631331511)
      ·
        refine ⟨1271193057789825946997267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 847462038526550631331511 1271193057789825946997267)
        ·
          refine ⟨1906789586684738920495901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271193057789825946997267 1906789586684738920495901)
          ·
            refine ⟨715046095006777095185963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1906789586684738920495901 715046095006777095185963)
            ·
              refine ⟨1072569142510165642778945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715046095006777095185963 1072569142510165642778945)
              ·
                refine ⟨804426856882624232084209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072569142510165642778945 804426856882624232084209)
                ·
                  refine ⟨603320142661968174063157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 804426856882624232084209 603320142661968174063157)
                  ·
                    refine ⟨56561263374559516318421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 603320142661968174063157 56561263374559516318421)
                    ·
                      rfl

theorem cell22_165229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_165229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165229 prefixEnd_165229 := by exact prefixLift 165229
  have htrace : WordTrace (prefixWord ++ tailWord_165229) baseStart_165229 baseEnd_165229 := by
    simpa [prefixWord, tailWord_165229, baseEnd_165229] using wordTrace_append hprefix tailTrace_165229
  have hstable : (prefixWord ++ tailWord_165229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165229).length < 2 ^ (prefixWord ++ tailWord_165229).sum := by decide
  have hdescent : baseEnd_165229 < baseStart_165229 := by decide
  rcases family_descends (prefixWord ++ tailWord_165229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165242 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 10]
def baseStart_165242 : Nat := 118140960795 + 165242 * 2 ^ 59
def prefixEnd_165242 : Nat := 4983230072969 + 3 ^ 40 * 165242 * 2
def baseEnd_165242 : Nat := 18855237846743938581127

theorem tailTrace_165242 : CollatzResearch.WordTrace tailWord_165242 prefixEnd_165242 18855237846743938581127 := by
  unfold tailWord_165242
  simp only [CollatzResearch.WordTrace]
  refine ⟨1506717716840982482978495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4017913911575953287942653 1506717716840982482978495)
  ·
    refine ⟨2260076575261473724467743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1506717716840982482978495 2260076575261473724467743)
    ·
      refine ⟨3390114862892210586701615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2260076575261473724467743 3390114862892210586701615)
      ·
        refine ⟨5085172294338315880052423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3390114862892210586701615 5085172294338315880052423)
        ·
          refine ⟨7627758441507473820078635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5085172294338315880052423 7627758441507473820078635)
          ·
            refine ⟨11441637662261210730117953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7627758441507473820078635 11441637662261210730117953)
            ·
              refine ⟨8581228246695908047588465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11441637662261210730117953 8581228246695908047588465)
              ·
                refine ⟨6435921185021931035691349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8581228246695908047588465 6435921185021931035691349)
                ·
                  refine ⟨18855237846743938581127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 6435921185021931035691349 18855237846743938581127)
                  ·
                    rfl

theorem cell22_165242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_165242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165242 prefixEnd_165242 := by exact prefixLift 165242
  have htrace : WordTrace (prefixWord ++ tailWord_165242) baseStart_165242 baseEnd_165242 := by
    simpa [prefixWord, tailWord_165242, baseEnd_165242] using wordTrace_append hprefix tailTrace_165242
  have hstable : (prefixWord ++ tailWord_165242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165242).length < 2 ^ (prefixWord ++ tailWord_165242).sum := by decide
  have hdescent : baseEnd_165242 < baseStart_165242 := by decide
  rcases family_descends (prefixWord ++ tailWord_165242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165274 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 3, 5]
def baseStart_165274 : Nat := 118140960795 + 165274 * 2 ^ 59
def prefixEnd_165274 : Nat := 4983230072969 + 3 ^ 40 * 165274 * 2
def baseEnd_165274 : Nat := 56576667794194398943283

theorem tailTrace_165274 : CollatzResearch.WordTrace tailWord_165274 prefixEnd_165274 56576667794194398943283 := by
  unfold tailWord_165274
  simp only [CollatzResearch.WordTrace]
  refine ⟨1507009500811999849269719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4018692002165332931385917 1507009500811999849269719)
  ·
    refine ⟨2260514251217999773904579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1507009500811999849269719 2260514251217999773904579)
    ·
      refine ⟨3390771376826999660856869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2260514251217999773904579 3390771376826999660856869)
      ·
        refine ⟨635769633155062436410663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3390771376826999660856869 635769633155062436410663)
        ·
          refine ⟨953654449732593654615995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635769633155062436410663 953654449732593654615995)
          ·
            refine ⟨1430481674598890481923993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953654449732593654615995 1430481674598890481923993)
            ·
              refine ⟨1072861255949167861442995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1430481674598890481923993 1072861255949167861442995)
              ·
                refine ⟨1609291883923751792164493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072861255949167861442995 1609291883923751792164493)
                ·
                  refine ⟨603484456471406922061685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1609291883923751792164493 603484456471406922061685)
                  ·
                    refine ⟨56576667794194398943283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 603484456471406922061685 56576667794194398943283)
                    ·
                      rfl

theorem cell22_165274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_165274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165274 prefixEnd_165274 := by exact prefixLift 165274
  have htrace : WordTrace (prefixWord ++ tailWord_165274) baseStart_165274 baseEnd_165274 := by
    simpa [prefixWord, tailWord_165274, baseEnd_165274] using wordTrace_append hprefix tailTrace_165274
  have hstable : (prefixWord ++ tailWord_165274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165274).length < 2 ^ (prefixWord ++ tailWord_165274).sum := by decide
  have hdescent : baseEnd_165274 < baseStart_165274 := by decide
  rcases family_descends (prefixWord ++ tailWord_165274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165293 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 6]
def baseStart_165293 : Nat := 118140960795 + 165293 * 2 ^ 59
def prefixEnd_165293 : Nat := 4983230072969 + 3 ^ 40 * 165293 * 2
def baseEnd_165293 : Nat := 18861057294161560906075

theorem tailTrace_165293 : CollatzResearch.WordTrace tailWord_165293 prefixEnd_165293 18861057294161560906075 := by
  unfold tailWord_165293
  simp only [CollatzResearch.WordTrace]
  refine ⟨6028730990179165642020533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4019153993452777094680355 6028730990179165642020533)
  ·
    refine ⟨565193530329296778939425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6028730990179165642020533 565193530329296778939425)
    ·
      refine ⟨423895147746972584204569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 565193530329296778939425 423895147746972584204569)
      ·
        refine ⟨317921360810229438153427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423895147746972584204569 317921360810229438153427)
        ·
          refine ⟨476882041215344157230141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317921360810229438153427 476882041215344157230141)
          ·
            refine ⟨178830765455754058961303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 476882041215344157230141 178830765455754058961303)
            ·
              refine ⟨268246148183631088441955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178830765455754058961303 268246148183631088441955)
              ·
                refine ⟨402369222275446632662933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268246148183631088441955 402369222275446632662933)
                ·
                  refine ⟨18861057294161560906075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 402369222275446632662933 18861057294161560906075)
                  ·
                    rfl

theorem cell22_165293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_165293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165293 prefixEnd_165293 := by exact prefixLift 165293
  have htrace : WordTrace (prefixWord ++ tailWord_165293) baseStart_165293 baseEnd_165293 := by
    simpa [prefixWord, tailWord_165293, baseEnd_165293] using wordTrace_append hprefix tailTrace_165293
  have hstable : (prefixWord ++ tailWord_165293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165293).length < 2 ^ (prefixWord ++ tailWord_165293).sum := by decide
  have hdescent : baseEnd_165293 < baseStart_165293 := by decide
  rcases family_descends (prefixWord ++ tailWord_165293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165400 : List Nat := [2, 1, 2, 3, 5, 1, 1, 2, 5]
def baseStart_165400 : Nat := 118140960795 + 165400 * 2 ^ 59
def prefixEnd_165400 : Nat := 4983230072969 + 3 ^ 40 * 165400 * 2
def baseEnd_165400 : Nat := 18873266723057356764299

theorem tailTrace_165400 : CollatzResearch.WordTrace tailWord_165400 prefixEnd_165400 18873266723057356764299 := by
  unfold tailWord_165400
  simp only [CollatzResearch.WordTrace]
  refine ⟨3016316800395761458082827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4021755733861015277443769 3016316800395761458082827)
  ·
    refine ⟨4524475200593642187124241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3016316800395761458082827 4524475200593642187124241)
    ·
      refine ⟨3393356400445231640343181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4524475200593642187124241 3393356400445231640343181)
      ·
        refine ⟨1272508650166961865128693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3393356400445231640343181 1272508650166961865128693)
        ·
          refine ⟨119297685953152674855815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1272508650166961865128693 119297685953152674855815)
          ·
            refine ⟨178946528929729012283723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119297685953152674855815 178946528929729012283723)
            ·
              refine ⟨268419793394593518425585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178946528929729012283723 268419793394593518425585)
              ·
                refine ⟨201314845045945138819189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268419793394593518425585 201314845045945138819189)
                ·
                  refine ⟨18873266723057356764299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 201314845045945138819189 18873266723057356764299)
                  ·
                    rfl

theorem cell22_165400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 5].length) (baseStart_165400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165400 prefixEnd_165400 := by exact prefixLift 165400
  have htrace : WordTrace (prefixWord ++ tailWord_165400) baseStart_165400 baseEnd_165400 := by
    simpa [prefixWord, tailWord_165400, baseEnd_165400] using wordTrace_append hprefix tailTrace_165400
  have hstable : (prefixWord ++ tailWord_165400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165400).length < 2 ^ (prefixWord ++ tailWord_165400).sum := by decide
  have hdescent : baseEnd_165400 < baseStart_165400 := by decide
  rcases family_descends (prefixWord ++ tailWord_165400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165441 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 1, 6]
def baseStart_165441 : Nat := 118140960795 + 165441 * 2 ^ 59
def prefixEnd_165441 : Nat := 4983230072969 + 3 ^ 40 * 165441 * 2
def baseEnd_165441 : Nat := 56633835307061630017771

theorem tailTrace_165441 : CollatzResearch.WordTrace tailWord_165441 prefixEnd_165441 56633835307061630017771 := by
  unfold tailWord_165441
  simp only [CollatzResearch.WordTrace]
  refine ⟨6034128993642986918408177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4022752662428657945605451 6034128993642986918408177)
  ·
    refine ⟨4525596745232240188806133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6034128993642986918408177 4525596745232240188806133)
    ·
      refine ⟨424274694865522517700575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4525596745232240188806133 424274694865522517700575)
      ·
        refine ⟨636412042298283776550863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424274694865522517700575 636412042298283776550863)
        ·
          refine ⟨954618063447425664826295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636412042298283776550863 954618063447425664826295)
          ·
            refine ⟨1431927095171138497239443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954618063447425664826295 1431927095171138497239443)
            ·
              refine ⟨2147890642756707745859165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1431927095171138497239443 2147890642756707745859165)
              ·
                refine ⟨805458991033765404697187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2147890642756707745859165 805458991033765404697187)
                ·
                  refine ⟨1208188486550648107045781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805458991033765404697187 1208188486550648107045781)
                  ·
                    refine ⟨56633835307061630017771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1208188486550648107045781 56633835307061630017771)
                    ·
                      rfl

theorem cell22_165441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_165441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165441 prefixEnd_165441 := by exact prefixLift 165441
  have htrace : WordTrace (prefixWord ++ tailWord_165441) baseStart_165441 baseEnd_165441 := by
    simpa [prefixWord, tailWord_165441, baseEnd_165441] using wordTrace_append hprefix tailTrace_165441
  have hstable : (prefixWord ++ tailWord_165441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165441).length < 2 ^ (prefixWord ++ tailWord_165441).sum := by decide
  have hdescent : baseEnd_165441 < baseStart_165441 := by decide
  rcases family_descends (prefixWord ++ tailWord_165441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165458 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_165458 : Nat := 118140960795 + 165458 * 2 ^ 59
def prefixEnd_165458 : Nat := 4983230072969 + 3 ^ 40 * 165458 * 2
def baseEnd_165458 : Nat := 56639654754479252342719

theorem tailTrace_165458 : CollatzResearch.WordTrace tailWord_165458 prefixEnd_165458 56639654754479252342719 := by
  unfold tailWord_165458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1508687258645349705444257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4023166023054265881184685 1508687258645349705444257)
  ·
    refine ⟨1131515443984012279083193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1508687258645349705444257 1131515443984012279083193)
    ·
      refine ⟨848636582988009209312395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1131515443984012279083193 848636582988009209312395)
      ·
        refine ⟨1272954874482013813968593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848636582988009209312395 1272954874482013813968593)
        ·
          refine ⟨954716155861510360476445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1272954874482013813968593 954716155861510360476445)
          ·
            refine ⟨358018558448066385178667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 954716155861510360476445 358018558448066385178667)
            ·
              refine ⟨537027837672099577768001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358018558448066385178667 537027837672099577768001)
              ·
                refine ⟨402770878254074683326001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537027837672099577768001 402770878254074683326001)
                ·
                  refine ⟨302078158690556012494501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402770878254074683326001 302078158690556012494501)
                  ·
                    refine ⟨56639654754479252342719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 302078158690556012494501 56639654754479252342719)
                    ·
                      rfl

theorem cell22_165458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_165458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165458 prefixEnd_165458 := by exact prefixLift 165458
  have htrace : WordTrace (prefixWord ++ tailWord_165458) baseStart_165458 baseEnd_165458 := by
    simpa [prefixWord, tailWord_165458, baseEnd_165458] using wordTrace_append hprefix tailTrace_165458
  have hstable : (prefixWord ++ tailWord_165458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165458).length < 2 ^ (prefixWord ++ tailWord_165458).sum := by decide
  have hdescent : baseEnd_165458 < baseStart_165458 := by decide
  rcases family_descends (prefixWord ++ tailWord_165458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165477 : List Nat := [1, 3, 1, 3, 3, 3, 2, 1, 2, 3]
def baseStart_165477 : Nat := 118140960795 + 165477 * 2 ^ 59
def prefixEnd_165477 : Nat := 4983230072969 + 3 ^ 40 * 165477 * 2
def baseEnd_165477 : Nat := 56646158842769536117661

theorem tailTrace_165477 : CollatzResearch.WordTrace tailWord_165477 prefixEnd_165477 56646158842769536117661 := by
  unfold tailWord_165477
  simp only [CollatzResearch.WordTrace]
  refine ⟨6035442021512565066718685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4023628014341710044479123 6035442021512565066718685)
  ·
    refine ⟨2263290758067211900019507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6035442021512565066718685 2263290758067211900019507)
    ·
      refine ⟨3394936137100817850029261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2263290758067211900019507 3394936137100817850029261)
      ·
        refine ⟨1273101051412806693760973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3394936137100817850029261 1273101051412806693760973)
        ·
          refine ⟨477412894279802510160365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1273101051412806693760973 477412894279802510160365)
          ·
            refine ⟨179029835354925941310137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 477412894279802510160365 179029835354925941310137)
            ·
              refine ⟨134272376516194455982603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179029835354925941310137 134272376516194455982603)
              ·
                refine ⟨201408564774291683973905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134272376516194455982603 201408564774291683973905)
                ·
                  refine ⟨151056423580718762980429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201408564774291683973905 151056423580718762980429)
                  ·
                    refine ⟨56646158842769536117661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 151056423580718762980429 56646158842769536117661)
                    ·
                      rfl

theorem cell22_165477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_165477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165477 prefixEnd_165477 := by exact prefixLift 165477
  have htrace : WordTrace (prefixWord ++ tailWord_165477) baseStart_165477 baseEnd_165477 := by
    simpa [prefixWord, tailWord_165477, baseEnd_165477] using wordTrace_append hprefix tailTrace_165477
  have hstable : (prefixWord ++ tailWord_165477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165477).length < 2 ^ (prefixWord ++ tailWord_165477).sum := by decide
  have hdescent : baseEnd_165477 < baseStart_165477 := by decide
  rcases family_descends (prefixWord ++ tailWord_165477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165516 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 2, 5]
def baseStart_165516 : Nat := 118140960795 + 165516 * 2 ^ 59
def prefixEnd_165516 : Nat := 4983230072969 + 3 ^ 40 * 165516 * 2
def baseEnd_165516 : Nat := 56659509339786434392541

theorem tailTrace_165516 : CollatzResearch.WordTrace tailWord_165516 prefixEnd_165516 56659509339786434392541 := by
  unfold tailWord_165516
  simp only [CollatzResearch.WordTrace]
  refine ⟨3018432234185637363694201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4024576312247516484925601 3018432234185637363694201)
  ·
    refine ⟨2263824175639228022770651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3018432234185637363694201 2263824175639228022770651)
    ·
      refine ⟨3395736263458842034155977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2263824175639228022770651 3395736263458842034155977)
      ·
        refine ⟨2546802197594131525616983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3395736263458842034155977 2546802197594131525616983)
        ·
          refine ⟨3820203296391197288425475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2546802197594131525616983 3820203296391197288425475)
          ·
            refine ⟨5730304944586795932638213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3820203296391197288425475 5730304944586795932638213)
            ·
              refine ⟨1074432177110024237369665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5730304944586795932638213 1074432177110024237369665)
              ·
                refine ⟨805824132832518178027249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1074432177110024237369665 805824132832518178027249)
                ·
                  refine ⟨604368099624388633520437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 805824132832518178027249 604368099624388633520437)
                  ·
                    refine ⟨56659509339786434392541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 604368099624388633520437 56659509339786434392541)
                    ·
                      rfl

theorem cell22_165516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_165516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165516 prefixEnd_165516 := by exact prefixLift 165516
  have htrace : WordTrace (prefixWord ++ tailWord_165516) baseStart_165516 baseEnd_165516 := by
    simpa [prefixWord, tailWord_165516, baseEnd_165516] using wordTrace_append hprefix tailTrace_165516
  have hstable : (prefixWord ++ tailWord_165516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165516).length < 2 ^ (prefixWord ++ tailWord_165516).sum := by decide
  have hdescent : baseEnd_165516 < baseStart_165516 := by decide
  rcases family_descends (prefixWord ++ tailWord_165516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165518 : List Nat := [4, 1, 1, 3, 1, 2, 1, 4, 5]
def baseStart_165518 : Nat := 118140960795 + 165518 * 2 ^ 59
def prefixEnd_165518 : Nat := 4983230072969 + 3 ^ 40 * 165518 * 2
def baseEnd_165518 : Nat := 18886731326886365280845

theorem tailTrace_165518 : CollatzResearch.WordTrace tailWord_165518 prefixEnd_165518 18886731326886365280845 := by
  unfold tailWord_165518
  simp only [CollatzResearch.WordTrace]
  refine ⟨754617176795503633620151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4024624942909352712640805 754617176795503633620151)
  ·
    refine ⟨1131925765193255450430227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 754617176795503633620151 1131925765193255450430227)
    ·
      refine ⟨1697888647789883175645341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1131925765193255450430227 1697888647789883175645341)
      ·
        refine ⟨636708242921206190867003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1697888647789883175645341 636708242921206190867003)
        ·
          refine ⟨955062364381809286300505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636708242921206190867003 955062364381809286300505)
          ·
            refine ⟨716296773286356964725379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 955062364381809286300505 716296773286356964725379)
            ·
              refine ⟨1074445159929535447088069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716296773286356964725379 1074445159929535447088069)
              ·
                refine ⟨201458467486787896329013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1074445159929535447088069 201458467486787896329013)
                ·
                  refine ⟨18886731326886365280845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 201458467486787896329013 18886731326886365280845)
                  ·
                    rfl

theorem cell22_165518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_165518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165518 prefixEnd_165518 := by exact prefixLift 165518
  have htrace : WordTrace (prefixWord ++ tailWord_165518) baseStart_165518 baseEnd_165518 := by
    simpa [prefixWord, tailWord_165518, baseEnd_165518] using wordTrace_append hprefix tailTrace_165518
  have hstable : (prefixWord ++ tailWord_165518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165518).length < 2 ^ (prefixWord ++ tailWord_165518).sum := by decide
  have hdescent : baseEnd_165518 < baseStart_165518 := by decide
  rcases family_descends (prefixWord ++ tailWord_165518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165580 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 6]
def baseStart_165580 : Nat := 118140960795 + 165580 * 2 ^ 59
def prefixEnd_165580 : Nat := 4983230072969 + 3 ^ 40 * 165580 * 2
def baseEnd_165580 : Nat := 18893805949237200264115

theorem tailTrace_165580 : CollatzResearch.WordTrace tailWord_165580 prefixEnd_165580 18893805949237200264115 := by
  unfold tailWord_165580
  simp only [CollatzResearch.WordTrace]
  refine ⟨3019599370069706828859097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4026132493426275771812129 3019599370069706828859097)
  ·
    refine ⟨2264699527552280121644323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3019599370069706828859097 2264699527552280121644323)
    ·
      refine ⟨3397049291328420182466485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2264699527552280121644323 3397049291328420182466485)
      ·
        refine ⟨318473371062039392106233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3397049291328420182466485 318473371062039392106233)
        ·
          refine ⟨238855028296529544079675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318473371062039392106233 238855028296529544079675)
          ·
            refine ⟨358282542444794316119513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238855028296529544079675 358282542444794316119513)
            ·
              refine ⟨268711906833595737089635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358282542444794316119513 268711906833595737089635)
              ·
                refine ⟨403067860250393605634453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268711906833595737089635 403067860250393605634453)
                ·
                  refine ⟨18893805949237200264115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 403067860250393605634453 18893805949237200264115)
                  ·
                    rfl

theorem cell22_165580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_165580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165580 prefixEnd_165580 := by exact prefixLift 165580
  have htrace : WordTrace (prefixWord ++ tailWord_165580) baseStart_165580 baseEnd_165580 := by
    simpa [prefixWord, tailWord_165580, baseEnd_165580] using wordTrace_append hprefix tailTrace_165580
  have hstable : (prefixWord ++ tailWord_165580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165580).length < 2 ^ (prefixWord ++ tailWord_165580).sum := by decide
  have hdescent : baseEnd_165580 < baseStart_165580 := by decide
  rcases family_descends (prefixWord ++ tailWord_165580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165591 : List Nat := [1, 1, 3, 2, 1, 3, 2, 9]
def baseStart_165591 : Nat := 118140960795 + 165591 * 2 ^ 59
def prefixEnd_165591 : Nat := 4983230072969 + 3 ^ 40 * 165591 * 2
def baseEnd_165591 : Nat := 6298353708056804307479

theorem tailTrace_165591 : CollatzResearch.WordTrace tailWord_165591 prefixEnd_165591 6298353708056804307479 := by
  unfold tailWord_165591
  simp only [CollatzResearch.WordTrace]
  refine ⟨6039599943099562536368627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4026399962066375024245751 6039599943099562536368627)
  ·
    refine ⟨9059399914649343804552941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6039599943099562536368627 9059399914649343804552941)
    ·
      refine ⟨3397274967993503926707353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9059399914649343804552941 3397274967993503926707353)
      ·
        refine ⟨2547956225995127945030515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3397274967993503926707353 2547956225995127945030515)
        ·
          refine ⟨3821934338992691917545773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547956225995127945030515 3821934338992691917545773)
          ·
            refine ⟨1433225377122259469079665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3821934338992691917545773 1433225377122259469079665)
            ·
              refine ⟨1074919032841694601809749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1433225377122259469079665 1074919032841694601809749)
              ·
                refine ⟨6298353708056804307479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1074919032841694601809749 6298353708056804307479)
                ·
                  rfl

theorem cell22_165591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 9].length) (baseStart_165591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165591 prefixEnd_165591 := by exact prefixLift 165591
  have htrace : WordTrace (prefixWord ++ tailWord_165591) baseStart_165591 baseEnd_165591 := by
    simpa [prefixWord, tailWord_165591, baseEnd_165591] using wordTrace_append hprefix tailTrace_165591
  have hstable : (prefixWord ++ tailWord_165591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165591).length < 2 ^ (prefixWord ++ tailWord_165591).sum := by decide
  have hdescent : baseEnd_165591 < baseStart_165591 := by decide
  rcases family_descends (prefixWord ++ tailWord_165591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165608 : List Nat := [2, 1, 4, 1, 3, 2, 1, 8]
def baseStart_165608 : Nat := 118140960795 + 165608 * 2 ^ 59
def prefixEnd_165608 : Nat := 4983230072969 + 3 ^ 40 * 165608 * 2
def baseEnd_165608 : Nat := 6299000313325429010251

theorem tailTrace_165608 : CollatzResearch.WordTrace tailWord_165608 prefixEnd_165608 6299000313325429010251 := by
  unfold tailWord_165608
  simp only [CollatzResearch.WordTrace]
  refine ⟨3020109992018987219868739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4026813322691982959824985 3020109992018987219868739)
  ·
    refine ⟨4530164988028480829803109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3020109992018987219868739 4530164988028480829803109)
    ·
      refine ⟨849405935255340155588083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4530164988028480829803109 849405935255340155588083)
      ·
        refine ⟨1274108902883010233382125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 849405935255340155588083 1274108902883010233382125)
        ·
          refine ⟨477790838581128837518297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1274108902883010233382125 477790838581128837518297)
          ·
            refine ⟨358343128935846628138723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477790838581128837518297 358343128935846628138723)
            ·
              refine ⟨537514693403769942208085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358343128935846628138723 537514693403769942208085)
              ·
                refine ⟨6299000313325429010251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 537514693403769942208085 6299000313325429010251)
                ·
                  rfl

theorem cell22_165608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 8].length) (baseStart_165608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165608 prefixEnd_165608 := by exact prefixLift 165608
  have htrace : WordTrace (prefixWord ++ tailWord_165608) baseStart_165608 baseEnd_165608 := by
    simpa [prefixWord, tailWord_165608, baseEnd_165608] using wordTrace_append hprefix tailTrace_165608
  have hstable : (prefixWord ++ tailWord_165608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165608).length < 2 ^ (prefixWord ++ tailWord_165608).sum := by decide
  have hdescent : baseEnd_165608 < baseStart_165608 := by decide
  rcases family_descends (prefixWord ++ tailWord_165608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165623 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 5, 3]
def baseStart_165623 : Nat := 118140960795 + 165623 * 2 ^ 59
def prefixEnd_165623 : Nat := 4983230072969 + 3 ^ 40 * 165623 * 2
def baseEnd_165623 : Nat := 56696137626473821967213

theorem tailTrace_165623 : CollatzResearch.WordTrace tailWord_165623 prefixEnd_165623 56696137626473821967213 := by
  unfold tailWord_165623
  simp only [CollatzResearch.WordTrace]
  refine ⟨6040767078983632001533523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4027178052655754667689015 6040767078983632001533523)
  ·
    refine ⟨9061150618475448002300285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6040767078983632001533523 9061150618475448002300285)
    ·
      refine ⟨3397931481928293000862607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9061150618475448002300285 3397931481928293000862607)
      ·
        refine ⟨5096897222892439501293911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3397931481928293000862607 5096897222892439501293911)
        ·
          refine ⟨7645345834338659251940867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5096897222892439501293911 7645345834338659251940867)
          ·
            refine ⟨11468018751507988877911301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7645345834338659251940867 11468018751507988877911301)
            ·
              refine ⟨2150253515907747914608369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11468018751507988877911301 2150253515907747914608369)
              ·
                refine ⟨1612690136930810935956277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2150253515907747914608369 1612690136930810935956277)
                ·
                  refine ⟨151189700337263525245901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1612690136930810935956277 151189700337263525245901)
                  ·
                    refine ⟨56696137626473821967213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 151189700337263525245901 56696137626473821967213)
                    ·
                      rfl

theorem cell22_165623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_165623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165623 prefixEnd_165623 := by exact prefixLift 165623
  have htrace : WordTrace (prefixWord ++ tailWord_165623) baseStart_165623 baseEnd_165623 := by
    simpa [prefixWord, tailWord_165623, baseEnd_165623] using wordTrace_append hprefix tailTrace_165623
  have hstable : (prefixWord ++ tailWord_165623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165623).length < 2 ^ (prefixWord ++ tailWord_165623).sum := by decide
  have hdescent : baseEnd_165623 < baseStart_165623 := by decide
  rcases family_descends (prefixWord ++ tailWord_165623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165702 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_165702 : Nat := 118140960795 + 165702 * 2 ^ 59
def prefixEnd_165702 : Nat := 4983230072969 + 3 ^ 40 * 165702 * 2
def baseEnd_165702 : Nat := 56723180940943949241971

theorem tailTrace_165702 : CollatzResearch.WordTrace tailWord_165702 prefixEnd_165702 56723180940943949241971 := by
  unfold tailWord_165702
  simp only [CollatzResearch.WordTrace]
  refine ⟨188864013928044640426855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4029098963798285662439573 188864013928044640426855)
  ·
    refine ⟨283296020892066960640283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188864013928044640426855 283296020892066960640283)
    ·
      refine ⟨424944031338100440960425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283296020892066960640283 424944031338100440960425)
      ·
        refine ⟨318708023503575330720319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424944031338100440960425 318708023503575330720319)
        ·
          refine ⟨478062035255362996080479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318708023503575330720319 478062035255362996080479)
          ·
            refine ⟨717093052883044494120719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478062035255362996080479 717093052883044494120719)
            ·
              refine ⟨1075639579324566741181079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717093052883044494120719 1075639579324566741181079)
              ·
                refine ⟨1613459368986850111771619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075639579324566741181079 1613459368986850111771619)
                ·
                  refine ⟨2420189053480275167657429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613459368986850111771619 2420189053480275167657429)
                  ·
                    refine ⟨56723180940943949241971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2420189053480275167657429 56723180940943949241971)
                    ·
                      rfl

theorem cell22_165702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_165702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165702 prefixEnd_165702 := by exact prefixLift 165702
  have htrace : WordTrace (prefixWord ++ tailWord_165702) baseStart_165702 baseEnd_165702 := by
    simpa [prefixWord, tailWord_165702, baseEnd_165702] using wordTrace_append hprefix tailTrace_165702
  have hstable : (prefixWord ++ tailWord_165702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165702).length < 2 ^ (prefixWord ++ tailWord_165702).sum := by decide
  have hdescent : baseEnd_165702 < baseStart_165702 := by decide
  rcases family_descends (prefixWord ++ tailWord_165702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165809 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 3, 3]
def baseStart_165809 : Nat := 118140960795 + 165809 * 2 ^ 59
def prefixEnd_165809 : Nat := 4983230072969 + 3 ^ 40 * 165809 * 2
def baseEnd_165809 : Nat := 56759809227631336816643

theorem tailTrace_165809 : CollatzResearch.WordTrace tailWord_165809 prefixEnd_165809 56759809227631336816643 := by
  unfold tailWord_165809
  simp only [CollatzResearch.WordTrace]
  refine ⟨6047551056309785767804481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4031700704206523845202987 6047551056309785767804481)
  ·
    refine ⟨4535663292232339325853361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6047551056309785767804481 4535663292232339325853361)
    ·
      refine ⟨3401747469174254494390021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4535663292232339325853361 3401747469174254494390021)
      ·
        refine ⟨637827650470172717698129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3401747469174254494390021 637827650470172717698129)
        ·
          refine ⟨478370737852629538273597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637827650470172717698129 478370737852629538273597)
          ·
            refine ⟨179389026694736076852599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 478370737852629538273597 179389026694736076852599)
            ·
              refine ⟨269083540042104115278899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179389026694736076852599 269083540042104115278899)
              ·
                refine ⟨403625310063156172918349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269083540042104115278899 403625310063156172918349)
                ·
                  refine ⟨151359491273683564844381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403625310063156172918349 151359491273683564844381)
                  ·
                    refine ⟨56759809227631336816643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 151359491273683564844381 56759809227631336816643)
                    ·
                      rfl

theorem cell22_165809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_165809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165809 prefixEnd_165809 := by exact prefixLift 165809
  have htrace : WordTrace (prefixWord ++ tailWord_165809) baseStart_165809 baseEnd_165809 := by
    simpa [prefixWord, tailWord_165809, baseEnd_165809] using wordTrace_append hprefix tailTrace_165809
  have hstable : (prefixWord ++ tailWord_165809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165809).length < 2 ^ (prefixWord ++ tailWord_165809).sum := by decide
  have hdescent : baseEnd_165809 < baseStart_165809 := by decide
  rcases family_descends (prefixWord ++ tailWord_165809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165822 : List Nat := [4, 2, 1, 1, 1, 4, 1, 3, 5]
def baseStart_165822 : Nat := 118140960795 + 165822 * 2 ^ 59
def prefixEnd_165822 : Nat := 4983230072969 + 3 ^ 40 * 165822 * 2
def baseEnd_165822 : Nat := 18921419797767878747201

theorem tailTrace_165822 : CollatzResearch.WordTrace tailWord_165822 prefixEnd_165822 18921419797767878747201 := by
  unfold tailWord_165822
  simp only [CollatzResearch.WordTrace]
  refine ⟨756003150657836123503465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4032016803508459325351813 756003150657836123503465)
  ·
    refine ⟨567002362993377092627599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 756003150657836123503465 567002362993377092627599)
    ·
      refine ⟨850503544490065638941399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 567002362993377092627599 850503544490065638941399)
      ·
        refine ⟨1275755316735098458412099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 850503544490065638941399 1275755316735098458412099)
        ·
          refine ⟨1913632975102647687618149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1275755316735098458412099 1913632975102647687618149)
          ·
            refine ⟨358806182831746441428403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1913632975102647687618149 358806182831746441428403)
            ·
              refine ⟨538209274247619662142605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358806182831746441428403 538209274247619662142605)
              ·
                refine ⟨201828477842857373303477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 538209274247619662142605 201828477842857373303477)
                ·
                  refine ⟨18921419797767878747201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 201828477842857373303477 18921419797767878747201)
                  ·
                    rfl

theorem cell22_165822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_165822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165822 prefixEnd_165822 := by exact prefixLift 165822
  have htrace : WordTrace (prefixWord ++ tailWord_165822) baseStart_165822 baseEnd_165822 := by
    simpa [prefixWord, tailWord_165822, baseEnd_165822] using wordTrace_append hprefix tailTrace_165822
  have hstable : (prefixWord ++ tailWord_165822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165822).length < 2 ^ (prefixWord ++ tailWord_165822).sum := by decide
  have hdescent : baseEnd_165822 < baseStart_165822 := by decide
  rcases family_descends (prefixWord ++ tailWord_165822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165835 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 3, 4]
def baseStart_165835 : Nat := 118140960795 + 165835 * 2 ^ 59
def prefixEnd_165835 : Nat := 4983230072969 + 3 ^ 40 * 165835 * 2
def baseEnd_165835 : Nat := 56768709558975935666563

theorem tailTrace_165835 : CollatzResearch.WordTrace tailWord_165835 prefixEnd_165835 56768709558975935666563 := by
  unfold tailWord_165835
  simp only [CollatzResearch.WordTrace]
  refine ⟨6048499354215592208250959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4032332902810394805500639 6048499354215592208250959)
  ·
    refine ⟨9072749031323388312376439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6048499354215592208250959 9072749031323388312376439)
    ·
      refine ⟨13609123546985082468564659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9072749031323388312376439 13609123546985082468564659)
      ·
        refine ⟨20413685320477623702846989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13609123546985082468564659 20413685320477623702846989)
        ·
          refine ⟨7655131995179108888567621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20413685320477623702846989 7655131995179108888567621)
          ·
            refine ⟨1435337249096082916606429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7655131995179108888567621 1435337249096082916606429)
            ·
              refine ⟨538251468411031093727411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1435337249096082916606429 538251468411031093727411)
              ·
                refine ⟨807377202616546640591117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538251468411031093727411 807377202616546640591117)
                ·
                  refine ⟨302766450981204990221669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807377202616546640591117 302766450981204990221669)
                  ·
                    refine ⟨56768709558975935666563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 302766450981204990221669 56768709558975935666563)
                    ·
                      rfl

theorem cell22_165835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 4].length) (baseStart_165835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165835 prefixEnd_165835 := by exact prefixLift 165835
  have htrace : WordTrace (prefixWord ++ tailWord_165835) baseStart_165835 baseEnd_165835 := by
    simpa [prefixWord, tailWord_165835, baseEnd_165835] using wordTrace_append hprefix tailTrace_165835
  have hstable : (prefixWord ++ tailWord_165835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165835).length < 2 ^ (prefixWord ++ tailWord_165835).sum := by decide
  have hdescent : baseEnd_165835 < baseStart_165835 := by decide
  rcases family_descends (prefixWord ++ tailWord_165835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165880 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 4, 4]
def baseStart_165880 : Nat := 118140960795 + 165880 * 2 ^ 59
def prefixEnd_165880 : Nat := 4983230072969 + 3 ^ 40 * 165880 * 2
def baseEnd_165880 : Nat := 56784113978610818291425

theorem tailTrace_165880 : CollatzResearch.WordTrace tailWord_165880 prefixEnd_165880 56784113978610818291425 := by
  unfold tailWord_165880
  simp only [CollatzResearch.WordTrace]
  refine ⟨3025070319526282446819547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4033427092701709929092729 3025070319526282446819547)
  ·
    refine ⟨4537605479289423670229321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3025070319526282446819547 4537605479289423670229321)
    ·
      refine ⟨3403204109467067752671991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4537605479289423670229321 3403204109467067752671991)
      ·
        refine ⟨5104806164200601629007987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3403204109467067752671991 5104806164200601629007987)
        ·
          refine ⟨7657209246300902443511981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5104806164200601629007987 7657209246300902443511981)
          ·
            refine ⟨2871453467362838416316993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7657209246300902443511981 2871453467362838416316993)
            ·
              refine ⟨2153590100522128812237745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2871453467362838416316993 2153590100522128812237745)
              ·
                refine ⟨1615192575391596609178309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2153590100522128812237745 1615192575391596609178309)
                ·
                  refine ⟨302848607885924364220933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1615192575391596609178309 302848607885924364220933)
                  ·
                    refine ⟨56784113978610818291425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 302848607885924364220933 56784113978610818291425)
                    ·
                      rfl

theorem cell22_165880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_165880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165880 prefixEnd_165880 := by exact prefixLift 165880
  have htrace : WordTrace (prefixWord ++ tailWord_165880) baseStart_165880 baseEnd_165880 := by
    simpa [prefixWord, tailWord_165880, baseEnd_165880] using wordTrace_append hprefix tailTrace_165880
  have hstable : (prefixWord ++ tailWord_165880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165880).length < 2 ^ (prefixWord ++ tailWord_165880).sum := by decide
  have hdescent : baseEnd_165880 < baseStart_165880 := by decide
  rcases family_descends (prefixWord ++ tailWord_165880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165916 : List Nat := [2, 2, 3, 1, 3, 3, 1, 2, 2, 3]
def baseStart_165916 : Nat := 118140960795 + 165916 * 2 ^ 59
def prefixEnd_165916 : Nat := 4983230072969 + 3 ^ 40 * 165916 * 2
def baseEnd_165916 : Nat := 56796437514318724391315

theorem tailTrace_165916 : CollatzResearch.WordTrace tailWord_165916 prefixEnd_165916 56796437514318724391315 := by
  unfold tailWord_165916
  simp only [CollatzResearch.WordTrace]
  refine ⟨3025726833461071520974801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4034302444614762027966401 3025726833461071520974801)
  ·
    refine ⟨2269295125095803640731101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3025726833461071520974801 2269295125095803640731101)
    ·
      refine ⟨850985671910926365274163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2269295125095803640731101 850985671910926365274163)
      ·
        refine ⟨1276478507866389547911245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 850985671910926365274163 1276478507866389547911245)
        ·
          refine ⟨478679440449896080466717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1276478507866389547911245 478679440449896080466717)
          ·
            refine ⟨179504790168711030175019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 478679440449896080466717 179504790168711030175019)
            ·
              refine ⟨269257185253066545262529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179504790168711030175019 269257185253066545262529)
              ·
                refine ⟨201942888939799908946897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269257185253066545262529 201942888939799908946897)
                ·
                  refine ⟨151457166704849931710173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201942888939799908946897 151457166704849931710173)
                  ·
                    refine ⟨56796437514318724391315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 151457166704849931710173 56796437514318724391315)
                    ·
                      rfl

theorem cell22_165916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_165916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165916 prefixEnd_165916 := by exact prefixLift 165916
  have htrace : WordTrace (prefixWord ++ tailWord_165916) baseStart_165916 baseEnd_165916 := by
    simpa [prefixWord, tailWord_165916, baseEnd_165916] using wordTrace_append hprefix tailTrace_165916
  have hstable : (prefixWord ++ tailWord_165916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165916).length < 2 ^ (prefixWord ++ tailWord_165916).sum := by decide
  have hdescent : baseEnd_165916 < baseStart_165916 := by decide
  rcases family_descends (prefixWord ++ tailWord_165916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165955 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 4, 5]
def baseStart_165955 : Nat := 118140960795 + 165955 * 2 ^ 59
def prefixEnd_165955 : Nat := 4983230072969 + 3 ^ 40 * 165955 * 2
def baseEnd_165955 : Nat := 56809788011335622666195

theorem tailTrace_165955 : CollatzResearch.WordTrace tailWord_165955 prefixEnd_165955 56809788011335622666195 := by
  unfold tailWord_165955
  simp only [CollatzResearch.WordTrace]
  refine ⟨6052876113780852702619319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4035250742520568468412879 6052876113780852702619319)
  ·
    refine ⟨9079314170671279053928979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6052876113780852702619319 9079314170671279053928979)
    ·
      refine ⟨13618971256006918580893469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9079314170671279053928979 13618971256006918580893469)
      ·
        refine ⟨5107114221002594467835051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13618971256006918580893469 5107114221002594467835051)
        ·
          refine ⟨7660671331503891701752577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5107114221002594467835051 7660671331503891701752577)
          ·
            refine ⟨5745503498627918776314433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7660671331503891701752577 5745503498627918776314433)
            ·
              refine ⟨4309127623970939082235825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5745503498627918776314433 4309127623970939082235825)
              ·
                refine ⟨3231845717978204311676869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4309127623970939082235825 3231845717978204311676869)
                ·
                  refine ⟨605971072120913308439413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3231845717978204311676869 605971072120913308439413)
                  ·
                    refine ⟨56809788011335622666195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 605971072120913308439413 56809788011335622666195)
                    ·
                      rfl

theorem cell22_165955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 5].length) (baseStart_165955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_165955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_165955 prefixEnd_165955 := by exact prefixLift 165955
  have htrace : WordTrace (prefixWord ++ tailWord_165955) baseStart_165955 baseEnd_165955 := by
    simpa [prefixWord, tailWord_165955, baseEnd_165955] using wordTrace_append hprefix tailTrace_165955
  have hstable : (prefixWord ++ tailWord_165955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165955).length < 2 ^ (prefixWord ++ tailWord_165955).sum := by decide
  have hdescent : baseEnd_165955 < baseStart_165955 := by decide
  rcases family_descends (prefixWord ++ tailWord_165955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166021 : List Nat := [1, 3, 1, 1, 5, 2, 3, 1, 1, 4]
def baseStart_166021 : Nat := 118140960795 + 166021 * 2 ^ 59
def prefixEnd_166021 : Nat := 4983230072969 + 3 ^ 40 * 166021 * 2
def baseEnd_166021 : Nat := 56832381160133450515993

theorem tailTrace_166021 : CollatzResearch.WordTrace tailWord_166021 prefixEnd_166021 56832381160133450515993 := by
  unfold tailWord_166021
  simp only [CollatzResearch.WordTrace]
  refine ⟨6055283331541745974521917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4036855554361163983014611 6055283331541745974521917)
  ·
    refine ⟨2270731249328154740445719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6055283331541745974521917 2270731249328154740445719)
    ·
      refine ⟨3406096873992232110668579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2270731249328154740445719 3406096873992232110668579)
      ·
        refine ⟨5109145310988348166002869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3406096873992232110668579 5109145310988348166002869)
        ·
          refine ⟨478982372905157640562769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5109145310988348166002869 478982372905157640562769)
          ·
            refine ⟨359236779678868230422077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 478982372905157640562769 359236779678868230422077)
            ·
              refine ⟨134713792379575586408279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359236779678868230422077 134713792379575586408279)
              ·
                refine ⟨202070688569363379612419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134713792379575586408279 202070688569363379612419)
                ·
                  refine ⟨303106032854045069418629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202070688569363379612419 303106032854045069418629)
                  ·
                    refine ⟨56832381160133450515993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 303106032854045069418629 56832381160133450515993)
                    ·
                      rfl

theorem cell22_166021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_166021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166021 prefixEnd_166021 := by exact prefixLift 166021
  have htrace : WordTrace (prefixWord ++ tailWord_166021) baseStart_166021 baseEnd_166021 := by
    simpa [prefixWord, tailWord_166021, baseEnd_166021] using wordTrace_append hprefix tailTrace_166021
  have hstable : (prefixWord ++ tailWord_166021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166021).length < 2 ^ (prefixWord ++ tailWord_166021).sum := by decide
  have hdescent : baseEnd_166021 < baseStart_166021 := by decide
  rcases family_descends (prefixWord ++ tailWord_166021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166032 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 2, 4]
def baseStart_166032 : Nat := 118140960795 + 166032 * 2 ^ 59
def prefixEnd_166032 : Nat := 4983230072969 + 3 ^ 40 * 166032 * 2
def baseEnd_166032 : Nat := 56836146684933088490959

theorem tailTrace_166032 : CollatzResearch.WordTrace tailWord_166032 prefixEnd_166032 56836146684933088490959 := by
  unfold tailWord_166032
  simp only [CollatzResearch.WordTrace]
  refine ⟨3027842267250947426586175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4037123023001263235448233 3027842267250947426586175)
  ·
    refine ⟨4541763400876421139879263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3027842267250947426586175 4541763400876421139879263)
    ·
      refine ⟨6812645101314631709818895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4541763400876421139879263 6812645101314631709818895)
      ·
        refine ⟨10218967651971947564728343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6812645101314631709818895 10218967651971947564728343)
        ·
          refine ⟨15328451477957921347092515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10218967651971947564728343 15328451477957921347092515)
          ·
            refine ⟨22992677216936882020638773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15328451477957921347092515 22992677216936882020638773)
            ·
              refine ⟨2155563489087832689434885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22992677216936882020638773 2155563489087832689434885)
              ·
                refine ⟨404168154203968629269041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2155563489087832689434885 404168154203968629269041)
                ·
                  refine ⟨303126115652976471951781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404168154203968629269041 303126115652976471951781)
                  ·
                    refine ⟨56836146684933088490959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 303126115652976471951781 56836146684933088490959)
                    ·
                      rfl

theorem cell22_166032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_166032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166032 prefixEnd_166032 := by exact prefixLift 166032
  have htrace : WordTrace (prefixWord ++ tailWord_166032) baseStart_166032 baseEnd_166032 := by
    simpa [prefixWord, tailWord_166032, baseEnd_166032] using wordTrace_append hprefix tailTrace_166032
  have hstable : (prefixWord ++ tailWord_166032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166032).length < 2 ^ (prefixWord ++ tailWord_166032).sum := by decide
  have hdescent : baseEnd_166032 < baseStart_166032 := by decide
  rcases family_descends (prefixWord ++ tailWord_166032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166130 : List Nat := [3, 2, 1, 3, 2, 3, 1, 3, 1, 3]
def baseStart_166130 : Nat := 118140960795 + 166130 * 2 ^ 59
def prefixEnd_166130 : Nat := 4983230072969 + 3 ^ 40 * 166130 * 2
def baseEnd_166130 : Nat := 56869694087693499540659

theorem tailTrace_166130 : CollatzResearch.WordTrace tailWord_166130 prefixEnd_166130 56869694087693499540659 := by
  unfold tailWord_166130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1514814722036714397559961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4039505925431238393493229 1514814722036714397559961)
  ·
    refine ⟨1136111041527535798169971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1514814722036714397559961 1136111041527535798169971)
    ·
      refine ⟨1704166562291303697254957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1136111041527535798169971 1704166562291303697254957)
      ·
        refine ⟨639062460859238886470609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1704166562291303697254957 639062460859238886470609)
        ·
          refine ⟨479296845644429164852957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 639062460859238886470609 479296845644429164852957)
          ·
            refine ⟨179736317116660936819859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 479296845644429164852957 179736317116660936819859)
            ·
              refine ⟨269604475674991405229789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179736317116660936819859 269604475674991405229789)
              ·
                refine ⟨101101678378121776961171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269604475674991405229789 101101678378121776961171)
                ·
                  refine ⟨151652517567182665441757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101101678378121776961171 151652517567182665441757)
                  ·
                    refine ⟨56869694087693499540659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 151652517567182665441757 56869694087693499540659)
                    ·
                      rfl

theorem cell22_166130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_166130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166130 prefixEnd_166130 := by exact prefixLift 166130
  have htrace : WordTrace (prefixWord ++ tailWord_166130) baseStart_166130 baseEnd_166130 := by
    simpa [prefixWord, tailWord_166130, baseEnd_166130] using wordTrace_append hprefix tailTrace_166130
  have hstable : (prefixWord ++ tailWord_166130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166130).length < 2 ^ (prefixWord ++ tailWord_166130).sum := by decide
  have hdescent : baseEnd_166130 < baseStart_166130 := by decide
  rcases family_descends (prefixWord ++ tailWord_166130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166154 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 6]
def baseStart_166154 : Nat := 118140960795 + 166154 * 2 ^ 59
def prefixEnd_166154 : Nat := 4983230072969 + 3 ^ 40 * 166154 * 2
def baseEnd_166154 : Nat := 18959303259388478980195

theorem tailTrace_166154 : CollatzResearch.WordTrace tailWord_166154 prefixEnd_166154 18959303259388478980195 := by
  unfold tailWord_166154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1515033560014977422278379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4040089493373273126075677 1515033560014977422278379)
  ·
    refine ⟨2272550340022466133417569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1515033560014977422278379 2272550340022466133417569)
    ·
      refine ⟨1704412755016849600063177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2272550340022466133417569 1704412755016849600063177)
      ·
        refine ⟨1278309566262637200047383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1704412755016849600063177 1278309566262637200047383)
        ·
          refine ⟨1917464349393955800071075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278309566262637200047383 1917464349393955800071075)
          ·
            refine ⟨2876196524090933700106613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917464349393955800071075 2876196524090933700106613)
            ·
              refine ⟨269643424133525034384995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2876196524090933700106613 269643424133525034384995)
              ·
                refine ⟨404465136200287551577493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269643424133525034384995 404465136200287551577493)
                ·
                  refine ⟨18959303259388478980195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 404465136200287551577493 18959303259388478980195)
                  ·
                    rfl

theorem cell22_166154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_166154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166154 prefixEnd_166154 := by exact prefixLift 166154
  have htrace : WordTrace (prefixWord ++ tailWord_166154) baseStart_166154 baseEnd_166154 := by
    simpa [prefixWord, tailWord_166154, baseEnd_166154] using wordTrace_append hprefix tailTrace_166154
  have hstable : (prefixWord ++ tailWord_166154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166154).length < 2 ^ (prefixWord ++ tailWord_166154).sum := by decide
  have hdescent : baseEnd_166154 < baseStart_166154 := by decide
  rcases family_descends (prefixWord ++ tailWord_166154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166201 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 2, 4]
def baseStart_166201 : Nat := 118140960795 + 166201 * 2 ^ 59
def prefixEnd_166201 : Nat := 4983230072969 + 3 ^ 40 * 166201 * 2
def baseEnd_166201 : Nat := 56893998838672981015441

theorem tailTrace_166201 : CollatzResearch.WordTrace tailWord_166201 prefixEnd_166201 56893998838672981015441 := by
  unfold tailWord_166201
  simp only [CollatzResearch.WordTrace]
  refine ⟨6061848470889636716074457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4041232313926424477382971 6061848470889636716074457)
  ·
    refine ⟨4546386353167227537055843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6061848470889636716074457 4546386353167227537055843)
    ·
      refine ⟨6819579529750841305583765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4546386353167227537055843 6819579529750841305583765)
      ·
        refine ⟨319667790457070686199239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6819579529750841305583765 319667790457070686199239)
        ·
          refine ⟨479501685685606029298859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319667790457070686199239 479501685685606029298859)
          ·
            refine ⟨719252528528409043948289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479501685685606029298859 719252528528409043948289)
            ·
              refine ⟨539439396396306782961217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719252528528409043948289 539439396396306782961217)
              ·
                refine ⟨404579547297230087220913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539439396396306782961217 404579547297230087220913)
                ·
                  refine ⟨303434660472922565415685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404579547297230087220913 303434660472922565415685)
                  ·
                    refine ⟨56893998838672981015441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 303434660472922565415685 56893998838672981015441)
                    ·
                      rfl

theorem cell22_166201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_166201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166201 prefixEnd_166201 := by exact prefixLift 166201
  have htrace : WordTrace (prefixWord ++ tailWord_166201) baseStart_166201 baseEnd_166201 := by
    simpa [prefixWord, tailWord_166201, baseEnd_166201] using wordTrace_append hprefix tailTrace_166201
  have hstable : (prefixWord ++ tailWord_166201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166201).length < 2 ^ (prefixWord ++ tailWord_166201).sum := by decide
  have hdescent : baseEnd_166201 < baseStart_166201 := by decide
  rcases family_descends (prefixWord ++ tailWord_166201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166231 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 3, 3]
def baseStart_166231 : Nat := 118140960795 + 166231 * 2 ^ 59
def prefixEnd_166231 : Nat := 4983230072969 + 3 ^ 40 * 166231 * 2
def baseEnd_166231 : Nat := 56904268451762902765349

theorem tailTrace_166231 : CollatzResearch.WordTrace tailWord_166231 prefixEnd_166231 56904268451762902765349 := by
  unfold tailWord_166231
  simp only [CollatzResearch.WordTrace]
  refine ⟨6062942660780951839666547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4041961773853967893111031 6062942660780951839666547)
  ·
    refine ⟨9094413991171427759499821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6062942660780951839666547 9094413991171427759499821)
    ·
      refine ⟨3410405246689285409812433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9094413991171427759499821 3410405246689285409812433)
      ·
        refine ⟨2557803935016964057359325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3410405246689285409812433 2557803935016964057359325)
        ·
          refine ⟨959176475631361521509747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2557803935016964057359325 959176475631361521509747)
          ·
            refine ⟨1438764713447042282264621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959176475631361521509747 1438764713447042282264621)
            ·
              refine ⟨539536767542640855849233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1438764713447042282264621 539536767542640855849233)
              ·
                refine ⟨404652575656980641886925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539536767542640855849233 404652575656980641886925)
                ·
                  refine ⟨151744715871367740707597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 404652575656980641886925 151744715871367740707597)
                  ·
                    refine ⟨56904268451762902765349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 151744715871367740707597 56904268451762902765349)
                    ·
                      rfl

theorem cell22_166231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_166231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166231 prefixEnd_166231 := by exact prefixLift 166231
  have htrace : WordTrace (prefixWord ++ tailWord_166231) baseStart_166231 baseEnd_166231 := by
    simpa [prefixWord, tailWord_166231, baseEnd_166231] using wordTrace_append hprefix tailTrace_166231
  have hstable : (prefixWord ++ tailWord_166231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166231).length < 2 ^ (prefixWord ++ tailWord_166231).sum := by decide
  have hdescent : baseEnd_166231 < baseStart_166231 := by decide
  rcases family_descends (prefixWord ++ tailWord_166231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166244 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 7]
def baseStart_166244 : Nat := 118140960795 + 166244 * 2 ^ 59
def prefixEnd_166244 : Nat := 4983230072969 + 3 ^ 40 * 166244 * 2
def baseEnd_166244 : Nat := 18969572872478400730103

theorem tailTrace_166244 : CollatzResearch.WordTrace tailWord_166244 prefixEnd_166244 18969572872478400730103 := by
  unfold tailWord_166244
  simp only [CollatzResearch.WordTrace]
  refine ⟨3031708404866927529944893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4042277873155903373259857 3031708404866927529944893)
  ·
    refine ⟨1136890651825097823729335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3031708404866927529944893 1136890651825097823729335)
    ·
      refine ⟨1705335977737646735594003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1136890651825097823729335 1705335977737646735594003)
      ·
        refine ⟨2558003966606470103391005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705335977737646735594003 2558003966606470103391005)
        ·
          refine ⟨959251487477426288771627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2558003966606470103391005 959251487477426288771627)
          ·
            refine ⟨1438877231216139433157441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959251487477426288771627 1438877231216139433157441)
            ·
              refine ⟨1079157923412104574868081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1438877231216139433157441 1079157923412104574868081)
              ·
                refine ⟨809368442559078431151061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1079157923412104574868081 809368442559078431151061)
                ·
                  refine ⟨18969572872478400730103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 809368442559078431151061 18969572872478400730103)
                  ·
                    rfl

theorem cell22_166244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_166244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166244 prefixEnd_166244 := by exact prefixLift 166244
  have htrace : WordTrace (prefixWord ++ tailWord_166244) baseStart_166244 baseEnd_166244 := by
    simpa [prefixWord, tailWord_166244, baseEnd_166244] using wordTrace_append hprefix tailTrace_166244
  have hstable : (prefixWord ++ tailWord_166244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166244).length < 2 ^ (prefixWord ++ tailWord_166244).sum := by decide
  have hdescent : baseEnd_166244 < baseStart_166244 := by decide
  rcases family_descends (prefixWord ++ tailWord_166244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166261 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 7]
def baseStart_166261 : Nat := 118140960795 + 166261 * 2 ^ 59
def prefixEnd_166261 : Nat := 4983230072969 + 3 ^ 40 * 166261 * 2
def baseEnd_166261 : Nat := 18971512688284274838419

theorem tailTrace_166261 : CollatzResearch.WordTrace tailWord_166261 prefixEnd_166261 18971512688284274838419 := by
  unfold tailWord_166261
  simp only [CollatzResearch.WordTrace]
  refine ⟨6064036850672266963258637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4042691233781511308839091 6064036850672266963258637)
  ·
    refine ⟨2274013819002100111221989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6064036850672266963258637 2274013819002100111221989)
    ·
      refine ⟨426377591062893770854123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2274013819002100111221989 426377591062893770854123)
      ·
        refine ⟨639566386594340656281185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426377591062893770854123 639566386594340656281185)
        ·
          refine ⟨479674789945755492210889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 639566386594340656281185 479674789945755492210889)
          ·
            refine ⟨359756092459316619158167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 479674789945755492210889 359756092459316619158167)
            ·
              refine ⟨539634138688974928737251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359756092459316619158167 539634138688974928737251)
              ·
                refine ⟨809451208033462393105877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 539634138688974928737251 809451208033462393105877)
                ·
                  refine ⟨18971512688284274838419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 809451208033462393105877 18971512688284274838419)
                  ·
                    rfl

theorem cell22_166261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_166261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166261 prefixEnd_166261 := by exact prefixLift 166261
  have htrace : WordTrace (prefixWord ++ tailWord_166261) baseStart_166261 baseEnd_166261 := by
    simpa [prefixWord, tailWord_166261, baseEnd_166261] using wordTrace_append hprefix tailTrace_166261
  have hstable : (prefixWord ++ tailWord_166261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166261).length < 2 ^ (prefixWord ++ tailWord_166261).sum := by decide
  have hdescent : baseEnd_166261 < baseStart_166261 := by decide
  rcases family_descends (prefixWord ++ tailWord_166261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166460 : List Nat := [2, 2, 2, 2, 3, 2, 2, 2, 1, 4]
def baseStart_166460 : Nat := 118140960795 + 166460 * 2 ^ 59
def prefixEnd_166460 : Nat := 4983230072969 + 3 ^ 40 * 166460 * 2
def baseEnd_166460 : Nat := 56982659831682638789647

theorem tailTrace_166460 : CollatzResearch.WordTrace tailWord_166460 prefixEnd_166460 56982659831682638789647 := by
  unfold tailWord_166460
  simp only [CollatzResearch.WordTrace]
  refine ⟨3035647488475661974876417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4047529984634215966501889 3035647488475661974876417)
  ·
    refine ⟨2276735616356746481157313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3035647488475661974876417 2276735616356746481157313)
    ·
      refine ⟨1707551712267559860867985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2276735616356746481157313 1707551712267559860867985)
      ·
        refine ⟨1280663784200669895650989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1707551712267559860867985 1280663784200669895650989)
        ·
          refine ⟨480248919075251210869121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1280663784200669895650989 480248919075251210869121)
          ·
            refine ⟨360186689306438408151841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480248919075251210869121 360186689306438408151841)
            ·
              refine ⟨270140016979828806113881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360186689306438408151841 270140016979828806113881)
              ·
                refine ⟨202605012734871604585411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270140016979828806113881 202605012734871604585411)
                ·
                  refine ⟨303907519102307406878117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202605012734871604585411 303907519102307406878117)
                  ·
                    refine ⟨56982659831682638789647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 303907519102307406878117 56982659831682638789647)
                    ·
                      rfl

theorem cell22_166460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_166460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166460 prefixEnd_166460 := by exact prefixLift 166460
  have htrace : WordTrace (prefixWord ++ tailWord_166460) baseStart_166460 baseEnd_166460 := by
    simpa [prefixWord, tailWord_166460, baseEnd_166460] using wordTrace_append hprefix tailTrace_166460
  have hstable : (prefixWord ++ tailWord_166460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166460).length < 2 ^ (prefixWord ++ tailWord_166460).sum := by decide
  have hdescent : baseEnd_166460 < baseStart_166460 := by decide
  rcases family_descends (prefixWord ++ tailWord_166460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166468 : List Nat := [2, 3, 5, 1, 1, 2, 1, 3, 1, 3]
def baseStart_166468 : Nat := 118140960795 + 166468 * 2 ^ 59
def prefixEnd_166468 : Nat := 4983230072969 + 3 ^ 40 * 166468 * 2
def baseEnd_166468 : Nat := 56985398395173284589623

theorem tailTrace_166468 : CollatzResearch.WordTrace tailWord_166468 prefixEnd_166468 56985398395173284589623 := by
  unfold tailWord_166468
  simp only [CollatzResearch.WordTrace]
  refine ⟨3035793380461170658022029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4047724507281560877362705 3035793380461170658022029)
  ·
    refine ⟨1138422517672938996758261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3035793380461170658022029 1138422517672938996758261)
    ·
      refine ⟨106727111031838030946087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1138422517672938996758261 106727111031838030946087)
      ·
        refine ⟨160090666547757046419131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106727111031838030946087 160090666547757046419131)
        ·
          refine ⟨240135999821635569628697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160090666547757046419131 240135999821635569628697)
          ·
            refine ⟨180101999866226677221523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240135999821635569628697 180101999866226677221523)
            ·
              refine ⟨270152999799340015832285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180101999866226677221523 270152999799340015832285)
              ·
                refine ⟨101307374924752505937107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270152999799340015832285 101307374924752505937107)
                ·
                  refine ⟨151961062387128758905661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101307374924752505937107 151961062387128758905661)
                  ·
                    refine ⟨56985398395173284589623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 151961062387128758905661 56985398395173284589623)
                    ·
                      rfl

theorem cell22_166468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_166468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166468 prefixEnd_166468 := by exact prefixLift 166468
  have htrace : WordTrace (prefixWord ++ tailWord_166468) baseStart_166468 baseEnd_166468 := by
    simpa [prefixWord, tailWord_166468, baseEnd_166468] using wordTrace_append hprefix tailTrace_166468
  have hstable : (prefixWord ++ tailWord_166468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166468).length < 2 ^ (prefixWord ++ tailWord_166468).sum := by decide
  have hdescent : baseEnd_166468 < baseStart_166468 := by decide
  rcases family_descends (prefixWord ++ tailWord_166468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166492 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 6]
def baseStart_166492 : Nat := 118140960795 + 166492 * 2 ^ 59
def prefixEnd_166492 : Nat := 4983230072969 + 3 ^ 40 * 166492 * 2
def baseEnd_166492 : Nat := 18997871361881740663183

theorem tailTrace_166492 : CollatzResearch.WordTrace tailWord_166492 prefixEnd_166492 18997871361881740663183 := by
  unfold tailWord_166492
  simp only [CollatzResearch.WordTrace]
  refine ⟨3036231056417696707458865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4048308075223595609945153 3036231056417696707458865)
  ·
    refine ⟨2277173292313272530594149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3036231056417696707458865 2277173292313272530594149)
    ·
      refine ⟨426969992308738599486403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2277173292313272530594149 426969992308738599486403)
      ·
        refine ⟨640454988463107899229605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426969992308738599486403 640454988463107899229605)
        ·
          refine ⟨120085310336832731105551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 640454988463107899229605 120085310336832731105551)
          ·
            refine ⟨180127965505249096658327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120085310336832731105551 180127965505249096658327)
            ·
              refine ⟨270191948257873644987491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180127965505249096658327 270191948257873644987491)
              ·
                refine ⟨405287922386810467481237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270191948257873644987491 405287922386810467481237)
                ·
                  refine ⟨18997871361881740663183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 405287922386810467481237 18997871361881740663183)
                  ·
                    rfl

theorem cell22_166492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_166492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166492 prefixEnd_166492 := by exact prefixLift 166492
  have htrace : WordTrace (prefixWord ++ tailWord_166492) baseStart_166492 baseEnd_166492 := by
    simpa [prefixWord, tailWord_166492, baseEnd_166492] using wordTrace_append hprefix tailTrace_166492
  have hstable : (prefixWord ++ tailWord_166492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166492).length < 2 ^ (prefixWord ++ tailWord_166492).sum := by decide
  have hdescent : baseEnd_166492 < baseStart_166492 := by decide
  rcases family_descends (prefixWord ++ tailWord_166492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166531 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 9]
def baseStart_166531 : Nat := 118140960795 + 166531 * 2 ^ 59
def prefixEnd_166531 : Nat := 4983230072969 + 3 ^ 40 * 166531 * 2
def baseEnd_166531 : Nat := 19002321527554040088143

theorem tailTrace_166531 : CollatzResearch.WordTrace tailWord_166531 prefixEnd_166531 19002321527554040088143 := by
  unfold tailWord_166531
  simp only [CollatzResearch.WordTrace]
  refine ⟨6073884559694103075587447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4049256373129402050391631 6073884559694103075587447)
  ·
    refine ⟨9110826839541154613381171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6073884559694103075587447 9110826839541154613381171)
    ·
      refine ⟨13666240259311731920071757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9110826839541154613381171 13666240259311731920071757)
      ·
        refine ⟨5124840097241899470026909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13666240259311731920071757 5124840097241899470026909)
        ·
          refine ⟨1921815036465712301260091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5124840097241899470026909 1921815036465712301260091)
          ·
            refine ⟨2882722554698568451890137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1921815036465712301260091 2882722554698568451890137)
            ·
              refine ⟨2162041916023926338917603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2882722554698568451890137 2162041916023926338917603)
              ·
                refine ⟨3243062874035889508376405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2162041916023926338917603 3243062874035889508376405)
                ·
                  refine ⟨19002321527554040088143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3243062874035889508376405 19002321527554040088143)
                  ·
                    rfl

theorem cell22_166531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 9].length) (baseStart_166531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166531 prefixEnd_166531 := by exact prefixLift 166531
  have htrace : WordTrace (prefixWord ++ tailWord_166531) baseStart_166531 baseEnd_166531 := by
    simpa [prefixWord, tailWord_166531, baseEnd_166531] using wordTrace_append hprefix tailTrace_166531
  have hstable : (prefixWord ++ tailWord_166531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166531).length < 2 ^ (prefixWord ++ tailWord_166531).sum := by decide
  have hdescent : baseEnd_166531 < baseStart_166531 := by decide
  rcases family_descends (prefixWord ++ tailWord_166531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166552 : List Nat := [2, 1, 2, 4, 1, 1, 3, 4, 1, 3]
def baseStart_166552 : Nat := 118140960795 + 166552 * 2 ^ 59
def prefixEnd_166552 : Nat := 4983230072969 + 3 ^ 40 * 166552 * 2
def baseEnd_166552 : Nat := 57014153311825065489365

theorem tailTrace_166552 : CollatzResearch.WordTrace tailWord_166552 prefixEnd_166552 57014153311825065489365 := by
  unfold tailWord_166552
  simp only [CollatzResearch.WordTrace]
  refine ⟨3037325246309011831050955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4049766995078682441401273 3037325246309011831050955)
  ·
    refine ⟨4555987869463517746576433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3037325246309011831050955 4555987869463517746576433)
    ·
      refine ⟨3416990902097638309932325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4555987869463517746576433 3416990902097638309932325)
      ·
        refine ⟨640685794143307183112311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3416990902097638309932325 640685794143307183112311)
        ·
          refine ⟨961028691214960774668467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640685794143307183112311 961028691214960774668467)
          ·
            refine ⟨1441543036822441162002701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961028691214960774668467 1441543036822441162002701)
            ·
              refine ⟨540578638808415435751013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1441543036822441162002701 540578638808415435751013)
              ·
                refine ⟨101358494776577894203315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 540578638808415435751013 101358494776577894203315)
                ·
                  refine ⟨152037742164866841304973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101358494776577894203315 152037742164866841304973)
                  ·
                    refine ⟨57014153311825065489365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 152037742164866841304973 57014153311825065489365)
                    ·
                      rfl

theorem cell22_166552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_166552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166552 prefixEnd_166552 := by exact prefixLift 166552
  have htrace : WordTrace (prefixWord ++ tailWord_166552) baseStart_166552 baseEnd_166552 := by
    simpa [prefixWord, tailWord_166552, baseEnd_166552] using wordTrace_append hprefix tailTrace_166552
  have hstable : (prefixWord ++ tailWord_166552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166552).length < 2 ^ (prefixWord ++ tailWord_166552).sum := by decide
  have hdescent : baseEnd_166552 < baseStart_166552 := by decide
  rcases family_descends (prefixWord ++ tailWord_166552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166623 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 1, 6]
def baseStart_166623 : Nat := 118140960795 + 166623 * 2 ^ 59
def prefixEnd_166623 : Nat := 4983230072969 + 3 ^ 40 * 166623 * 2
def baseEnd_166623 : Nat := 57038458062804546964147

theorem tailTrace_166623 : CollatzResearch.WordTrace tailWord_166623 prefixEnd_166623 57038458062804546964147 := by
  unfold tailWord_166623
  simp only [CollatzResearch.WordTrace]
  refine ⟨6077240075360802787936523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4051493383573868525291015 6077240075360802787936523)
  ·
    refine ⟨9115860113041204181904785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6077240075360802787936523 9115860113041204181904785)
    ·
      refine ⟨6836895084780903136428589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9115860113041204181904785 6836895084780903136428589)
      ·
        refine ⟨2563835656792838676160721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6836895084780903136428589 2563835656792838676160721)
        ·
          refine ⟨1922876742594629007120541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2563835656792838676160721 1922876742594629007120541)
          ·
            refine ⟨721078778472985877670203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1922876742594629007120541 721078778472985877670203)
            ·
              refine ⟨1081618167709478816505305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721078778472985877670203 1081618167709478816505305)
              ·
                refine ⟨811213625782109112378979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081618167709478816505305 811213625782109112378979)
                ·
                  refine ⟨1216820438673163668568469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 811213625782109112378979 1216820438673163668568469)
                  ·
                    refine ⟨57038458062804546964147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1216820438673163668568469 57038458062804546964147)
                    ·
                      rfl

theorem cell22_166623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_166623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166623 prefixEnd_166623 := by exact prefixLift 166623
  have htrace : WordTrace (prefixWord ++ tailWord_166623) baseStart_166623 baseEnd_166623 := by
    simpa [prefixWord, tailWord_166623, baseEnd_166623] using wordTrace_append hprefix tailTrace_166623
  have hstable : (prefixWord ++ tailWord_166623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166623).length < 2 ^ (prefixWord ++ tailWord_166623).sum := by decide
  have hdescent : baseEnd_166623 < baseStart_166623 := by decide
  rcases family_descends (prefixWord ++ tailWord_166623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166625 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 1, 5]
def baseStart_166625 : Nat := 118140960795 + 166625 * 2 ^ 59
def prefixEnd_166625 : Nat := 4983230072969 + 3 ^ 40 * 166625 * 2
def baseEnd_166625 : Nat := 57039142703677208414141

theorem tailTrace_166625 : CollatzResearch.WordTrace tailWord_166625 prefixEnd_166625 57039142703677208414141 := by
  unfold tailWord_166625
  simp only [CollatzResearch.WordTrace]
  refine ⟨6077313021353557129509329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4051542014235704753006219 6077313021353557129509329)
  ·
    refine ⟨4557984766015167847131997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6077313021353557129509329 4557984766015167847131997)
    ·
      refine ⟨1709244287255687942674499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4557984766015167847131997 1709244287255687942674499)
      ·
        refine ⟨2563866430883531914011749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709244287255687942674499 2563866430883531914011749)
        ·
          refine ⟨480724955790662233877203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2563866430883531914011749 480724955790662233877203)
          ·
            refine ⟨721087433685993350815805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480724955790662233877203 721087433685993350815805)
            ·
              refine ⟨270407787632247506555927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 721087433685993350815805 270407787632247506555927)
              ·
                refine ⟨405611681448371259833891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270407787632247506555927 405611681448371259833891)
                ·
                  refine ⟨608417522172556889750837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405611681448371259833891 608417522172556889750837)
                  ·
                    refine ⟨57039142703677208414141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 608417522172556889750837 57039142703677208414141)
                    ·
                      rfl

theorem cell22_166625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_166625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166625 prefixEnd_166625 := by exact prefixLift 166625
  have htrace : WordTrace (prefixWord ++ tailWord_166625) baseStart_166625 baseEnd_166625 := by
    simpa [prefixWord, tailWord_166625, baseEnd_166625] using wordTrace_append hprefix tailTrace_166625
  have hstable : (prefixWord ++ tailWord_166625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166625).length < 2 ^ (prefixWord ++ tailWord_166625).sum := by decide
  have hdescent : baseEnd_166625 < baseStart_166625 := by decide
  rcases family_descends (prefixWord ++ tailWord_166625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166668 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 2, 6]
def baseStart_166668 : Nat := 118140960795 + 166668 * 2 ^ 59
def prefixEnd_166668 : Nat := 4983230072969 + 3 ^ 40 * 166668 * 2
def baseEnd_166668 : Nat := 57053862482439429589009

theorem tailTrace_166668 : CollatzResearch.WordTrace tailWord_166668 prefixEnd_166668 57053862482439429589009 := by
  unfold tailWord_166668
  simp only [CollatzResearch.WordTrace]
  refine ⟨3039440680098887736662329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4052587573465183648883105 3039440680098887736662329)
  ·
    refine ⟨2279580510074165802496747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3039440680098887736662329 2279580510074165802496747)
    ·
      refine ⟨3419370765111248703745121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2279580510074165802496747 3419370765111248703745121)
      ·
        refine ⟨2564528073833436527808841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3419370765111248703745121 2564528073833436527808841)
        ·
          refine ⟨1923396055375077395856631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2564528073833436527808841 1923396055375077395856631)
          ·
            refine ⟨2885094083062616093784947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923396055375077395856631 2885094083062616093784947)
            ·
              refine ⟨4327641124593924140677421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885094083062616093784947 4327641124593924140677421)
              ·
                refine ⟨1622865421722721552754033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4327641124593924140677421 1622865421722721552754033)
                ·
                  refine ⟨1217149066292041164565525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1622865421722721552754033 1217149066292041164565525)
                  ·
                    refine ⟨57053862482439429589009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1217149066292041164565525 57053862482439429589009)
                    ·
                      rfl

theorem cell22_166668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_166668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166668 prefixEnd_166668 := by exact prefixLift 166668
  have htrace : WordTrace (prefixWord ++ tailWord_166668) baseStart_166668 baseEnd_166668 := by
    simpa [prefixWord, tailWord_166668, baseEnd_166668] using wordTrace_append hprefix tailTrace_166668
  have hstable : (prefixWord ++ tailWord_166668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166668).length < 2 ^ (prefixWord ++ tailWord_166668).sum := by decide
  have hdescent : baseEnd_166668 < baseStart_166668 := by decide
  rcases family_descends (prefixWord ++ tailWord_166668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166745 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 6]
def baseStart_166745 : Nat := 118140960795 + 166745 * 2 ^ 59
def prefixEnd_166745 : Nat := 4983230072969 + 3 ^ 40 * 166745 * 2
def baseEnd_166745 : Nat := 19026740385345631804591

theorem tailTrace_166745 : CollatzResearch.WordTrace tailWord_166745 prefixEnd_166745 19026740385345631804591 := by
  unfold tailWord_166745
  simp only [CollatzResearch.WordTrace]
  refine ⟨6081689780918817623877689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4054459853945878415918459 6081689780918817623877689)
  ·
    refine ⟨4561267335689113217908267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6081689780918817623877689 4561267335689113217908267)
    ·
      refine ⟨6841901003533669826862401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4561267335689113217908267 6841901003533669826862401)
      ·
        refine ⟨5131425752650252370146801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6841901003533669826862401 5131425752650252370146801)
        ·
          refine ⟨3848569314487689277610101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5131425752650252370146801 3848569314487689277610101)
          ·
            refine ⟨360803373233220869775947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3848569314487689277610101 360803373233220869775947)
            ·
              refine ⟨541205059849831304663921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360803373233220869775947 541205059849831304663921)
              ·
                refine ⟨405903794887373478497941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541205059849831304663921 405903794887373478497941)
                ·
                  refine ⟨19026740385345631804591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 405903794887373478497941 19026740385345631804591)
                  ·
                    rfl

theorem cell22_166745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 6].length) (baseStart_166745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166745 prefixEnd_166745 := by exact prefixLift 166745
  have htrace : WordTrace (prefixWord ++ tailWord_166745) baseStart_166745 baseEnd_166745 := by
    simpa [prefixWord, tailWord_166745, baseEnd_166745] using wordTrace_append hprefix tailTrace_166745
  have hstable : (prefixWord ++ tailWord_166745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166745).length < 2 ^ (prefixWord ++ tailWord_166745).sum := by decide
  have hdescent : baseEnd_166745 < baseStart_166745 := by decide
  rcases family_descends (prefixWord ++ tailWord_166745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166775 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 2, 4]
def baseStart_166775 : Nat := 118140960795 + 166775 * 2 ^ 59
def prefixEnd_166775 : Nat := 4983230072969 + 3 ^ 40 * 166775 * 2
def baseEnd_166775 : Nat := 57090490769126817163681

theorem tailTrace_166775 : CollatzResearch.WordTrace tailWord_166775 prefixEnd_166775 57090490769126817163681 := by
  unfold tailWord_166775
  simp only [CollatzResearch.WordTrace]
  refine ⟨6082783970810132747469779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4055189313873421831646519 6082783970810132747469779)
  ·
    refine ⟨9124175956215199121204669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6082783970810132747469779 9124175956215199121204669)
    ·
      refine ⟨3421565983580699670451751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9124175956215199121204669 3421565983580699670451751)
      ·
        refine ⟨5132348975371049505677627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3421565983580699670451751 5132348975371049505677627)
        ·
          refine ⟨7698523463056574258516441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5132348975371049505677627 7698523463056574258516441)
          ·
            refine ⟨5773892597292430693887331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7698523463056574258516441 5773892597292430693887331)
            ·
              refine ⟨8660838895938646040830997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5773892597292430693887331 8660838895938646040830997)
              ·
                refine ⟨405976823247124033163953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8660838895938646040830997 405976823247124033163953)
                ·
                  refine ⟨304482617435343024872965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405976823247124033163953 304482617435343024872965)
                  ·
                    refine ⟨57090490769126817163681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 304482617435343024872965 57090490769126817163681)
                    ·
                      rfl

theorem cell22_166775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_166775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166775 prefixEnd_166775 := by exact prefixLift 166775
  have htrace : WordTrace (prefixWord ++ tailWord_166775) baseStart_166775 baseEnd_166775 := by
    simpa [prefixWord, tailWord_166775, baseEnd_166775] using wordTrace_append hprefix tailTrace_166775
  have hstable : (prefixWord ++ tailWord_166775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166775).length < 2 ^ (prefixWord ++ tailWord_166775).sum := by decide
  have hdescent : baseEnd_166775 < baseStart_166775 := by decide
  rcases family_descends (prefixWord ++ tailWord_166775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166777 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 4, 3]
def baseStart_166777 : Nat := 118140960795 + 166777 * 2 ^ 59
def prefixEnd_166777 : Nat := 4983230072969 + 3 ^ 40 * 166777 * 2
def baseEnd_166777 : Nat := 57091175409999478613675

theorem tailTrace_166777 : CollatzResearch.WordTrace tailWord_166777 prefixEnd_166777 57091175409999478613675 := by
  unfold tailWord_166777
  simp only [CollatzResearch.WordTrace]
  refine ⟨6082856916802887089042585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4055237944535258059361723 6082856916802887089042585)
  ·
    refine ⟨4562142687602165316781939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6082856916802887089042585 4562142687602165316781939)
    ·
      refine ⟨6843214031403247975172909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4562142687602165316781939 6843214031403247975172909)
      ·
        refine ⟨2566205261776217990689841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6843214031403247975172909 2566205261776217990689841)
        ·
          refine ⟨1924653946332163493017381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2566205261776217990689841 1924653946332163493017381)
          ·
            refine ⟨360872614937280654940759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1924653946332163493017381 360872614937280654940759)
            ·
              refine ⟨541308922405920982411139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360872614937280654940759 541308922405920982411139)
              ·
                refine ⟨811963383608881473616709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541308922405920982411139 811963383608881473616709)
                ·
                  refine ⟨152243134426665276303133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 811963383608881473616709 152243134426665276303133)
                  ·
                    refine ⟨57091175409999478613675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 152243134426665276303133 57091175409999478613675)
                    ·
                      rfl

theorem cell22_166777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 3].length) (baseStart_166777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166777 prefixEnd_166777 := by exact prefixLift 166777
  have htrace : WordTrace (prefixWord ++ tailWord_166777) baseStart_166777 baseEnd_166777 := by
    simpa [prefixWord, tailWord_166777, baseEnd_166777] using wordTrace_append hprefix tailTrace_166777
  have hstable : (prefixWord ++ tailWord_166777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166777).length < 2 ^ (prefixWord ++ tailWord_166777).sum := by decide
  have hdescent : baseEnd_166777 < baseStart_166777 := by decide
  rcases family_descends (prefixWord ++ tailWord_166777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166794 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 1, 5]
def baseStart_166794 : Nat := 118140960795 + 166794 * 2 ^ 59
def prefixEnd_166794 : Nat := 4983230072969 + 3 ^ 40 * 166794 * 2
def baseEnd_166794 : Nat := 57096994857417100938623

theorem tailTrace_166794 : CollatzResearch.WordTrace tailWord_166794 prefixEnd_166794 57096994857417100938623 := by
  unfold tailWord_166794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1520869239435324748102859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4055651305160865994940957 1520869239435324748102859)
  ·
    refine ⟨2281303859152987122154289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1520869239435324748102859 2281303859152987122154289)
    ·
      refine ⟨1710977894364740341615717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2281303859152987122154289 1710977894364740341615717)
      ·
        refine ⟨320808355193388814052947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1710977894364740341615717 320808355193388814052947)
        ·
          refine ⟨481212532790083221079421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320808355193388814052947 481212532790083221079421)
          ·
            refine ⟨180454699796281207904783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 481212532790083221079421 180454699796281207904783)
            ·
              refine ⟨270682049694421811857175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180454699796281207904783 270682049694421811857175)
              ·
                refine ⟨406023074541632717785763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270682049694421811857175 406023074541632717785763)
                ·
                  refine ⟨609034611812449076678645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406023074541632717785763 609034611812449076678645)
                  ·
                    refine ⟨57096994857417100938623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 609034611812449076678645 57096994857417100938623)
                    ·
                      rfl

theorem cell22_166794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_166794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166794 prefixEnd_166794 := by exact prefixLift 166794
  have htrace : WordTrace (prefixWord ++ tailWord_166794) baseStart_166794 baseEnd_166794 := by
    simpa [prefixWord, tailWord_166794, baseEnd_166794] using wordTrace_append hprefix tailTrace_166794
  have hstable : (prefixWord ++ tailWord_166794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166794).length < 2 ^ (prefixWord ++ tailWord_166794).sum := by decide
  have hdescent : baseEnd_166794 < baseStart_166794 := by decide
  rcases family_descends (prefixWord ++ tailWord_166794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166839 : List Nat := [1, 1, 3, 1, 3, 1, 2, 6, 1, 3]
def baseStart_166839 : Nat := 118140960795 + 166839 * 2 ^ 59
def prefixEnd_166839 : Nat := 4983230072969 + 3 ^ 40 * 166839 * 2
def baseEnd_166839 : Nat := 57112399277051983563485

theorem tailTrace_166839 : CollatzResearch.WordTrace tailWord_166839 prefixEnd_166839 57112399277051983563485 := by
  unfold tailWord_166839
  simp only [CollatzResearch.WordTrace]
  refine ⟨6085118242578271677799571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4056745495052181118533047 6085118242578271677799571)
  ·
    refine ⟨9127677363867407516699357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6085118242578271677799571 9127677363867407516699357)
    ·
      refine ⟨3422879011450277818762259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9127677363867407516699357 3422879011450277818762259)
      ·
        refine ⟨5134318517175416728143389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3422879011450277818762259 5134318517175416728143389)
        ·
          refine ⟨1925369443940781273053771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5134318517175416728143389 1925369443940781273053771)
          ·
            refine ⟨2888054165911171909580657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1925369443940781273053771 2888054165911171909580657)
            ·
              refine ⟨2166040624433378932185493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2888054165911171909580657 2166040624433378932185493)
              ·
                refine ⟨101533154270314637446195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2166040624433378932185493 101533154270314637446195)
                ·
                  refine ⟨152299731405471956169293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101533154270314637446195 152299731405471956169293)
                  ·
                    refine ⟨57112399277051983563485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 152299731405471956169293 57112399277051983563485)
                    ·
                      rfl

theorem cell22_166839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_166839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166839 prefixEnd_166839 := by exact prefixLift 166839
  have htrace : WordTrace (prefixWord ++ tailWord_166839) baseStart_166839 baseEnd_166839 := by
    simpa [prefixWord, tailWord_166839, baseEnd_166839] using wordTrace_append hprefix tailTrace_166839
  have hstable : (prefixWord ++ tailWord_166839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166839).length < 2 ^ (prefixWord ++ tailWord_166839).sum := by decide
  have hdescent : baseEnd_166839 < baseStart_166839 := by decide
  rcases family_descends (prefixWord ++ tailWord_166839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166901 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 2, 5]
def baseStart_166901 : Nat := 118140960795 + 166901 * 2 ^ 59
def prefixEnd_166901 : Nat := 4983230072969 + 3 ^ 40 * 166901 * 2
def baseEnd_166901 : Nat := 57133623144104488513295

theorem tailTrace_166901 : CollatzResearch.WordTrace tailWord_166901 prefixEnd_166901 57133623144104488513295 := by
  unfold tailWord_166901
  simp only [CollatzResearch.WordTrace]
  refine ⟨6087379568353656266556557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4058253045569104177704371 6087379568353656266556557)
  ·
    refine ⟨2282767338132621099958709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6087379568353656266556557 2282767338132621099958709)
    ·
      refine ⟨214009437949933228121129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2282767338132621099958709 214009437949933228121129)
      ·
        refine ⟨160507078462449921090847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214009437949933228121129 160507078462449921090847)
        ·
          refine ⟨240760617693674881636271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160507078462449921090847 240760617693674881636271)
          ·
            refine ⟨361140926540512322454407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240760617693674881636271 361140926540512322454407)
            ·
              refine ⟨541711389810768483681611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361140926540512322454407 541711389810768483681611)
              ·
                refine ⟨812567084716152725522417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541711389810768483681611 812567084716152725522417)
                ·
                  refine ⟨609425313537114544141813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 812567084716152725522417 609425313537114544141813)
                  ·
                    refine ⟨57133623144104488513295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 609425313537114544141813 57133623144104488513295)
                    ·
                      rfl

theorem cell22_166901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_166901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166901 prefixEnd_166901 := by exact prefixLift 166901
  have htrace : WordTrace (prefixWord ++ tailWord_166901) baseStart_166901 baseEnd_166901 := by
    simpa [prefixWord, tailWord_166901, baseEnd_166901] using wordTrace_append hprefix tailTrace_166901
  have hstable : (prefixWord ++ tailWord_166901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166901).length < 2 ^ (prefixWord ++ tailWord_166901).sum := by decide
  have hdescent : baseEnd_166901 < baseStart_166901 := by decide
  rcases family_descends (prefixWord ++ tailWord_166901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166946 : List Nat := [3, 3, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_166946 : Nat := 118140960795 + 166946 * 2 ^ 59
def prefixEnd_166946 : Nat := 4983230072969 + 3 ^ 40 * 166946 * 2
def baseEnd_166946 : Nat := 57149027563739371138157

theorem tailTrace_166946 : CollatzResearch.WordTrace tailWord_166946 prefixEnd_166946 57149027563739371138157 := by
  unfold tailWord_166946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1522255213297657237986173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4059347235460419301296461 1522255213297657237986173)
  ·
    refine ⟨570845704986621464244815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1522255213297657237986173 570845704986621464244815)
    ·
      refine ⟨856268557479932196367223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 570845704986621464244815 856268557479932196367223)
      ·
        refine ⟨1284402836219898294550835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 856268557479932196367223 1284402836219898294550835)
        ·
          refine ⟨1926604254329847441826253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284402836219898294550835 1926604254329847441826253)
          ·
            refine ⟨722476595373692790684845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1926604254329847441826253 722476595373692790684845)
            ·
              refine ⟨270928723265134796506817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 722476595373692790684845 270928723265134796506817)
              ·
                refine ⟨203196542448851097380113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270928723265134796506817 203196542448851097380113)
                ·
                  refine ⟨152397406836638323035085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203196542448851097380113 152397406836638323035085)
                  ·
                    refine ⟨57149027563739371138157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 152397406836638323035085 57149027563739371138157)
                    ·
                      rfl

theorem cell22_166946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_166946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_166946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_166946 prefixEnd_166946 := by exact prefixLift 166946
  have htrace : WordTrace (prefixWord ++ tailWord_166946) baseStart_166946 baseEnd_166946 := by
    simpa [prefixWord, tailWord_166946, baseEnd_166946] using wordTrace_append hprefix tailTrace_166946
  have hstable : (prefixWord ++ tailWord_166946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166946).length < 2 ^ (prefixWord ++ tailWord_166946).sum := by decide
  have hdescent : baseEnd_166946 < baseStart_166946 := by decide
  rcases family_descends (prefixWord ++ tailWord_166946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167002 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 2, 5]
def baseStart_167002 : Nat := 118140960795 + 167002 * 2 ^ 59
def prefixEnd_167002 : Nat := 4983230072969 + 3 ^ 40 * 167002 * 2
def baseEnd_167002 : Nat := 57168197508173891737985

theorem tailTrace_167002 : CollatzResearch.WordTrace tailWord_167002 prefixEnd_167002 57168197508173891737985 := by
  unfold tailWord_167002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1522765835246937628995815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4060708893991833677322173 1522765835246937628995815)
  ·
    refine ⟨2284148752870406443493723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1522765835246937628995815 2284148752870406443493723)
    ·
      refine ⟨3426223129305609665240585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2284148752870406443493723 3426223129305609665240585)
      ·
        refine ⟨2569667346979207248930439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3426223129305609665240585 2569667346979207248930439)
        ·
          refine ⟨3854501020468810873395659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2569667346979207248930439 3854501020468810873395659)
          ·
            refine ⟨5781751530703216310093489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854501020468810873395659 5781751530703216310093489)
            ·
              refine ⟨4336313648027412232570117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5781751530703216310093489 4336313648027412232570117)
              ·
                refine ⟨813058809005139793606897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4336313648027412232570117 813058809005139793606897)
                ·
                  refine ⟨609794106753854845205173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 813058809005139793606897 609794106753854845205173)
                  ·
                    refine ⟨57168197508173891737985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 609794106753854845205173 57168197508173891737985)
                    ·
                      rfl

theorem cell22_167002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_167002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167002 prefixEnd_167002 := by exact prefixLift 167002
  have htrace : WordTrace (prefixWord ++ tailWord_167002) baseStart_167002 baseEnd_167002 := by
    simpa [prefixWord, tailWord_167002, baseEnd_167002] using wordTrace_append hprefix tailTrace_167002
  have hstable : (prefixWord ++ tailWord_167002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167002).length < 2 ^ (prefixWord ++ tailWord_167002).sum := by decide
  have hdescent : baseEnd_167002 < baseStart_167002 := by decide
  rcases family_descends (prefixWord ++ tailWord_167002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167004 : List Nat := [2, 2, 4, 1, 1, 1, 2, 4, 5]
def baseStart_167004 : Nat := 118140960795 + 167004 * 2 ^ 59
def prefixEnd_167004 : Nat := 4983230072969 + 3 ^ 40 * 167004 * 2
def baseEnd_167004 : Nat := 19056294049682184395993

theorem tailTrace_167004 : CollatzResearch.WordTrace tailWord_167004 prefixEnd_167004 19056294049682184395993 := by
  unfold tailWord_167004
  simp only [CollatzResearch.WordTrace]
  refine ⟨3045568143490252428778033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4060757524653669905037377 3045568143490252428778033)
  ·
    refine ⟨2284176107617689321583525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3045568143490252428778033 2284176107617689321583525)
    ·
      refine ⟨428283020178316747796911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2284176107617689321583525 428283020178316747796911)
      ·
        refine ⟨642424530267475121695367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428283020178316747796911 642424530267475121695367)
        ·
          refine ⟨963636795401212682543051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642424530267475121695367 963636795401212682543051)
          ·
            refine ⟨1445455193101819023814577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963636795401212682543051 1445455193101819023814577)
            ·
              refine ⟨1084091394826364267860933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1445455193101819023814577 1084091394826364267860933)
              ·
                refine ⟨203267136529943300223925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1084091394826364267860933 203267136529943300223925)
                ·
                  refine ⟨19056294049682184395993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 203267136529943300223925 19056294049682184395993)
                  ·
                    rfl

theorem cell22_167004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_167004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167004 prefixEnd_167004 := by exact prefixLift 167004
  have htrace : WordTrace (prefixWord ++ tailWord_167004) baseStart_167004 baseEnd_167004 := by
    simpa [prefixWord, tailWord_167004, baseEnd_167004] using wordTrace_append hprefix tailTrace_167004
  have hstable : (prefixWord ++ tailWord_167004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167004).length < 2 ^ (prefixWord ++ tailWord_167004).sum := by decide
  have hdescent : baseEnd_167004 < baseStart_167004 := by decide
  rcases family_descends (prefixWord ++ tailWord_167004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167008 : List Nat := [2, 1, 1, 3, 2, 2, 5, 2, 1, 3]
def baseStart_167008 : Nat := 118140960795 + 167008 * 2 ^ 59
def prefixEnd_167008 : Nat := 4983230072969 + 3 ^ 40 * 167008 * 2
def baseEnd_167008 : Nat := 57170251430791876087967

theorem tailTrace_167008 : CollatzResearch.WordTrace tailWord_167008 prefixEnd_167008 57170251430791876087967 := by
  unfold tailWord_167008
  simp only [CollatzResearch.WordTrace]
  refine ⟨3045641089483006770350839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4060854785977342360467785 3045641089483006770350839)
  ·
    refine ⟨4568461634224510155526259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3045641089483006770350839 4568461634224510155526259)
    ·
      refine ⟨6852692451336765233289389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4568461634224510155526259 6852692451336765233289389)
      ·
        refine ⟨2569759669251286962483521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6852692451336765233289389 2569759669251286962483521)
        ·
          refine ⟨1927319751938465221862641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2569759669251286962483521 1927319751938465221862641)
          ·
            refine ⟨1445489813953848916396981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1927319751938465221862641 1445489813953848916396981)
            ·
              refine ⟨135514670058173335912217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1445489813953848916396981 135514670058173335912217)
              ·
                refine ⟨101636002543630001934163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135514670058173335912217 101636002543630001934163)
                ·
                  refine ⟨152454003815445002901245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101636002543630001934163 152454003815445002901245)
                  ·
                    refine ⟨57170251430791876087967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 152454003815445002901245 57170251430791876087967)
                    ·
                      rfl

theorem cell22_167008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 1, 3].length) (baseStart_167008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167008 prefixEnd_167008 := by exact prefixLift 167008
  have htrace : WordTrace (prefixWord ++ tailWord_167008) baseStart_167008 baseEnd_167008 := by
    simpa [prefixWord, tailWord_167008, baseEnd_167008] using wordTrace_append hprefix tailTrace_167008
  have hstable : (prefixWord ++ tailWord_167008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167008).length < 2 ^ (prefixWord ++ tailWord_167008).sum := by decide
  have hdescent : baseEnd_167008 < baseStart_167008 := by decide
  rcases family_descends (prefixWord ++ tailWord_167008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167021 : List Nat := [1, 5, 1, 1, 2, 2, 4, 1, 5]
def baseStart_167021 : Nat := 118140960795 + 167021 * 2 ^ 59
def prefixEnd_167021 : Nat := 4983230072969 + 3 ^ 40 * 167021 * 2
def baseEnd_167021 : Nat := 19058233865488058504309

theorem tailTrace_167021 : CollatzResearch.WordTrace tailWord_167021 prefixEnd_167021 19058233865488058504309 := by
  unfold tailWord_167021
  simp only [CollatzResearch.WordTrace]
  refine ⟨6091756327918916760924917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4061170885279277840616611 6091756327918916760924917)
  ·
    refine ⟨571102155742398446336711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6091756327918916760924917 571102155742398446336711)
    ·
      refine ⟨856653233613597669505067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 571102155742398446336711 856653233613597669505067)
      ·
        refine ⟨1284979850420396504257601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 856653233613597669505067 1284979850420396504257601)
        ·
          refine ⟨963734887815297378193201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1284979850420396504257601 963734887815297378193201)
          ·
            refine ⟨722801165861473033644901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 963734887815297378193201 722801165861473033644901)
            ·
              refine ⟨135525218599026193808419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 722801165861473033644901 135525218599026193808419)
              ·
                refine ⟨203287827898539290712629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135525218599026193808419 203287827898539290712629)
                ·
                  refine ⟨19058233865488058504309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 203287827898539290712629 19058233865488058504309)
                  ·
                    rfl

theorem cell22_167021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_167021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167021 prefixEnd_167021 := by exact prefixLift 167021
  have htrace : WordTrace (prefixWord ++ tailWord_167021) baseStart_167021 baseEnd_167021 := by
    simpa [prefixWord, tailWord_167021, baseEnd_167021] using wordTrace_append hprefix tailTrace_167021
  have hstable : (prefixWord ++ tailWord_167021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167021).length < 2 ^ (prefixWord ++ tailWord_167021).sum := by decide
  have hdescent : baseEnd_167021 < baseStart_167021 := by decide
  rcases family_descends (prefixWord ++ tailWord_167021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167032 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 6]
def baseStart_167032 : Nat := 118140960795 + 167032 * 2 ^ 59
def prefixEnd_167032 : Nat := 4983230072969 + 3 ^ 40 * 167032 * 2
def baseEnd_167032 : Nat := 19059489040421271162631

theorem tailTrace_167032 : CollatzResearch.WordTrace tailWord_167032 prefixEnd_167032 19059489040421271162631 := by
  unfold tailWord_167032
  simp only [CollatzResearch.WordTrace]
  refine ⟨3046078765439532819787675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4061438353919377093050233 3046078765439532819787675)
  ·
    refine ⟨4569118148159299229681513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3046078765439532819787675 4569118148159299229681513)
    ·
      refine ⟨3426838611119474422261135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4569118148159299229681513 3426838611119474422261135)
      ·
        refine ⟨5140257916679211633391703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3426838611119474422261135 5140257916679211633391703)
        ·
          refine ⟨7710386875018817450087555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5140257916679211633391703 7710386875018817450087555)
          ·
            refine ⟨11565580312528226175131333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7710386875018817450087555 11565580312528226175131333)
            ·
              refine ⟨2168546308599042407837125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11565580312528226175131333 2168546308599042407837125)
              ·
                refine ⟨406602432862320451469461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2168546308599042407837125 406602432862320451469461)
                ·
                  refine ⟨19059489040421271162631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 406602432862320451469461 19059489040421271162631)
                  ·
                    rfl

theorem cell22_167032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 6].length) (baseStart_167032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167032 prefixEnd_167032 := by exact prefixLift 167032
  have htrace : WordTrace (prefixWord ++ tailWord_167032) baseStart_167032 baseEnd_167032 := by
    simpa [prefixWord, tailWord_167032, baseEnd_167032] using wordTrace_append hprefix tailTrace_167032
  have hstable : (prefixWord ++ tailWord_167032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167032).length < 2 ^ (prefixWord ++ tailWord_167032).sum := by decide
  have hdescent : baseEnd_167032 < baseStart_167032 := by decide
  rcases family_descends (prefixWord ++ tailWord_167032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167107 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 1, 8]
def baseStart_167107 : Nat := 118140960795 + 167107 * 2 ^ 59
def prefixEnd_167107 : Nat := 4983230072969 + 3 ^ 40 * 167107 * 2
def baseEnd_167107 : Nat := 57204141153988617862663

theorem tailTrace_167107 : CollatzResearch.WordTrace tailWord_167107 prefixEnd_167107 57204141153988617862663 := by
  unfold tailWord_167107
  simp only [CollatzResearch.WordTrace]
  refine ⟨6094893005607353448555575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4063262003738235632370383 6094893005607353448555575)
  ·
    refine ⟨9142339508411030172833363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6094893005607353448555575 9142339508411030172833363)
    ·
      refine ⟨13713509262616545259250045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9142339508411030172833363 13713509262616545259250045)
      ·
        refine ⟨5142565973481204472218767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13713509262616545259250045 5142565973481204472218767)
        ·
          refine ⟨7713848960221806708328151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5142565973481204472218767 7713848960221806708328151)
          ·
            refine ⟨11570773440332710062492227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7713848960221806708328151 11570773440332710062492227)
            ·
              refine ⟨17356160160499065093738341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11570773440332710062492227 17356160160499065093738341)
              ·
                refine ⟨3254280030093574705075939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17356160160499065093738341 3254280030093574705075939)
                ·
                  refine ⟨4881420045140362057613909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254280030093574705075939 4881420045140362057613909)
                  ·
                    refine ⟨57204141153988617862663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4881420045140362057613909 57204141153988617862663)
                    ·
                      rfl

theorem cell22_167107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 8].length) (baseStart_167107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167107 prefixEnd_167107 := by exact prefixLift 167107
  have htrace : WordTrace (prefixWord ++ tailWord_167107) baseStart_167107 baseEnd_167107 := by
    simpa [prefixWord, tailWord_167107, baseEnd_167107] using wordTrace_append hprefix tailTrace_167107
  have hstable : (prefixWord ++ tailWord_167107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167107).length < 2 ^ (prefixWord ++ tailWord_167107).sum := by decide
  have hdescent : baseEnd_167107 < baseStart_167107 := by decide
  rcases family_descends (prefixWord ++ tailWord_167107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167109 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 7, 3]
def baseStart_167109 : Nat := 118140960795 + 167109 * 2 ^ 59
def prefixEnd_167109 : Nat := 4983230072969 + 3 ^ 40 * 167109 * 2
def baseEnd_167109 : Nat := 57204825794861279312657

theorem tailTrace_167109 : CollatzResearch.WordTrace tailWord_167109 prefixEnd_167109 57204825794861279312657 := by
  unfold tailWord_167109
  simp only [CollatzResearch.WordTrace]
  refine ⟨6094965951600107790128381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4063310634400071860085587 6094965951600107790128381)
  ·
    refine ⟨2285612231850040421298143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6094965951600107790128381 2285612231850040421298143)
    ·
      refine ⟨3428418347775060631947215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2285612231850040421298143 3428418347775060631947215)
      ·
        refine ⟨5142627521662590947920823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3428418347775060631947215 5142627521662590947920823)
        ·
          refine ⟨7713941282493886421881235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5142627521662590947920823 7713941282493886421881235)
          ·
            refine ⟨11570911923740829632821853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7713941282493886421881235 11570911923740829632821853)
            ·
              refine ⟨4339091971402811112308195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11570911923740829632821853 4339091971402811112308195)
              ·
                refine ⟨6508637957104216668462293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4339091971402811112308195 6508637957104216668462293)
                ·
                  refine ⟨152546202119630078167085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6508637957104216668462293 152546202119630078167085)
                  ·
                    refine ⟨57204825794861279312657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 152546202119630078167085 57204825794861279312657)
                    ·
                      rfl

theorem cell22_167109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_167109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167109 prefixEnd_167109 := by exact prefixLift 167109
  have htrace : WordTrace (prefixWord ++ tailWord_167109) baseStart_167109 baseEnd_167109 := by
    simpa [prefixWord, tailWord_167109, baseEnd_167109] using wordTrace_append hprefix tailTrace_167109
  have hstable : (prefixWord ++ tailWord_167109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167109).length < 2 ^ (prefixWord ++ tailWord_167109).sum := by decide
  have hdescent : baseEnd_167109 < baseStart_167109 := by decide
  rcases family_descends (prefixWord ++ tailWord_167109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167203 : List Nat := [1, 1, 1, 4, 2, 5, 1, 2, 1, 4]
def baseStart_167203 : Nat := 118140960795 + 167203 * 2 ^ 59
def prefixEnd_167203 : Nat := 4983230072969 + 3 ^ 40 * 167203 * 2
def baseEnd_167203 : Nat := 57237003915876367462369

theorem tailTrace_167203 : CollatzResearch.WordTrace tailWord_167203 prefixEnd_167203 57237003915876367462369 := by
  unfold tailWord_167203
  simp only [CollatzResearch.WordTrace]
  refine ⟨6098394413259561844050263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4065596275506374562700175 6098394413259561844050263)
  ·
    refine ⟨9147591619889342766075395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6098394413259561844050263 9147591619889342766075395)
    ·
      refine ⟨13721387429834014149113093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9147591619889342766075395 13721387429834014149113093)
      ·
        refine ⟨2572760143093877652958705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13721387429834014149113093 2572760143093877652958705)
        ·
          refine ⟨1929570107320408239719029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2572760143093877652958705 1929570107320408239719029)
          ·
            refine ⟨180897197561288272473659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1929570107320408239719029 180897197561288272473659)
            ·
              refine ⟨271345796341932408710489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180897197561288272473659 271345796341932408710489)
              ·
                refine ⟨203509347256449306532867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271345796341932408710489 203509347256449306532867)
                ·
                  refine ⟨305264020884673959799301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203509347256449306532867 305264020884673959799301)
                  ·
                    refine ⟨57237003915876367462369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 305264020884673959799301 57237003915876367462369)
                    ·
                      rfl

theorem cell22_167203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 4].length) (baseStart_167203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167203 prefixEnd_167203 := by exact prefixLift 167203
  have htrace : WordTrace (prefixWord ++ tailWord_167203) baseStart_167203 baseEnd_167203 := by
    simpa [prefixWord, tailWord_167203, baseEnd_167203] using wordTrace_append hprefix tailTrace_167203
  have hstable : (prefixWord ++ tailWord_167203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167203).length < 2 ^ (prefixWord ++ tailWord_167203).sum := by decide
  have hdescent : baseEnd_167203 < baseStart_167203 := by decide
  rcases family_descends (prefixWord ++ tailWord_167203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167220 : List Nat := [2, 5, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_167220 : Nat := 118140960795 + 167220 * 2 ^ 59
def prefixEnd_167220 : Nat := 4983230072969 + 3 ^ 40 * 167220 * 2
def baseEnd_167220 : Nat := 57242823363293989787317

theorem tailTrace_167220 : CollatzResearch.WordTrace tailWord_167220 prefixEnd_167220 57242823363293989787317 := by
  unfold tailWord_167220
  simp only [CollatzResearch.WordTrace]
  refine ⟨3049507227098986873709557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4066009636131982498279409 3049507227098986873709557)
  ·
    refine ⟨285891302540530019410271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3049507227098986873709557 285891302540530019410271)
    ·
      refine ⟨428836953810795029115407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285891302540530019410271 428836953810795029115407)
      ·
        refine ⟨643255430716192543673111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428836953810795029115407 643255430716192543673111)
        ·
          refine ⟨964883146074288815509667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643255430716192543673111 964883146074288815509667)
          ·
            refine ⟨1447324719111433223264501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964883146074288815509667 1447324719111433223264501)
            ·
              refine ⟨135686692416696864681047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1447324719111433223264501 135686692416696864681047)
              ·
                refine ⟨203530038625045297021571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135686692416696864681047 203530038625045297021571)
                ·
                  refine ⟨305295057937567945532357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203530038625045297021571 305295057937567945532357)
                  ·
                    refine ⟨57242823363293989787317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 305295057937567945532357 57242823363293989787317)
                    ·
                      rfl

theorem cell22_167220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_167220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167220 prefixEnd_167220 := by exact prefixLift 167220
  have htrace : WordTrace (prefixWord ++ tailWord_167220) baseStart_167220 baseEnd_167220 := by
    simpa [prefixWord, tailWord_167220, baseEnd_167220] using wordTrace_append hprefix tailTrace_167220
  have hstable : (prefixWord ++ tailWord_167220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167220).length < 2 ^ (prefixWord ++ tailWord_167220).sum := by decide
  have hdescent : baseEnd_167220 < baseStart_167220 := by decide
  rcases family_descends (prefixWord ++ tailWord_167220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167231 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 2, 4]
def baseStart_167231 : Nat := 118140960795 + 167231 * 2 ^ 59
def prefixEnd_167231 : Nat := 4983230072969 + 3 ^ 40 * 167231 * 2
def baseEnd_167231 : Nat := 57246588888093627762283

theorem tailTrace_167231 : CollatzResearch.WordTrace tailWord_167231 prefixEnd_167231 57246588888093627762283 := by
  unfold tailWord_167231
  simp only [CollatzResearch.WordTrace]
  refine ⟨6099415657158122626069547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4066277104772081750713031 6099415657158122626069547)
  ·
    refine ⟨9149123485737183939104321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6099415657158122626069547 9149123485737183939104321)
    ·
      refine ⟨6861842614302887954328241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9149123485737183939104321 6861842614302887954328241)
      ·
        refine ⟨5146381960727165965746181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6861842614302887954328241 5146381960727165965746181)
        ·
          refine ⟨964946617636343618577409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5146381960727165965746181 964946617636343618577409)
          ·
            refine ⟨723709963227257713933057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 964946617636343618577409 723709963227257713933057)
            ·
              refine ⟨542782472420443285449793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723709963227257713933057 542782472420443285449793)
              ·
                refine ⟨407086854315332464087345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542782472420443285449793 407086854315332464087345)
                ·
                  refine ⟨305315140736499348065509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407086854315332464087345 305315140736499348065509)
                  ·
                    refine ⟨57246588888093627762283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 305315140736499348065509 57246588888093627762283)
                    ·
                      rfl

theorem cell22_167231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_167231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167231 prefixEnd_167231 := by exact prefixLift 167231
  have htrace : WordTrace (prefixWord ++ tailWord_167231) baseStart_167231 baseEnd_167231 := by
    simpa [prefixWord, tailWord_167231, baseEnd_167231] using wordTrace_append hprefix tailTrace_167231
  have hstable : (prefixWord ++ tailWord_167231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167231).length < 2 ^ (prefixWord ++ tailWord_167231).sum := by decide
  have hdescent : baseEnd_167231 < baseStart_167231 := by decide
  rcases family_descends (prefixWord ++ tailWord_167231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167308 : List Nat := [2, 2, 1, 2, 1, 3, 5, 1, 5]
def baseStart_167308 : Nat := 118140960795 + 167308 * 2 ^ 59
def prefixEnd_167308 : Nat := 4983230072969 + 3 ^ 40 * 167308 * 2
def baseEnd_167308 : Nat := 19090982520563697862349

theorem tailTrace_167308 : CollatzResearch.WordTrace tailWord_167308 prefixEnd_167308 19090982520563697862349 := by
  unfold tailWord_167308
  simp only [CollatzResearch.WordTrace]
  refine ⟨3051112038939582388311289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4068149385252776517748385 3051112038939582388311289)
  ·
    refine ⟨2288334029204686791233467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3051112038939582388311289 2288334029204686791233467)
    ·
      refine ⟨3432501043807030186850201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2288334029204686791233467 3432501043807030186850201)
      ·
        refine ⟨2574375782855272640137651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3432501043807030186850201 2574375782855272640137651)
        ·
          refine ⟨3861563674282908960206477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2574375782855272640137651 3861563674282908960206477)
          ·
            refine ⟨1448086377856090860077429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3861563674282908960206477 1448086377856090860077429)
            ·
              refine ⟨135758097924008518132259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1448086377856090860077429 135758097924008518132259)
              ·
                refine ⟨203637146886012777198389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135758097924008518132259 203637146886012777198389)
                ·
                  refine ⟨19090982520563697862349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 203637146886012777198389 19090982520563697862349)
                  ·
                    rfl

theorem cell22_167308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_167308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167308 prefixEnd_167308 := by exact prefixLift 167308
  have htrace : WordTrace (prefixWord ++ tailWord_167308) baseStart_167308 baseEnd_167308 := by
    simpa [prefixWord, tailWord_167308, baseEnd_167308] using wordTrace_append hprefix tailTrace_167308
  have hstable : (prefixWord ++ tailWord_167308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167308).length < 2 ^ (prefixWord ++ tailWord_167308).sum := by decide
  have hdescent : baseEnd_167308 < baseStart_167308 := by decide
  rcases family_descends (prefixWord ++ tailWord_167308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167381 : List Nat := [1, 3, 2, 3, 1, 1, 1, 10]
def baseStart_167381 : Nat := 118140960795 + 167381 * 2 ^ 59
def prefixEnd_167381 : Nat := 4983230072969 + 3 ^ 40 * 167381 * 2
def baseEnd_167381 : Nat := 6366437439282581834647

theorem tailTrace_167381 : CollatzResearch.WordTrace tailWord_167381 prefixEnd_167381 6366437439282581834647 := by
  unfold tailWord_167381
  simp only [CollatzResearch.WordTrace]
  refine ⟨6104886606614698244029997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4069924404409798829353331 6104886606614698244029997)
  ·
    refine ⟨2289332477480511841511249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6104886606614698244029997 2289332477480511841511249)
    ·
      refine ⟨1716999358110383881133437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2289332477480511841511249 1716999358110383881133437)
      ·
        refine ⟨643874759291393955425039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1716999358110383881133437 643874759291393955425039)
        ·
          refine ⟨965812138937090933137559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643874759291393955425039 965812138937090933137559)
          ·
            refine ⟨1448718208405636399706339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965812138937090933137559 1448718208405636399706339)
            ·
              refine ⟨2173077312608454599559509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1448718208405636399706339 2173077312608454599559509)
              ·
                refine ⟨6366437439282581834647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2173077312608454599559509 6366437439282581834647)
                ·
                  rfl

theorem cell22_167381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 10].length) (baseStart_167381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167381 prefixEnd_167381 := by exact prefixLift 167381
  have htrace : WordTrace (prefixWord ++ tailWord_167381) baseStart_167381 baseEnd_167381 := by
    simpa [prefixWord, tailWord_167381, baseEnd_167381] using wordTrace_append hprefix tailTrace_167381
  have hstable : (prefixWord ++ tailWord_167381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167381).length < 2 ^ (prefixWord ++ tailWord_167381).sum := by decide
  have hdescent : baseEnd_167381 < baseStart_167381 := by decide
  rcases family_descends (prefixWord ++ tailWord_167381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167402 : List Nat := [3, 1, 3, 1, 4, 1, 2, 2, 2, 3]
def baseStart_167402 : Nat := 118140960795 + 167402 * 2 ^ 59
def prefixEnd_167402 : Nat := 4983230072969 + 3 ^ 40 * 167402 * 2
def baseEnd_167402 : Nat := 57305125682706181736759

theorem tailTrace_167402 : CollatzResearch.WordTrace tailWord_167402 prefixEnd_167402 57305125682706181736759 := by
  unfold tailWord_167402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526413134884654707636115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4070435026359079220362973 1526413134884654707636115)
  ·
    refine ⟨2289619702326982061454173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1526413134884654707636115 2289619702326982061454173)
    ·
      refine ⟨858607388372618273045315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2289619702326982061454173 858607388372618273045315)
      ·
        refine ⟨1287911082558927409567973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 858607388372618273045315 1287911082558927409567973)
        ·
          refine ⟨241483327979798889293995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1287911082558927409567973 241483327979798889293995)
          ·
            refine ⟨362224991969698333940993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241483327979798889293995 362224991969698333940993)
            ·
              refine ⟨271668743977273750455745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362224991969698333940993 271668743977273750455745)
              ·
                refine ⟨203751557982955312841809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271668743977273750455745 203751557982955312841809)
                ·
                  refine ⟨152813668487216484631357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203751557982955312841809 152813668487216484631357)
                  ·
                    refine ⟨57305125682706181736759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 152813668487216484631357 57305125682706181736759)
                    ·
                      rfl

theorem cell22_167402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_167402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167402 prefixEnd_167402 := by exact prefixLift 167402
  have htrace : WordTrace (prefixWord ++ tailWord_167402) baseStart_167402 baseEnd_167402 := by
    simpa [prefixWord, tailWord_167402, baseEnd_167402] using wordTrace_append hprefix tailTrace_167402
  have hstable : (prefixWord ++ tailWord_167402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167402).length < 2 ^ (prefixWord ++ tailWord_167402).sum := by decide
  have hdescent : baseEnd_167402 < baseStart_167402 := by decide
  rcases family_descends (prefixWord ++ tailWord_167402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167441 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 1, 7]
def baseStart_167441 : Nat := 118140960795 + 167441 * 2 ^ 59
def prefixEnd_167441 : Nat := 4983230072969 + 3 ^ 40 * 167441 * 2
def baseEnd_167441 : Nat := 57318476179723080011639

theorem tailTrace_167441 : CollatzResearch.WordTrace tailWord_167441 prefixEnd_167441 57318476179723080011639 := by
  unfold tailWord_167441
  simp only [CollatzResearch.WordTrace]
  refine ⟨6107074986397328491214177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4071383324264885660809451 6107074986397328491214177)
  ·
    refine ⟨4580306239797996368410633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6107074986397328491214177 4580306239797996368410633)
    ·
      refine ⟨3435229679848497276307975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4580306239797996368410633 3435229679848497276307975)
      ·
        refine ⟨5152844519772745914461963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3435229679848497276307975 5152844519772745914461963)
        ·
          refine ⟨7729266779659118871692945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5152844519772745914461963 7729266779659118871692945)
          ·
            refine ⟨5796950084744339153769709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7729266779659118871692945 5796950084744339153769709)
            ·
              refine ⟨2173856281779127182663641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5796950084744339153769709 2173856281779127182663641)
              ·
                refine ⟨1630392211334345386997731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2173856281779127182663641 1630392211334345386997731)
                ·
                  refine ⟨2445588317001518080496597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1630392211334345386997731 2445588317001518080496597)
                  ·
                    refine ⟨57318476179723080011639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2445588317001518080496597 57318476179723080011639)
                    ·
                      rfl

theorem cell22_167441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_167441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167441 prefixEnd_167441 := by exact prefixLift 167441
  have htrace : WordTrace (prefixWord ++ tailWord_167441) baseStart_167441 baseEnd_167441 := by
    simpa [prefixWord, tailWord_167441, baseEnd_167441] using wordTrace_append hprefix tailTrace_167441
  have hstable : (prefixWord ++ tailWord_167441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167441).length < 2 ^ (prefixWord ++ tailWord_167441).sum := by decide
  have hdescent : baseEnd_167441 < baseStart_167441 := by decide
  rcases family_descends (prefixWord ++ tailWord_167441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167458 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_167458 : Nat := 118140960795 + 167458 * 2 ^ 59
def prefixEnd_167458 : Nat := 4983230072969 + 3 ^ 40 * 167458 * 2
def baseEnd_167458 : Nat := 57324295627140702336587

theorem tailTrace_167458 : CollatzResearch.WordTrace tailWord_167458 prefixEnd_167458 57324295627140702336587 := by
  unfold tailWord_167458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526923756833935098645757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4071796684890493596388685 1526923756833935098645757)
  ·
    refine ⟨572596408812725661992159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1526923756833935098645757 572596408812725661992159)
    ·
      refine ⟨858894613219088492988239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 572596408812725661992159 858894613219088492988239)
      ·
        refine ⟨1288341919828632739482359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 858894613219088492988239 1288341919828632739482359)
        ·
          refine ⟨1932512879742949109223539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1288341919828632739482359 1932512879742949109223539)
          ·
            refine ⟨2898769319614423663835309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1932512879742949109223539 2898769319614423663835309)
            ·
              refine ⟨1087038494855408873938241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2898769319614423663835309 1087038494855408873938241)
              ·
                refine ⟨815278871141556655453681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1087038494855408873938241 815278871141556655453681)
                ·
                  refine ⟨611459153356167491590261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 815278871141556655453681 611459153356167491590261)
                  ·
                    refine ⟨57324295627140702336587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 611459153356167491590261 57324295627140702336587)
                    ·
                      rfl

theorem cell22_167458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_167458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167458 prefixEnd_167458 := by exact prefixLift 167458
  have htrace : WordTrace (prefixWord ++ tailWord_167458) baseStart_167458 baseEnd_167458 := by
    simpa [prefixWord, tailWord_167458, baseEnd_167458] using wordTrace_append hprefix tailTrace_167458
  have hstable : (prefixWord ++ tailWord_167458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167458).length < 2 ^ (prefixWord ++ tailWord_167458).sum := by decide
  have hdescent : baseEnd_167458 < baseStart_167458 := by decide
  rcases family_descends (prefixWord ++ tailWord_167458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167520 : List Nat := [2, 1, 1, 3, 2, 1, 1, 6, 2, 3]
def baseStart_167520 : Nat := 118140960795 + 167520 * 2 ^ 59
def prefixEnd_167520 : Nat := 4983230072969 + 3 ^ 40 * 167520 * 2
def baseEnd_167520 : Nat := 57345519494193207286397

theorem tailTrace_167520 : CollatzResearch.WordTrace tailWord_167520 prefixEnd_167520 57345519494193207286397 := by
  unfold tailWord_167520
  simp only [CollatzResearch.WordTrace]
  refine ⟨3054978176555562491670007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4073304235407416655560009 3054978176555562491670007)
  ·
    refine ⟨4582467264833343737505011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3054978176555562491670007 4582467264833343737505011)
    ·
      refine ⟨6873700897250015606257517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4582467264833343737505011 6873700897250015606257517)
      ·
        refine ⟨2577637836468755852346569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6873700897250015606257517 2577637836468755852346569)
        ·
          refine ⟨1933228377351566889259927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2577637836468755852346569 1933228377351566889259927)
          ·
            refine ⟨2899842566027350333889891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1933228377351566889259927 2899842566027350333889891)
            ·
              refine ⟨4349763849041025500834837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899842566027350333889891 4349763849041025500834837)
              ·
                refine ⟨203895180423798070351633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4349763849041025500834837 203895180423798070351633)
                ·
                  refine ⟨152921385317848552763725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203895180423798070351633 152921385317848552763725)
                  ·
                    refine ⟨57345519494193207286397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 152921385317848552763725 57345519494193207286397)
                    ·
                      rfl

theorem cell22_167520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 2, 3].length) (baseStart_167520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167520 prefixEnd_167520 := by exact prefixLift 167520
  have htrace : WordTrace (prefixWord ++ tailWord_167520) baseStart_167520 baseEnd_167520 := by
    simpa [prefixWord, tailWord_167520, baseEnd_167520] using wordTrace_append hprefix tailTrace_167520
  have hstable : (prefixWord ++ tailWord_167520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167520).length < 2 ^ (prefixWord ++ tailWord_167520).sum := by decide
  have hdescent : baseEnd_167520 < baseStart_167520 := by decide
  rcases family_descends (prefixWord ++ tailWord_167520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167623 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 8]
def baseStart_167623 : Nat := 118140960795 + 167623 * 2 ^ 59
def prefixEnd_167623 : Nat := 4983230072969 + 3 ^ 40 * 167623 * 2
def baseEnd_167623 : Nat := 19126926166378423987027

theorem tailTrace_167623 : CollatzResearch.WordTrace tailWord_167623 prefixEnd_167623 19126926166378423987027 := by
  unfold tailWord_167623
  simp only [CollatzResearch.WordTrace]
  refine ⟨6113713071737973574339523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4075808714491982382893015 6113713071737973574339523)
  ·
    refine ⟨9170569607606960361509285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6113713071737973574339523 9170569607606960361509285)
    ·
      refine ⟨1719481801426305067782991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9170569607606960361509285 1719481801426305067782991)
      ·
        refine ⟨2579222702139457601674487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1719481801426305067782991 2579222702139457601674487)
        ·
          refine ⟨3868834053209186402511731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2579222702139457601674487 3868834053209186402511731)
          ·
            refine ⟨5803251079813779603767597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3868834053209186402511731 5803251079813779603767597)
            ·
              refine ⟨2176219154930167351412849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5803251079813779603767597 2176219154930167351412849)
              ·
                refine ⟨1632164366197625513559637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2176219154930167351412849 1632164366197625513559637)
                ·
                  refine ⟨19126926166378423987027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1632164366197625513559637 19126926166378423987027)
                  ·
                    rfl

theorem cell22_167623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 8].length) (baseStart_167623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167623 prefixEnd_167623 := by exact prefixLift 167623
  have htrace : WordTrace (prefixWord ++ tailWord_167623) baseStart_167623 baseEnd_167623 := by
    simpa [prefixWord, tailWord_167623, baseEnd_167623] using wordTrace_append hprefix tailTrace_167623
  have hstable : (prefixWord ++ tailWord_167623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167623).length < 2 ^ (prefixWord ++ tailWord_167623).sum := by decide
  have hdescent : baseEnd_167623 < baseStart_167623 := by decide
  rcases family_descends (prefixWord ++ tailWord_167623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167629 : List Nat := [1, 6, 2, 1, 1, 1, 3, 2, 5]
def baseStart_167629 : Nat := 118140960795 + 167629 * 2 ^ 59
def prefixEnd_167629 : Nat := 4983230072969 + 3 ^ 40 * 167629 * 2
def baseEnd_167629 : Nat := 19127610807251085437021

theorem tailTrace_167629 : CollatzResearch.WordTrace tailWord_167629 prefixEnd_167629 19127610807251085437021 := by
  unfold tailWord_167629
  simp only [CollatzResearch.WordTrace]
  refine ⟨6113931909716236599057941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4075954606477491066038627 6113931909716236599057941)
  ·
    refine ⟨286590558267948590580841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6113931909716236599057941 286590558267948590580841)
    ·
      refine ⟨214942918700961442935631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286590558267948590580841 214942918700961442935631)
      ·
        refine ⟨322414378051442164403447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214942918700961442935631 322414378051442164403447)
        ·
          refine ⟨483621567077163246605171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322414378051442164403447 483621567077163246605171)
          ·
            refine ⟨725432350615744869907757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483621567077163246605171 725432350615744869907757)
            ·
              refine ⟨272037131480904326215409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 725432350615744869907757 272037131480904326215409)
              ·
                refine ⟨204027848610678244661557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272037131480904326215409 204027848610678244661557)
                ·
                  refine ⟨19127610807251085437021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 204027848610678244661557 19127610807251085437021)
                  ·
                    rfl

theorem cell22_167629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_167629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167629 prefixEnd_167629 := by exact prefixLift 167629
  have htrace : WordTrace (prefixWord ++ tailWord_167629) baseStart_167629 baseEnd_167629 := by
    simpa [prefixWord, tailWord_167629, baseEnd_167629] using wordTrace_append hprefix tailTrace_167629
  have hstable : (prefixWord ++ tailWord_167629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167629).length < 2 ^ (prefixWord ++ tailWord_167629).sum := by decide
  have hdescent : baseEnd_167629 < baseStart_167629 := by decide
  rcases family_descends (prefixWord ++ tailWord_167629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167640 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 6]
def baseStart_167640 : Nat := 118140960795 + 167640 * 2 ^ 59
def prefixEnd_167640 : Nat := 4983230072969 + 3 ^ 40 * 167640 * 2
def baseEnd_167640 : Nat := 19128865982184298095343

theorem tailTrace_167640 : CollatzResearch.WordTrace tailWord_167640 prefixEnd_167640 19128865982184298095343 := by
  unfold tailWord_167640
  simp only [CollatzResearch.WordTrace]
  refine ⟨3057166556338192738854187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4076222075117590318472249 3057166556338192738854187)
  ·
    refine ⟨4585749834507289108281281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3057166556338192738854187 4585749834507289108281281)
    ·
      refine ⟨3439312375880466831210961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4585749834507289108281281 3439312375880466831210961)
      ·
        refine ⟨2579484281910350123408221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3439312375880466831210961 2579484281910350123408221)
        ·
          refine ⟨967306605716381296278083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2579484281910350123408221 967306605716381296278083)
          ·
            refine ⟨1450959908574571944417125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967306605716381296278083 1450959908574571944417125)
            ·
              refine ⟨272054982857732239578211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1450959908574571944417125 272054982857732239578211)
              ·
                refine ⟨408082474286598359367317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272054982857732239578211 408082474286598359367317)
                ·
                  refine ⟨19128865982184298095343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 408082474286598359367317 19128865982184298095343)
                  ·
                    rfl

theorem cell22_167640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 6].length) (baseStart_167640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167640 prefixEnd_167640 := by exact prefixLift 167640
  have htrace : WordTrace (prefixWord ++ tailWord_167640) baseStart_167640 baseEnd_167640 := by
    simpa [prefixWord, tailWord_167640, baseEnd_167640] using wordTrace_append hprefix tailTrace_167640
  have hstable : (prefixWord ++ tailWord_167640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167640).length < 2 ^ (prefixWord ++ tailWord_167640).sum := by decide
  have hdescent : baseEnd_167640 < baseStart_167640 := by decide
  rcases family_descends (prefixWord ++ tailWord_167640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167706 : List Nat := [3, 1, 1, 3, 2, 4, 2, 1, 2, 3]
def baseStart_167706 : Nat := 118140960795 + 167706 * 2 ^ 59
def prefixEnd_167706 : Nat := 4983230072969 + 3 ^ 40 * 167706 * 2
def baseEnd_167706 : Nat := 57409191095350722135827

theorem tailTrace_167706 : CollatzResearch.WordTrace tailWord_167706 prefixEnd_167706 57409191095350722135827 := by
  unfold tailWord_167706
  simp only [CollatzResearch.WordTrace]
  refine ⟨1529185082609319687402743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4077826886958185833073981 1529185082609319687402743)
  ·
    refine ⟨2293777623913979531104115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1529185082609319687402743 2293777623913979531104115)
    ·
      refine ⟨3440666435870969296656173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2293777623913979531104115 3440666435870969296656173)
      ·
        refine ⟨1290249913451613486246065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3440666435870969296656173 1290249913451613486246065)
        ·
          refine ⟨967687435088710114684549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1290249913451613486246065 967687435088710114684549)
          ·
            refine ⟨181441394079133146503353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 967687435088710114684549 181441394079133146503353)
            ·
              refine ⟨136081045559349859877515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181441394079133146503353 136081045559349859877515)
              ·
                refine ⟨204121568339024789816273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136081045559349859877515 204121568339024789816273)
                ·
                  refine ⟨153091176254268592362205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204121568339024789816273 153091176254268592362205)
                  ·
                    refine ⟨57409191095350722135827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153091176254268592362205 57409191095350722135827)
                    ·
                      rfl

theorem cell22_167706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_167706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167706 prefixEnd_167706 := by exact prefixLift 167706
  have htrace : WordTrace (prefixWord ++ tailWord_167706) baseStart_167706 baseEnd_167706 := by
    simpa [prefixWord, tailWord_167706, baseEnd_167706] using wordTrace_append hprefix tailTrace_167706
  have hstable : (prefixWord ++ tailWord_167706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167706).length < 2 ^ (prefixWord ++ tailWord_167706).sum := by decide
  have hdescent : baseEnd_167706 < baseStart_167706 := by decide
  rcases family_descends (prefixWord ++ tailWord_167706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167710 : List Nat := [4, 3, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_167710 : Nat := 118140960795 + 167710 * 2 ^ 59
def prefixEnd_167710 : Nat := 4983230072969 + 3 ^ 40 * 167710 * 2
def baseEnd_167710 : Nat := 57410560377096045035815

theorem tailTrace_167710 : CollatzResearch.WordTrace tailWord_167710 prefixEnd_167710 57410560377096045035815 := by
  unfold tailWord_167710
  simp only [CollatzResearch.WordTrace]
  refine ⟨764610777802848429094573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4077924148281858288504389 764610777802848429094573)
  ·
    refine ⟨286729041676068160910465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 764610777802848429094573 286729041676068160910465)
    ·
      refine ⟨215046781257051120682849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286729041676068160910465 215046781257051120682849)
      ·
        refine ⟨161285085942788340512137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215046781257051120682849 161285085942788340512137)
        ·
          refine ⟨120963814457091255384103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161285085942788340512137 120963814457091255384103)
          ·
            refine ⟨181445721685636883076155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120963814457091255384103 181445721685636883076155)
            ·
              refine ⟨272168582528455324614233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181445721685636883076155 272168582528455324614233)
              ·
                refine ⟨204126436896341493460675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272168582528455324614233 204126436896341493460675)
                ·
                  refine ⟨306189655344512240191013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204126436896341493460675 306189655344512240191013)
                  ·
                    refine ⟨57410560377096045035815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 306189655344512240191013 57410560377096045035815)
                    ·
                      rfl

theorem cell22_167710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_167710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167710 prefixEnd_167710 := by exact prefixLift 167710
  have htrace : WordTrace (prefixWord ++ tailWord_167710) baseStart_167710 baseEnd_167710 := by
    simpa [prefixWord, tailWord_167710, baseEnd_167710] using wordTrace_append hprefix tailTrace_167710
  have hstable : (prefixWord ++ tailWord_167710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167710).length < 2 ^ (prefixWord ++ tailWord_167710).sum := by decide
  have hdescent : baseEnd_167710 < baseStart_167710 := by decide
  rcases family_descends (prefixWord ++ tailWord_167710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167747 : List Nat := [1, 1, 1, 3, 1, 6, 2, 2, 5]
def baseStart_167747 : Nat := 118140960795 + 167747 * 2 ^ 59
def prefixEnd_167747 : Nat := 4983230072969 + 3 ^ 40 * 167747 * 2
def baseEnd_167747 : Nat := 19141075411080093953567

theorem tailTrace_167747 : CollatzResearch.WordTrace tailWord_167747 prefixEnd_167747 19141075411080093953567 := by
  unfold tailWord_167747
  simp only [CollatzResearch.WordTrace]
  refine ⟨6118235723288742751853495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4078823815525828501235663 6118235723288742751853495)
  ·
    refine ⟨9177353584933114127780243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6118235723288742751853495 9177353584933114127780243)
    ·
      refine ⟨13766030377399671191670365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9177353584933114127780243 13766030377399671191670365)
      ·
        refine ⟨5162261391524876696876387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13766030377399671191670365 5162261391524876696876387)
        ·
          refine ⟨7743392087287315045314581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5162261391524876696876387 7743392087287315045314581)
          ·
            refine ⟨362971504091592892749121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7743392087287315045314581 362971504091592892749121)
            ·
              refine ⟨272228628068694669561841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362971504091592892749121 272228628068694669561841)
              ·
                refine ⟨204171471051521002171381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272228628068694669561841 204171471051521002171381)
                ·
                  refine ⟨19141075411080093953567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 204171471051521002171381 19141075411080093953567)
                  ·
                    rfl

theorem cell22_167747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 5].length) (baseStart_167747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167747 prefixEnd_167747 := by exact prefixLift 167747
  have htrace : WordTrace (prefixWord ++ tailWord_167747) baseStart_167747 baseEnd_167747 := by
    simpa [prefixWord, tailWord_167747, baseEnd_167747] using wordTrace_append hprefix tailTrace_167747
  have hstable : (prefixWord ++ tailWord_167747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167747).length < 2 ^ (prefixWord ++ tailWord_167747).sum := by decide
  have hdescent : baseEnd_167747 < baseStart_167747 := by decide
  rcases family_descends (prefixWord ++ tailWord_167747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167751 : List Nat := [1, 1, 4, 1, 2, 1, 6, 2, 1, 3]
def baseStart_167751 : Nat := 118140960795 + 167751 * 2 ^ 59
def prefixEnd_167751 : Nat := 4983230072969 + 3 ^ 40 * 167751 * 2
def baseEnd_167751 : Nat := 57424595514985604760689

theorem tailTrace_167751 : CollatzResearch.WordTrace tailWord_167751 prefixEnd_167751 57424595514985604760689 := by
  unfold tailWord_167751
  simp only [CollatzResearch.WordTrace]
  refine ⟨6118381615274251434999107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4078921076849500956666071 6118381615274251434999107)
  ·
    refine ⟨9177572422911377152498661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6118381615274251434999107 9177572422911377152498661)
    ·
      refine ⟨1720794829295883216093499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9177572422911377152498661 1720794829295883216093499)
      ·
        refine ⟨2581192243943824824140249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1720794829295883216093499 2581192243943824824140249)
        ·
          refine ⟨1935894182957868618105187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2581192243943824824140249 1935894182957868618105187)
          ·
            refine ⟨2903841274436802927157781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1935894182957868618105187 2903841274436802927157781)
            ·
              refine ⟨136117559739225137210521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2903841274436802927157781 136117559739225137210521)
              ·
                refine ⟨102088169804418852907891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136117559739225137210521 102088169804418852907891)
                ·
                  refine ⟨153132254706628279361837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102088169804418852907891 153132254706628279361837)
                  ·
                    refine ⟨57424595514985604760689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153132254706628279361837 57424595514985604760689)
                    ·
                      rfl

theorem cell22_167751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_167751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167751 prefixEnd_167751 := by exact prefixLift 167751
  have htrace : WordTrace (prefixWord ++ tailWord_167751) baseStart_167751 baseEnd_167751 := by
    simpa [prefixWord, tailWord_167751, baseEnd_167751] using wordTrace_append hprefix tailTrace_167751
  have hstable : (prefixWord ++ tailWord_167751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167751).length < 2 ^ (prefixWord ++ tailWord_167751).sum := by decide
  have hdescent : baseEnd_167751 < baseStart_167751 := by decide
  rcases family_descends (prefixWord ++ tailWord_167751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167762 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_167762 : Nat := 118140960795 + 167762 * 2 ^ 59
def prefixEnd_167762 : Nat := 4983230072969 + 3 ^ 40 * 167762 * 2
def baseEnd_167762 : Nat := 57428361039785242735655

theorem tailTrace_167762 : CollatzResearch.WordTrace tailWord_167762 prefixEnd_167762 57428361039785242735655 := by
  unfold tailWord_167762
  simp only [CollatzResearch.WordTrace]
  refine ⟨1529695704558600078412385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4079188545489600209099693 1529695704558600078412385)
  ·
    refine ⟨1147271778418950058809289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1529695704558600078412385 1147271778418950058809289)
    ·
      refine ⟨860453833814212544106967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1147271778418950058809289 860453833814212544106967)
      ·
        refine ⟨1290680750721318816160451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860453833814212544106967 1290680750721318816160451)
        ·
          refine ⟨1936021126081978224240677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290680750721318816160451 1936021126081978224240677)
          ·
            refine ⟨363003961140370917045127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1936021126081978224240677 363003961140370917045127)
            ·
              refine ⟨544505941710556375567691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363003961140370917045127 544505941710556375567691)
              ·
                refine ⟨816758912565834563351537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544505941710556375567691 816758912565834563351537)
                ·
                  refine ⟨612569184424375922513653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 816758912565834563351537 612569184424375922513653)
                  ·
                    refine ⟨57428361039785242735655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 612569184424375922513653 57428361039785242735655)
                    ·
                      rfl

theorem cell22_167762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_167762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167762 prefixEnd_167762 := by exact prefixLift 167762
  have htrace : WordTrace (prefixWord ++ tailWord_167762) baseStart_167762 baseEnd_167762 := by
    simpa [prefixWord, tailWord_167762, baseEnd_167762] using wordTrace_append hprefix tailTrace_167762
  have hstable : (prefixWord ++ tailWord_167762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167762).length < 2 ^ (prefixWord ++ tailWord_167762).sum := by decide
  have hdescent : baseEnd_167762 < baseStart_167762 := by decide
  rcases family_descends (prefixWord ++ tailWord_167762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167775 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 8]
def baseStart_167775 : Nat := 118140960795 + 167775 * 2 ^ 59
def prefixEnd_167775 : Nat := 4983230072969 + 3 ^ 40 * 167775 * 2
def baseEnd_167775 : Nat := 19144270401819180720205

theorem tailTrace_167775 : CollatzResearch.WordTrace tailWord_167775 prefixEnd_167775 19144270401819180720205 := by
  unfold tailWord_167775
  simp only [CollatzResearch.WordTrace]
  refine ⟨6119256967187303533872779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4079504644791535689248519 6119256967187303533872779)
  ·
    refine ⟨9178885450780955300809169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6119256967187303533872779 9178885450780955300809169)
    ·
      refine ⟨6884164088085716475606877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9178885450780955300809169 6884164088085716475606877)
      ·
        refine ⟨2581561533032143678352579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6884164088085716475606877 2581561533032143678352579)
        ·
          refine ⟨3872342299548215517528869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2581561533032143678352579 3872342299548215517528869)
          ·
            refine ⟨726064181165290409536663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3872342299548215517528869 726064181165290409536663)
            ·
              refine ⟨1089096271747935614304995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726064181165290409536663 1089096271747935614304995)
              ·
                refine ⟨1633644407621903421457493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089096271747935614304995 1633644407621903421457493)
                ·
                  refine ⟨19144270401819180720205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1633644407621903421457493 19144270401819180720205)
                  ·
                    rfl

theorem cell22_167775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 8].length) (baseStart_167775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167775 prefixEnd_167775 := by exact prefixLift 167775
  have htrace : WordTrace (prefixWord ++ tailWord_167775) baseStart_167775 baseEnd_167775 := by
    simpa [prefixWord, tailWord_167775, baseEnd_167775] using wordTrace_append hprefix tailTrace_167775
  have hstable : (prefixWord ++ tailWord_167775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167775).length < 2 ^ (prefixWord ++ tailWord_167775).sum := by decide
  have hdescent : baseEnd_167775 < baseStart_167775 := by decide
  rcases family_descends (prefixWord ++ tailWord_167775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167777 : List Nat := [1, 2, 3, 1, 1, 1, 4, 4, 1, 4]
def baseStart_167777 : Nat := 118140960795 + 167777 * 2 ^ 59
def prefixEnd_167777 : Nat := 4983230072969 + 3 ^ 40 * 167777 * 2
def baseEnd_167777 : Nat := 57433495846330203610609

theorem tailTrace_167777 : CollatzResearch.WordTrace tailWord_167777 prefixEnd_167777 57433495846330203610609 := by
  unfold tailWord_167777
  simp only [CollatzResearch.WordTrace]
  refine ⟨6119329913180057875445585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4079553275453371916963723 6119329913180057875445585)
  ·
    refine ⟨4589497434885043406584189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6119329913180057875445585 4589497434885043406584189)
    ·
      refine ⟨1721061538081891277469071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4589497434885043406584189 1721061538081891277469071)
      ·
        refine ⟨2581592307122836916203607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1721061538081891277469071 2581592307122836916203607)
        ·
          refine ⟨3872388460684255374305411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2581592307122836916203607 3872388460684255374305411)
          ·
            refine ⟨5808582691026383061458117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3872388460684255374305411 5808582691026383061458117)
            ·
              refine ⟨1089109254567446824023397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5808582691026383061458117 1089109254567446824023397)
              ·
                refine ⟨204207985231396279504387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1089109254567446824023397 204207985231396279504387)
                ·
                  refine ⟨306311977847094419256581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204207985231396279504387 306311977847094419256581)
                  ·
                    refine ⟨57433495846330203610609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 306311977847094419256581 57433495846330203610609)
                    ·
                      rfl

theorem cell22_167777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_167777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167777 prefixEnd_167777 := by exact prefixLift 167777
  have htrace : WordTrace (prefixWord ++ tailWord_167777) baseStart_167777 baseEnd_167777 := by
    simpa [prefixWord, tailWord_167777, baseEnd_167777] using wordTrace_append hprefix tailTrace_167777
  have hstable : (prefixWord ++ tailWord_167777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167777).length < 2 ^ (prefixWord ++ tailWord_167777).sum := by decide
  have hdescent : baseEnd_167777 < baseStart_167777 := by decide
  rcases family_descends (prefixWord ++ tailWord_167777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167798 : List Nat := [5, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_167798 : Nat := 118140960795 + 167798 * 2 ^ 59
def prefixEnd_167798 : Nat := 4983230072969 + 3 ^ 40 * 167798 * 2
def baseEnd_167798 : Nat := 19146894858497716278515

theorem tailTrace_167798 : CollatzResearch.WordTrace tailWord_167798 prefixEnd_167798 19146894858497716278515 := by
  unfold tailWord_167798
  simp only [CollatzResearch.WordTrace]
  refine ⟨382505990381498653872503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4080063897402652307973365 382505990381498653872503)
  ·
    refine ⟨573758985572247980808755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 382505990381498653872503 573758985572247980808755)
    ·
      refine ⟨860638478358371971213133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 573758985572247980808755 860638478358371971213133)
      ·
        refine ⟨322739429384389489204925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 860638478358371971213133 322739429384389489204925)
        ·
          refine ⟨121027286019146058451847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 322739429384389489204925 121027286019146058451847)
          ·
            refine ⟨181540929028719087677771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121027286019146058451847 181540929028719087677771)
            ·
              refine ⟨272311393543078631516657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181540929028719087677771 272311393543078631516657)
              ·
                refine ⟨204233545157308973637493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272311393543078631516657 204233545157308973637493)
                ·
                  refine ⟨19146894858497716278515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 204233545157308973637493 19146894858497716278515)
                  ·
                    rfl

theorem cell22_167798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_167798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167798 prefixEnd_167798 := by exact prefixLift 167798
  have htrace : WordTrace (prefixWord ++ tailWord_167798) baseStart_167798 baseEnd_167798 := by
    simpa [prefixWord, tailWord_167798, baseEnd_167798] using wordTrace_append hprefix tailTrace_167798
  have hstable : (prefixWord ++ tailWord_167798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167798).length < 2 ^ (prefixWord ++ tailWord_167798).sum := by decide
  have hdescent : baseEnd_167798 < baseStart_167798 := by decide
  rcases family_descends (prefixWord ++ tailWord_167798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167820 : List Nat := [2, 2, 1, 2, 1, 2, 1, 11]
def baseStart_167820 : Nat := 118140960795 + 167820 * 2 ^ 59
def prefixEnd_167820 : Nat := 4983230072969 + 3 ^ 40 * 167820 * 2
def baseEnd_167820 : Nat := 6383135069454713865053

theorem tailTrace_167820 : CollatzResearch.WordTrace tailWord_167820 prefixEnd_167820 6383135069454713865053 := by
  unfold tailWord_167820
  simp only [CollatzResearch.WordTrace]
  refine ⟨3060449126012138109630457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4080598834682850812840609 3060449126012138109630457)
  ·
    refine ⟨2295336844509103582222843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3060449126012138109630457 2295336844509103582222843)
    ·
      refine ⟨3443005266763655373334265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2295336844509103582222843 3443005266763655373334265)
      ·
        refine ⟨2582253950072741530000699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3443005266763655373334265 2582253950072741530000699)
        ·
          refine ⟨3873380925109112295001049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2582253950072741530000699 3873380925109112295001049)
          ·
            refine ⟨2905035693831834221250787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3873380925109112295001049 2905035693831834221250787)
            ·
              refine ⟨4357553540747751331876181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905035693831834221250787 4357553540747751331876181)
              ·
                refine ⟨6383135069454713865053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 4357553540747751331876181 6383135069454713865053)
                ·
                  rfl

theorem cell22_167820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 11].length) (baseStart_167820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167820 prefixEnd_167820 := by exact prefixLift 167820
  have htrace : WordTrace (prefixWord ++ tailWord_167820) baseStart_167820 baseEnd_167820 := by
    simpa [prefixWord, tailWord_167820, baseEnd_167820] using wordTrace_append hprefix tailTrace_167820
  have hstable : (prefixWord ++ tailWord_167820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167820).length < 2 ^ (prefixWord ++ tailWord_167820).sum := by decide
  have hdescent : baseEnd_167820 < baseStart_167820 := by decide
  rcases family_descends (prefixWord ++ tailWord_167820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167837 : List Nat := [1, 4, 2, 1, 2, 3, 1, 8]
def baseStart_167837 : Nat := 118140960795 + 167837 * 2 ^ 59
def prefixEnd_167837 : Nat := 4983230072969 + 3 ^ 40 * 167837 * 2
def baseEnd_167837 : Nat := 6383781674723338567825

theorem tailTrace_167837 : CollatzResearch.WordTrace tailWord_167837 prefixEnd_167837 6383781674723338567825 := by
  unfold tailWord_167837
  simp only [CollatzResearch.WordTrace]
  refine ⟨6121518292962688122629765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4081012195308458748419843 6121518292962688122629765)
  ·
    refine ⟨1147784679930504022993081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6121518292962688122629765 1147784679930504022993081)
    ·
      refine ⟨860838509947878017244811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1147784679930504022993081 860838509947878017244811)
      ·
        refine ⟨1291257764921817025867217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860838509947878017244811 1291257764921817025867217)
        ·
          refine ⟨968443323691362769400413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1291257764921817025867217 968443323691362769400413)
          ·
            refine ⟨363166246384261038525155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 968443323691362769400413 363166246384261038525155)
            ·
              refine ⟨544749369576391557787733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363166246384261038525155 544749369576391557787733)
              ·
                refine ⟨6383781674723338567825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 544749369576391557787733 6383781674723338567825)
                ·
                  rfl

theorem cell22_167837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 8].length) (baseStart_167837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167837 prefixEnd_167837 := by exact prefixLift 167837
  have htrace : WordTrace (prefixWord ++ tailWord_167837) baseStart_167837 baseEnd_167837 := by
    simpa [prefixWord, tailWord_167837, baseEnd_167837] using wordTrace_append hprefix tailTrace_167837
  have hstable : (prefixWord ++ tailWord_167837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167837).length < 2 ^ (prefixWord ++ tailWord_167837).sum := by decide
  have hdescent : baseEnd_167837 < baseStart_167837 := by decide
  rcases family_descends (prefixWord ++ tailWord_167837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167860 : List Nat := [2, 5, 2, 1, 2, 1, 3, 2, 4]
def baseStart_167860 : Nat := 118140960795 + 167860 * 2 ^ 59
def prefixEnd_167860 : Nat := 4983230072969 + 3 ^ 40 * 167860 * 2
def baseEnd_167860 : Nat := 19153969480848551261785

theorem tailTrace_167860 : CollatzResearch.WordTrace tailWord_167860 prefixEnd_167860 19153969480848551261785 := by
  unfold tailWord_167860
  simp only [CollatzResearch.WordTrace]
  refine ⟨3061178585939681525358517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4081571447919575367144689 3061178585939681525358517)
  ·
    refine ⟨286985492431845143002361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3061178585939681525358517 286985492431845143002361)
    ·
      refine ⟨215239119323883857251771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286985492431845143002361 215239119323883857251771)
      ·
        refine ⟨322858678985825785877657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215239119323883857251771 322858678985825785877657)
        ·
          refine ⟨242144009239369339408243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322858678985825785877657 242144009239369339408243)
          ·
            refine ⟨363216013859054009112365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242144009239369339408243 363216013859054009112365)
            ·
              refine ⟨136206005197145253417137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 363216013859054009112365 136206005197145253417137)
              ·
                refine ⟨102154503897858940062853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136206005197145253417137 102154503897858940062853)
                ·
                  refine ⟨19153969480848551261785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102154503897858940062853 19153969480848551261785)
                  ·
                    rfl

theorem cell22_167860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_167860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167860 prefixEnd_167860 := by exact prefixLift 167860
  have htrace : WordTrace (prefixWord ++ tailWord_167860) baseStart_167860 baseEnd_167860 := by
    simpa [prefixWord, tailWord_167860, baseEnd_167860] using wordTrace_append hprefix tailTrace_167860
  have hstable : (prefixWord ++ tailWord_167860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167860).length < 2 ^ (prefixWord ++ tailWord_167860).sum := by decide
  have hdescent : baseEnd_167860 < baseStart_167860 := by decide
  rcases family_descends (prefixWord ++ tailWord_167860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167993 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 1, 5]
def baseStart_167993 : Nat := 118140960795 + 167993 * 2 ^ 59
def prefixEnd_167993 : Nat := 4983230072969 + 3 ^ 40 * 167993 * 2
def baseEnd_167993 : Nat := 57507437060577640209947

theorem tailTrace_167993 : CollatzResearch.WordTrace tailWord_167993 prefixEnd_167993 57507437060577640209947 := by
  unfold tailWord_167993
  simp only [CollatzResearch.WordTrace]
  refine ⟨6127208080397526765308633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4084805386931684510205755 6127208080397526765308633)
  ·
    refine ⟨4595406060298145073981475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6127208080397526765308633 4595406060298145073981475)
    ·
      refine ⟨6893109090447217610972213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4595406060298145073981475 6893109090447217610972213)
      ·
        refine ⟨646228977229426651028645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6893109090447217610972213 646228977229426651028645)
        ·
          refine ⟨121167933230517497067871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 646228977229426651028645 121167933230517497067871)
          ·
            refine ⟨181751899845776245601807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121167933230517497067871 181751899845776245601807)
            ·
              refine ⟨272627849768664368402711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181751899845776245601807 272627849768664368402711)
              ·
                refine ⟨408941774652996552604067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272627849768664368402711 408941774652996552604067)
                ·
                  refine ⟨613412661979494828906101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 408941774652996552604067 613412661979494828906101)
                  ·
                    refine ⟨57507437060577640209947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 613412661979494828906101 57507437060577640209947)
                    ·
                      rfl

theorem cell22_167993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 1, 5].length) (baseStart_167993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_167993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_167993 prefixEnd_167993 := by exact prefixLift 167993
  have htrace : WordTrace (prefixWord ++ tailWord_167993) baseStart_167993 baseEnd_167993 := by
    simpa [prefixWord, tailWord_167993, baseEnd_167993] using wordTrace_append hprefix tailTrace_167993
  have hstable : (prefixWord ++ tailWord_167993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167993).length < 2 ^ (prefixWord ++ tailWord_167993).sum := by decide
  have hdescent : baseEnd_167993 < baseStart_167993 := by decide
  rcases family_descends (prefixWord ++ tailWord_167993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168006 : List Nat := [6, 1, 1, 1, 1, 1, 3, 8]
def baseStart_168006 : Nat := 118140960795 + 168006 * 2 ^ 59
def prefixEnd_168006 : Nat := 4983230072969 + 3 ^ 40 * 168006 * 2
def baseEnd_168006 : Nat := 6390209691805548848323

theorem tailTrace_168006 : CollatzResearch.WordTrace tailWord_168006 prefixEnd_168006 6390209691805548848323 := by
  unfold tailWord_168006
  simp only [CollatzResearch.WordTrace]
  refine ⟨191490069667200937047871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4085121486233619990354581 191490069667200937047871)
  ·
    refine ⟨287235104500801405571807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191490069667200937047871 287235104500801405571807)
    ·
      refine ⟨430852656751202108357711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287235104500801405571807 430852656751202108357711)
      ·
        refine ⟨646278985126803162536567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430852656751202108357711 646278985126803162536567)
        ·
          refine ⟨969418477690204743804851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646278985126803162536567 969418477690204743804851)
          ·
            refine ⟨1454127716535307115707277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 969418477690204743804851 1454127716535307115707277)
            ·
              refine ⟨545297893700740168390229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1454127716535307115707277 545297893700740168390229)
              ·
                refine ⟨6390209691805548848323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 545297893700740168390229 6390209691805548848323)
                ·
                  rfl

theorem cell22_168006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_168006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168006 prefixEnd_168006 := by exact prefixLift 168006
  have htrace : WordTrace (prefixWord ++ tailWord_168006) baseStart_168006 baseEnd_168006 := by
    simpa [prefixWord, tailWord_168006, baseEnd_168006] using wordTrace_append hprefix tailTrace_168006
  have hstable : (prefixWord ++ tailWord_168006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168006).length < 2 ^ (prefixWord ++ tailWord_168006).sum := by decide
  have hdescent : baseEnd_168006 < baseStart_168006 := by decide
  rcases family_descends (prefixWord ++ tailWord_168006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168154 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 1, 8]
def baseStart_168154 : Nat := 118140960795 + 168154 * 2 ^ 59
def prefixEnd_168154 : Nat := 4983230072969 + 3 ^ 40 * 168154 * 2
def baseEnd_168154 : Nat := 57562550650826886934453

theorem tailTrace_168154 : CollatzResearch.WordTrace tailWord_168154 prefixEnd_168154 57562550650826886934453 := by
  unfold tailWord_168154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1533270058203562815479879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4088720155209500841279677 1533270058203562815479879)
  ·
    refine ⟨2299905087305344223219819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1533270058203562815479879 2299905087305344223219819)
    ·
      refine ⟨3449857630958016334829729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2299905087305344223219819 3449857630958016334829729)
      ·
        refine ⟨2587393223218512251122297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3449857630958016334829729 2587393223218512251122297)
        ·
          refine ⟨1940544917413884188341723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2587393223218512251122297 1940544917413884188341723)
          ·
            refine ⟨2910817376120826282512585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940544917413884188341723 2910817376120826282512585)
            ·
              refine ⟨2183113032090619711884439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2910817376120826282512585 2183113032090619711884439)
              ·
                refine ⟨3274669548135929567826659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2183113032090619711884439 3274669548135929567826659)
                ·
                  refine ⟨4912004322203894351739989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3274669548135929567826659 4912004322203894351739989)
                  ·
                    refine ⟨57562550650826886934453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4912004322203894351739989 57562550650826886934453)
                    ·
                      rfl

theorem cell22_168154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_168154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168154 prefixEnd_168154 := by exact prefixLift 168154
  have htrace : WordTrace (prefixWord ++ tailWord_168154) baseStart_168154 baseEnd_168154 := by
    simpa [prefixWord, tailWord_168154, baseEnd_168154] using wordTrace_append hprefix tailTrace_168154
  have hstable : (prefixWord ++ tailWord_168154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168154).length < 2 ^ (prefixWord ++ tailWord_168154).sum := by decide
  have hdescent : baseEnd_168154 < baseStart_168154 := by decide
  rcases family_descends (prefixWord ++ tailWord_168154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168184 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 1, 7]
def baseStart_168184 : Nat := 118140960795 + 168184 * 2 ^ 59
def prefixEnd_168184 : Nat := 4983230072969 + 3 ^ 40 * 168184 * 2
def baseEnd_168184 : Nat := 57572820263916808684361

theorem tailTrace_168184 : CollatzResearch.WordTrace tailWord_168184 prefixEnd_168184 57572820263916808684361 := by
  unfold tailWord_168184
  simp only [CollatzResearch.WordTrace]
  refine ⟨3067087211352783192755803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4089449615137044257007737 3067087211352783192755803)
  ·
    refine ⟨4600630817029174789133705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3067087211352783192755803 4600630817029174789133705)
    ·
      refine ⟨3450473112771881091850279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4600630817029174789133705 3450473112771881091850279)
      ·
        refine ⟨5175709669157821637775419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3450473112771881091850279 5175709669157821637775419)
        ·
          refine ⟨7763564503736732456663129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5175709669157821637775419 7763564503736732456663129)
          ·
            refine ⟨5822673377802549342497347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7763564503736732456663129 5822673377802549342497347)
            ·
              refine ⟨8734010066703824013746021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5822673377802549342497347 8734010066703824013746021)
              ·
                refine ⟨1637626887506967002577379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8734010066703824013746021 1637626887506967002577379)
                ·
                  refine ⟨2456440331260450503866069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637626887506967002577379 2456440331260450503866069)
                  ·
                    refine ⟨57572820263916808684361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2456440331260450503866069 57572820263916808684361)
                    ·
                      rfl

theorem cell22_168184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_168184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168184 prefixEnd_168184 := by exact prefixLift 168184
  have htrace : WordTrace (prefixWord ++ tailWord_168184) baseStart_168184 baseEnd_168184 := by
    simpa [prefixWord, tailWord_168184, baseEnd_168184] using wordTrace_append hprefix tailTrace_168184
  have hstable : (prefixWord ++ tailWord_168184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168184).length < 2 ^ (prefixWord ++ tailWord_168184).sum := by decide
  have hdescent : baseEnd_168184 < baseStart_168184 := by decide
  rcases family_descends (prefixWord ++ tailWord_168184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168216 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 3, 4]
def baseStart_168216 : Nat := 118140960795 + 168216 * 2 ^ 59
def prefixEnd_168216 : Nat := 4983230072969 + 3 ^ 40 * 168216 * 2
def baseEnd_168216 : Nat := 57583774517879391884263

theorem tailTrace_168216 : CollatzResearch.WordTrace tailWord_168216 prefixEnd_168216 57583774517879391884263 := by
  unfold tailWord_168216
  simp only [CollatzResearch.WordTrace]
  refine ⟨3067670779294817925338251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4090227705726423900451001 3067670779294817925338251)
  ·
    refine ⟨4601506168942226888007377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3067670779294817925338251 4601506168942226888007377)
    ·
      refine ⟨3451129626706670166005533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4601506168942226888007377 3451129626706670166005533)
      ·
        refine ⟨1294173610015001312252075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3451129626706670166005533 1294173610015001312252075)
        ·
          refine ⟨1941260415022501968378113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294173610015001312252075 1941260415022501968378113)
          ·
            refine ⟨1455945311266876476283585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1941260415022501968378113 1455945311266876476283585)
            ·
              refine ⟨1091958983450157357212689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1455945311266876476283585 1091958983450157357212689)
              ·
                refine ⟨818969237587618017909517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091958983450157357212689 818969237587618017909517)
                ·
                  refine ⟨307113464095356756716069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 818969237587618017909517 307113464095356756716069)
                  ·
                    refine ⟨57583774517879391884263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 307113464095356756716069 57583774517879391884263)
                    ·
                      rfl

theorem cell22_168216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_168216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168216 prefixEnd_168216 := by exact prefixLift 168216
  have htrace : WordTrace (prefixWord ++ tailWord_168216) baseStart_168216 baseEnd_168216 := by
    simpa [prefixWord, tailWord_168216, baseEnd_168216] using wordTrace_append hprefix tailTrace_168216
  have hstable : (prefixWord ++ tailWord_168216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168216).length < 2 ^ (prefixWord ++ tailWord_168216).sum := by decide
  have hdescent : baseEnd_168216 < baseStart_168216 := by decide
  rcases family_descends (prefixWord ++ tailWord_168216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168250 : List Nat := [3, 1, 1, 1, 4, 3, 3, 1, 1, 4]
def baseStart_168250 : Nat := 118140960795 + 168250 * 2 ^ 59
def prefixEnd_168250 : Nat := 4983230072969 + 3 ^ 40 * 168250 * 2
def baseEnd_168250 : Nat := 57595413412714636534159

theorem tailTrace_168250 : CollatzResearch.WordTrace tailWord_168250 prefixEnd_168250 57595413412714636534159 := by
  unfold tailWord_168250
  simp only [CollatzResearch.WordTrace]
  refine ⟨1534145410116614914353551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4091054426977639771609469 1534145410116614914353551)
  ·
    refine ⟨2301218115174922371530327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1534145410116614914353551 2301218115174922371530327)
    ·
      refine ⟨3451827172762383557295491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2301218115174922371530327 3451827172762383557295491)
      ·
        refine ⟨5177740759143575335943237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3451827172762383557295491 5177740759143575335943237)
        ·
          refine ⟨970826392339420375489357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5177740759143575335943237 970826392339420375489357)
          ·
            refine ⟨364059897127282640808509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 970826392339420375489357 364059897127282640808509)
            ·
              refine ⟨136522461422730990303191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 364059897127282640808509 136522461422730990303191)
              ·
                refine ⟨204783692134096485454787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136522461422730990303191 204783692134096485454787)
                ·
                  refine ⟨307175538201144728182181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204783692134096485454787 307175538201144728182181)
                  ·
                    refine ⟨57595413412714636534159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 307175538201144728182181 57595413412714636534159)
                    ·
                      rfl

theorem cell22_168250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_168250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168250 prefixEnd_168250 := by exact prefixLift 168250
  have htrace : WordTrace (prefixWord ++ tailWord_168250) baseStart_168250 baseEnd_168250 := by
    simpa [prefixWord, tailWord_168250, baseEnd_168250] using wordTrace_append hprefix tailTrace_168250
  have hstable : (prefixWord ++ tailWord_168250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168250).length < 2 ^ (prefixWord ++ tailWord_168250).sum := by decide
  have hdescent : baseEnd_168250 < baseStart_168250 := by decide
  rcases family_descends (prefixWord ++ tailWord_168250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168293 : List Nat := [1, 3, 1, 3, 1, 4, 3, 6]
def baseStart_168293 : Nat := 118140960795 + 168293 * 2 ^ 59
def prefixEnd_168293 : Nat := 4983230072969 + 3 ^ 40 * 168293 * 2
def baseEnd_168293 : Nat := 6401125910164095301003

theorem tailTrace_168293 : CollatzResearch.WordTrace tailWord_168293 prefixEnd_168293 6401125910164095301003 := by
  unfold tailWord_168293
  simp only [CollatzResearch.WordTrace]
  refine ⟨6138149979310678001229533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4092099986207118667486355 6138149979310678001229533)
  ·
    refine ⟨2301806242241504250461075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6138149979310678001229533 2301806242241504250461075)
    ·
      refine ⟨3452709363362256375691613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2301806242241504250461075 3452709363362256375691613)
      ·
        refine ⟨1294766011260846140884355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3452709363362256375691613 1294766011260846140884355)
        ·
          refine ⟨1942149016891269211326533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294766011260846140884355 1942149016891269211326533)
          ·
            refine ⟨364152940667112977123725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1942149016891269211326533 364152940667112977123725)
            ·
              refine ⟨136557352750167366421397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 364152940667112977123725 136557352750167366421397)
              ·
                refine ⟨6401125910164095301003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136557352750167366421397 6401125910164095301003)
                ·
                  rfl

theorem cell22_168293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 6].length) (baseStart_168293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168293 prefixEnd_168293 := by exact prefixLift 168293
  have htrace : WordTrace (prefixWord ++ tailWord_168293) baseStart_168293 baseEnd_168293 := by
    simpa [prefixWord, tailWord_168293, baseEnd_168293] using wordTrace_append hprefix tailTrace_168293
  have hstable : (prefixWord ++ tailWord_168293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168293).length < 2 ^ (prefixWord ++ tailWord_168293).sum := by decide
  have hdescent : baseEnd_168293 < baseStart_168293 := by decide
  rcases family_descends (prefixWord ++ tailWord_168293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168295 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 2, 4]
def baseStart_168295 : Nat := 118140960795 + 168295 * 2 ^ 59
def prefixEnd_168295 : Nat := 4983230072969 + 3 ^ 40 * 168295 * 2
def baseEnd_168295 : Nat := 57610817832349519159021

theorem tailTrace_168295 : CollatzResearch.WordTrace tailWord_168295 prefixEnd_168295 57610817832349519159021 := by
  unfold tailWord_168295
  simp only [CollatzResearch.WordTrace]
  refine ⟨6138222925303432342802339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4092148616868954895201559 6138222925303432342802339)
  ·
    refine ⟨9207334387955148514203509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6138222925303432342802339 9207334387955148514203509)
    ·
      refine ⟨863187598870795173206579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9207334387955148514203509 863187598870795173206579)
      ·
        refine ⟨1294781398306192759809869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 863187598870795173206579 1294781398306192759809869)
        ·
          refine ⟨485543024364822284928701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1294781398306192759809869 485543024364822284928701)
          ·
            refine ⟨182078634136808356848263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 485543024364822284928701 182078634136808356848263)
            ·
              refine ⟨273117951205212535272395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182078634136808356848263 273117951205212535272395)
              ·
                refine ⟨409676926807818802908593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273117951205212535272395 409676926807818802908593)
                ·
                  refine ⟨307257695105864102181445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 409676926807818802908593 307257695105864102181445)
                  ·
                    refine ⟨57610817832349519159021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 307257695105864102181445 57610817832349519159021)
                    ·
                      rfl

theorem cell22_168295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_168295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168295 prefixEnd_168295 := by exact prefixLift 168295
  have htrace : WordTrace (prefixWord ++ tailWord_168295) baseStart_168295 baseEnd_168295 := by
    simpa [prefixWord, tailWord_168295, baseEnd_168295] using wordTrace_append hprefix tailTrace_168295
  have hstable : (prefixWord ++ tailWord_168295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168295).length < 2 ^ (prefixWord ++ tailWord_168295).sum := by decide
  have hdescent : baseEnd_168295 < baseStart_168295 := by decide
  rcases family_descends (prefixWord ++ tailWord_168295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168310 : List Nat := [5, 1, 1, 4, 1, 1, 9]
def baseStart_168310 : Nat := 118140960795 + 168310 * 2 ^ 59
def prefixEnd_168310 : Nat := 4983230072969 + 3 ^ 40 * 168310 * 2
def baseEnd_168310 : Nat := 2133924171810906667925

theorem tailTrace_168310 : CollatzResearch.WordTrace tailWord_168310 prefixEnd_168310 2133924171810906667925 := by
  unfold tailWord_168310
  simp only [CollatzResearch.WordTrace]
  refine ⟨383673126265568119037399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4092513346832726603065589 383673126265568119037399)
  ·
    refine ⟨575509689398352178556099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 383673126265568119037399 575509689398352178556099)
    ·
      refine ⟨863264534097528267834149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 575509689398352178556099 863264534097528267834149)
      ·
        refine ⟨161862100143286550218903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 863264534097528267834149 161862100143286550218903)
        ·
          refine ⟨242793150214929825328355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161862100143286550218903 242793150214929825328355)
          ·
            refine ⟨364189725322394737992533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242793150214929825328355 364189725322394737992533)
            ·
              refine ⟨2133924171810906667925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 364189725322394737992533 2133924171810906667925)
              ·
                rfl

theorem cell22_168310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 9].length) (baseStart_168310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168310 prefixEnd_168310 := by exact prefixLift 168310
  have htrace : WordTrace (prefixWord ++ tailWord_168310) baseStart_168310 baseEnd_168310 := by
    simpa [prefixWord, tailWord_168310, baseEnd_168310] using wordTrace_append hprefix tailTrace_168310
  have hstable : (prefixWord ++ tailWord_168310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168310).length < 2 ^ (prefixWord ++ tailWord_168310).sum := by decide
  have hdescent : baseEnd_168310 < baseStart_168310 := by decide
  rcases family_descends (prefixWord ++ tailWord_168310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168359 : List Nat := [1, 1, 6, 1, 1, 4, 1, 3, 1, 3]
def baseStart_168359 : Nat := 118140960795 + 168359 * 2 ^ 59
def prefixEnd_168359 : Nat := 4983230072969 + 3 ^ 40 * 168359 * 2
def baseEnd_168359 : Nat := 57632726340274685558825

theorem tailTrace_168359 : CollatzResearch.WordTrace tailWord_168359 prefixEnd_168359 57632726340274685558825 := by
  unfold tailWord_168359
  simp only [CollatzResearch.WordTrace]
  refine ⟨6140557197071571273132131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4093704798047714182088087 6140557197071571273132131)
  ·
    refine ⟨9210835795607356909698197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6140557197071571273132131 9210835795607356909698197)
    ·
      refine ⟨431757927919094855142103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9210835795607356909698197 431757927919094855142103)
      ·
        refine ⟨647636891878642282713155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431757927919094855142103 647636891878642282713155)
        ·
          refine ⟨971455337817963424069733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647636891878642282713155 971455337817963424069733)
          ·
            refine ⟨182147875840868142013075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 971455337817963424069733 182147875840868142013075)
            ·
              refine ⟨273221813761302213019613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182147875840868142013075 273221813761302213019613)
              ·
                refine ⟨102458180160488329882355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 273221813761302213019613 102458180160488329882355)
                ·
                  refine ⟨153687270240732494823533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102458180160488329882355 153687270240732494823533)
                  ·
                    refine ⟨57632726340274685558825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153687270240732494823533 57632726340274685558825)
                    ·
                      rfl

theorem cell22_168359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_168359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168359 prefixEnd_168359 := by exact prefixLift 168359
  have htrace : WordTrace (prefixWord ++ tailWord_168359) baseStart_168359 baseEnd_168359 := by
    simpa [prefixWord, tailWord_168359, baseEnd_168359] using wordTrace_append hprefix tailTrace_168359
  have hstable : (prefixWord ++ tailWord_168359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168359).length < 2 ^ (prefixWord ++ tailWord_168359).sum := by decide
  have hdescent : baseEnd_168359 < baseStart_168359 := by decide
  rcases family_descends (prefixWord ++ tailWord_168359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168398 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_168398 : Nat := 118140960795 + 168398 * 2 ^ 59
def prefixEnd_168398 : Nat := 4983230072969 + 3 ^ 40 * 168398 * 2
def baseEnd_168398 : Nat := 57646076837291583833705

theorem tailTrace_168398 : CollatzResearch.WordTrace tailWord_168398 prefixEnd_168398 57646076837291583833705 := by
  unfold tailWord_168398
  simp only [CollatzResearch.WordTrace]
  refine ⟨767747455491285116725231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4094653095953520622534565 767747455491285116725231)
  ·
    refine ⟨1151621183236927675087847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 767747455491285116725231 1151621183236927675087847)
    ·
      refine ⟨1727431774855391512631771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1151621183236927675087847 1727431774855391512631771)
      ·
        refine ⟨2591147662283087268947657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1727431774855391512631771 2591147662283087268947657)
        ·
          refine ⟨1943360746712315451710743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2591147662283087268947657 1943360746712315451710743)
          ·
            refine ⟨2915041120068473177566115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1943360746712315451710743 2915041120068473177566115)
            ·
              refine ⟨4372561680102709766349173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2915041120068473177566115 4372561680102709766349173)
              ·
                refine ⟨409927657509629040595235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4372561680102709766349173 409927657509629040595235)
                ·
                  refine ⟨614891486264443560892853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409927657509629040595235 614891486264443560892853)
                  ·
                    refine ⟨57646076837291583833705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 614891486264443560892853 57646076837291583833705)
                    ·
                      rfl

theorem cell22_168398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_168398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168398 prefixEnd_168398 := by exact prefixLift 168398
  have htrace : WordTrace (prefixWord ++ tailWord_168398) baseStart_168398 baseEnd_168398 := by
    simpa [prefixWord, tailWord_168398, baseEnd_168398] using wordTrace_append hprefix tailTrace_168398
  have hstable : (prefixWord ++ tailWord_168398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168398).length < 2 ^ (prefixWord ++ tailWord_168398).sum := by decide
  have hdescent : baseEnd_168398 < baseStart_168398 := by decide
  rcases family_descends (prefixWord ++ tailWord_168398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168402 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 3, 4]
def baseStart_168402 : Nat := 118140960795 + 168402 * 2 ^ 59
def prefixEnd_168402 : Nat := 4983230072969 + 3 ^ 40 * 168402 * 2
def baseEnd_168402 : Nat := 57647446119036906733693

theorem tailTrace_168402 : CollatzResearch.WordTrace tailWord_168402 prefixEnd_168402 57647446119036906733693 := by
  unfold tailWord_168402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1535531383978947404236865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4094750357277193077964973 1535531383978947404236865)
  ·
    refine ⟨1151648537984210553177649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1535531383978947404236865 1151648537984210553177649)
    ·
      refine ⟨863736403488157914883237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1151648537984210553177649 863736403488157914883237)
      ·
        refine ⟨161950575654029609040607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 863736403488157914883237 161950575654029609040607)
        ·
          refine ⟨242925863481044413560911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161950575654029609040607 242925863481044413560911)
          ·
            refine ⟨364388795221566620341367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242925863481044413560911 364388795221566620341367)
            ·
              refine ⟨546583192832349930512051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364388795221566620341367 546583192832349930512051)
              ·
                refine ⟨819874789248524895768077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 546583192832349930512051 819874789248524895768077)
                ·
                  refine ⟨307453045968196835913029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819874789248524895768077 307453045968196835913029)
                  ·
                    refine ⟨57647446119036906733693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 307453045968196835913029 57647446119036906733693)
                    ·
                      rfl

theorem cell22_168402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_168402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168402 prefixEnd_168402 := by exact prefixLift 168402
  have htrace : WordTrace (prefixWord ++ tailWord_168402) baseStart_168402 baseEnd_168402 := by
    simpa [prefixWord, tailWord_168402, baseEnd_168402] using wordTrace_append hprefix tailTrace_168402
  have hstable : (prefixWord ++ tailWord_168402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168402).length < 2 ^ (prefixWord ++ tailWord_168402).sum := by decide
  have hdescent : baseEnd_168402 < baseStart_168402 := by decide
  rcases family_descends (prefixWord ++ tailWord_168402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168430 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_168430 : Nat := 118140960795 + 168430 * 2 ^ 59
def prefixEnd_168430 : Nat := 4983230072969 + 3 ^ 40 * 168430 * 2
def baseEnd_168430 : Nat := 57657031091254167033607

theorem tailTrace_168430 : CollatzResearch.WordTrace tailWord_168430 prefixEnd_168430 57657031091254167033607 := by
  unfold tailWord_168430
  simp only [CollatzResearch.WordTrace]
  refine ⟨767893347476793799870843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4095431186542900265977829 767893347476793799870843)
  ·
    refine ⟨1151840021215190699806265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 767893347476793799870843 1151840021215190699806265)
    ·
      refine ⟨863880015911393024854699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1151840021215190699806265 863880015911393024854699)
      ·
        refine ⟨1295820023867089537282049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 863880015911393024854699 1295820023867089537282049)
        ·
          refine ⟨971865017900317152961537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1295820023867089537282049 971865017900317152961537)
          ·
            refine ⟨728898763425237864721153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 971865017900317152961537 728898763425237864721153)
            ·
              refine ⟨546674072568928398540865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 728898763425237864721153 546674072568928398540865)
              ·
                refine ⟨410005554426696298905649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546674072568928398540865 410005554426696298905649)
                ·
                  refine ⟨307504165820022224179237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410005554426696298905649 307504165820022224179237)
                  ·
                    refine ⟨57657031091254167033607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 307504165820022224179237 57657031091254167033607)
                    ·
                      rfl

theorem cell22_168430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_168430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168430 prefixEnd_168430 := by exact prefixLift 168430
  have htrace : WordTrace (prefixWord ++ tailWord_168430) baseStart_168430 baseEnd_168430 := by
    simpa [prefixWord, tailWord_168430, baseEnd_168430] using wordTrace_append hprefix tailTrace_168430
  have hstable : (prefixWord ++ tailWord_168430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168430).length < 2 ^ (prefixWord ++ tailWord_168430).sum := by decide
  have hdescent : baseEnd_168430 < baseStart_168430 := by decide
  rcases family_descends (prefixWord ++ tailWord_168430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168458 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 2, 6]
def baseStart_168458 : Nat := 118140960795 + 168458 * 2 ^ 59
def prefixEnd_168458 : Nat := 4983230072969 + 3 ^ 40 * 168458 * 2
def baseEnd_168458 : Nat := 57666616063471427333521

theorem tailTrace_168458 : CollatzResearch.WordTrace tailWord_168458 prefixEnd_168458 57666616063471427333521 := by
  unfold tailWord_168458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536042005928227795246507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4096112015808607453990685 1536042005928227795246507)
  ·
    refine ⟨2304063008892341692869761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1536042005928227795246507 2304063008892341692869761)
    ·
      refine ⟨1728047256669256269652321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2304063008892341692869761 1728047256669256269652321)
      ·
        refine ⟨1296035442501942202239241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1728047256669256269652321 1296035442501942202239241)
        ·
          refine ⟨972026581876456651679431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1296035442501942202239241 972026581876456651679431)
          ·
            refine ⟨1458039872814684977519147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972026581876456651679431 1458039872814684977519147)
            ·
              refine ⟨2187059809222027466278721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1458039872814684977519147 2187059809222027466278721)
              ·
                refine ⟨1640294856916520599709041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187059809222027466278721 1640294856916520599709041)
                ·
                  refine ⟨1230221142687390449781781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1640294856916520599709041 1230221142687390449781781)
                  ·
                    refine ⟨57666616063471427333521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1230221142687390449781781 57666616063471427333521)
                    ·
                      rfl

theorem cell22_168458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_168458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168458 prefixEnd_168458 := by exact prefixLift 168458
  have htrace : WordTrace (prefixWord ++ tailWord_168458) baseStart_168458 baseEnd_168458 := by
    simpa [prefixWord, tailWord_168458, baseEnd_168458] using wordTrace_append hprefix tailTrace_168458
  have hstable : (prefixWord ++ tailWord_168458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168458).length < 2 ^ (prefixWord ++ tailWord_168458).sum := by decide
  have hdescent : baseEnd_168458 < baseStart_168458 := by decide
  rcases family_descends (prefixWord ++ tailWord_168458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168460 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 5, 3]
def baseStart_168460 : Nat := 118140960795 + 168460 * 2 ^ 59
def prefixEnd_168460 : Nat := 4983230072969 + 3 ^ 40 * 168460 * 2
def baseEnd_168460 : Nat := 57667300704344088783515

theorem tailTrace_168460 : CollatzResearch.WordTrace tailWord_168460 prefixEnd_168460 57667300704344088783515 := by
  unfold tailWord_168460
  simp only [CollatzResearch.WordTrace]
  refine ⟨3072120484852832761279417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4096160646470443681705889 3072120484852832761279417)
  ·
    refine ⟨2304090363639624570959563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3072120484852832761279417 2304090363639624570959563)
    ·
      refine ⟨3456135545459436856439345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2304090363639624570959563 3456135545459436856439345)
      ·
        refine ⟨2592101659094577642329509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3456135545459436856439345 2592101659094577642329509)
        ·
          refine ⟨486019061080233307936783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2592101659094577642329509 486019061080233307936783)
          ·
            refine ⟨729028591620349961905175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486019061080233307936783 729028591620349961905175)
            ·
              refine ⟨1093542887430524942857763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 729028591620349961905175 1093542887430524942857763)
              ·
                refine ⟨1640314331145787414286645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093542887430524942857763 1640314331145787414286645)
                ·
                  refine ⟨153779468544917570089373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1640314331145787414286645 153779468544917570089373)
                  ·
                    refine ⟨57667300704344088783515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153779468544917570089373 57667300704344088783515)
                    ·
                      rfl

theorem cell22_168460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_168460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168460 prefixEnd_168460 := by exact prefixLift 168460
  have htrace : WordTrace (prefixWord ++ tailWord_168460) baseStart_168460 baseEnd_168460 := by
    simpa [prefixWord, tailWord_168460, baseEnd_168460] using wordTrace_append hprefix tailTrace_168460
  have hstable : (prefixWord ++ tailWord_168460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168460).length < 2 ^ (prefixWord ++ tailWord_168460).sum := by decide
  have hdescent : baseEnd_168460 < baseStart_168460 := by decide
  rcases family_descends (prefixWord ++ tailWord_168460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168490 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 7]
def baseStart_168490 : Nat := 118140960795 + 168490 * 2 ^ 59
def prefixEnd_168490 : Nat := 4983230072969 + 3 ^ 40 * 168490 * 2
def baseEnd_168490 : Nat := 19225856772478003511141

theorem tailTrace_168490 : CollatzResearch.WordTrace tailWord_168490 prefixEnd_168490 19225856772478003511141 := by
  unfold tailWord_168490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536333789899245161537731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4096890106397987097433949 1536333789899245161537731)
  ·
    refine ⟨2304500684848867742306597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1536333789899245161537731 2304500684848867742306597)
    ·
      refine ⟨432093878409162701682487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2304500684848867742306597 432093878409162701682487)
      ·
        refine ⟨648140817613744052523731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432093878409162701682487 648140817613744052523731)
        ·
          refine ⟨972211226420616078785597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648140817613744052523731 972211226420616078785597)
          ·
            refine ⟨364579209907731029544599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 972211226420616078785597 364579209907731029544599)
            ·
              refine ⟨546868814861596544316899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364579209907731029544599 546868814861596544316899)
              ·
                refine ⟨820303222292394816475349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 546868814861596544316899 820303222292394816475349)
                ·
                  refine ⟨19225856772478003511141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 820303222292394816475349 19225856772478003511141)
                  ·
                    rfl

theorem cell22_168490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_168490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168490 prefixEnd_168490 := by exact prefixLift 168490
  have htrace : WordTrace (prefixWord ++ tailWord_168490) baseStart_168490 baseEnd_168490 := by
    simpa [prefixWord, tailWord_168490, baseEnd_168490] using wordTrace_append hprefix tailTrace_168490
  have hstable : (prefixWord ++ tailWord_168490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168490).length < 2 ^ (prefixWord ++ tailWord_168490).sum := by decide
  have hdescent : baseEnd_168490 < baseStart_168490 := by decide
  rcases family_descends (prefixWord ++ tailWord_168490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168494 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 3, 3]
def baseStart_168494 : Nat := 118140960795 + 168494 * 2 ^ 59
def prefixEnd_168494 : Nat := 4983230072969 + 3 ^ 40 * 168494 * 2
def baseEnd_168494 : Nat := 57678939599179333433411

theorem tailTrace_168494 : CollatzResearch.WordTrace tailWord_168494 prefixEnd_168494 57678939599179333433411 := by
  unfold tailWord_168494
  simp only [CollatzResearch.WordTrace]
  refine ⟨768185131447811166162067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4096987367721659552864357 768185131447811166162067)
  ·
    refine ⟨1152277697171716749243101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 768185131447811166162067 1152277697171716749243101)
    ·
      refine ⟨432104136439393780966163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1152277697171716749243101 432104136439393780966163)
      ·
        refine ⟨648156204659090671449245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432104136439393780966163 648156204659090671449245)
        ·
          refine ⟨243058576747159001793467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 648156204659090671449245 243058576747159001793467)
          ·
            refine ⟨364587865120738502690201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243058576747159001793467 364587865120738502690201)
            ·
              refine ⟨273440898840553877017651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364587865120738502690201 273440898840553877017651)
              ·
                refine ⟨410161348260830815526477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273440898840553877017651 410161348260830815526477)
                ·
                  refine ⟨153810505597811555822429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 410161348260830815526477 153810505597811555822429)
                  ·
                    refine ⟨57678939599179333433411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153810505597811555822429 57678939599179333433411)
                    ·
                      rfl

theorem cell22_168494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_168494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168494 prefixEnd_168494 := by exact prefixLift 168494
  have htrace : WordTrace (prefixWord ++ tailWord_168494) baseStart_168494 baseEnd_168494 := by
    simpa [prefixWord, tailWord_168494, baseEnd_168494] using wordTrace_append hprefix tailTrace_168494
  have hstable : (prefixWord ++ tailWord_168494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168494).length < 2 ^ (prefixWord ++ tailWord_168494).sum := by decide
  have hdescent : baseEnd_168494 < baseStart_168494 := by decide
  rcases family_descends (prefixWord ++ tailWord_168494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168580 : List Nat := [2, 3, 2, 1, 3, 1, 2, 8]
def baseStart_168580 : Nat := 118140960795 + 168580 * 2 ^ 59
def prefixEnd_168580 : Nat := 4983230072969 + 3 ^ 40 * 168580 * 2
def baseEnd_168580 : Nat := 6412042128522641753683

theorem tailTrace_168580 : CollatzResearch.WordTrace tailWord_168580 prefixEnd_168580 6412042128522641753683 := by
  unfold tailWord_168580
  simp only [CollatzResearch.WordTrace]
  refine ⟨3074308864635463008463597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4099078486180617344618129 3074308864635463008463597)
  ·
    refine ⟨1152865824238298628173849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3074308864635463008463597 1152865824238298628173849)
    ·
      refine ⟨864649368178723971130387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1152865824238298628173849 864649368178723971130387)
      ·
        refine ⟨1296974052268085956695581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 864649368178723971130387 1296974052268085956695581)
        ·
          refine ⟨486365269600532233760843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1296974052268085956695581 486365269600532233760843)
          ·
            refine ⟨729547904400798350641265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486365269600532233760843 729547904400798350641265)
            ·
              refine ⟨547160928300598762980949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 729547904400798350641265 547160928300598762980949)
              ·
                refine ⟨6412042128522641753683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 547160928300598762980949 6412042128522641753683)
                ·
                  rfl

theorem cell22_168580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 8].length) (baseStart_168580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168580 prefixEnd_168580 := by exact prefixLift 168580
  have htrace : WordTrace (prefixWord ++ tailWord_168580) baseStart_168580 baseEnd_168580 := by
    simpa [prefixWord, tailWord_168580, baseEnd_168580] using wordTrace_append hprefix tailTrace_168580
  have hstable : (prefixWord ++ tailWord_168580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168580).length < 2 ^ (prefixWord ++ tailWord_168580).sum := by decide
  have hdescent : baseEnd_168580 < baseStart_168580 := by decide
  rcases family_descends (prefixWord ++ tailWord_168580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168595 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 5, 3]
def baseStart_168595 : Nat := 118140960795 + 168595 * 2 ^ 59
def prefixEnd_168595 : Nat := 4983230072969 + 3 ^ 40 * 168595 * 2
def baseEnd_168595 : Nat := 57713513963248736658101

theorem tailTrace_168595 : CollatzResearch.WordTrace tailWord_168595 prefixEnd_168595 57713513963248736658101 := by
  unfold tailWord_168595
  simp only [CollatzResearch.WordTrace]
  refine ⟨6149164824216583578723239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4099443216144389052482159 6149164824216583578723239)
  ·
    refine ⟨9223747236324875368084859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6149164824216583578723239 9223747236324875368084859)
    ·
      refine ⟨13835620854487313052127289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9223747236324875368084859 13835620854487313052127289)
      ·
        refine ⟨10376715640865484789095467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13835620854487313052127289 10376715640865484789095467)
        ·
          refine ⟨15565073461298227183643201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10376715640865484789095467 15565073461298227183643201)
          ·
            refine ⟨11673805095973670387732401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15565073461298227183643201 11673805095973670387732401)
            ·
              refine ⟨8755353821980252790799301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11673805095973670387732401 8755353821980252790799301)
              ·
                refine ⟨1641628841621297398274869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8755353821980252790799301 1641628841621297398274869)
                ·
                  refine ⟨153902703901996631088269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1641628841621297398274869 153902703901996631088269)
                  ·
                    refine ⟨57713513963248736658101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153902703901996631088269 57713513963248736658101)
                    ·
                      rfl

theorem cell22_168595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 3].length) (baseStart_168595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168595 prefixEnd_168595 := by exact prefixLift 168595
  have htrace : WordTrace (prefixWord ++ tailWord_168595) baseStart_168595 baseEnd_168595 := by
    simpa [prefixWord, tailWord_168595, baseEnd_168595] using wordTrace_append hprefix tailTrace_168595
  have hstable : (prefixWord ++ tailWord_168595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168595).length < 2 ^ (prefixWord ++ tailWord_168595).sum := by decide
  have hdescent : baseEnd_168595 < baseStart_168595 := by decide
  rcases family_descends (prefixWord ++ tailWord_168595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168612 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 3, 3]
def baseStart_168612 : Nat := 118140960795 + 168612 * 2 ^ 59
def prefixEnd_168612 : Nat := 4983230072969 + 3 ^ 40 * 168612 * 2
def baseEnd_168612 : Nat := 57719333410666358983049

theorem tailTrace_168612 : CollatzResearch.WordTrace tailWord_168612 prefixEnd_168612 57719333410666358983049 := by
  unfold tailWord_168612
  simp only [CollatzResearch.WordTrace]
  refine ⟨3074892432577497741046045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4099856576769996988061393 3074892432577497741046045)
  ·
    refine ⟨1153084662216561652892267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3074892432577497741046045 1153084662216561652892267)
    ·
      refine ⟨1729626993324842479338401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1153084662216561652892267 1729626993324842479338401)
      ·
        refine ⟨1297220244993631859503801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1729626993324842479338401 1297220244993631859503801)
        ·
          refine ⟨972915183745223894627851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1297220244993631859503801 972915183745223894627851)
          ·
            refine ⟨1459372775617835841941777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972915183745223894627851 1459372775617835841941777)
            ·
              refine ⟨1094529581713376881456333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1459372775617835841941777 1094529581713376881456333)
              ·
                refine ⟨410448593142516330546125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1094529581713376881456333 410448593142516330546125)
                ·
                  refine ⟨153918222428443623954797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 410448593142516330546125 153918222428443623954797)
                  ·
                    refine ⟨57719333410666358983049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153918222428443623954797 57719333410666358983049)
                    ·
                      rfl

theorem cell22_168612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_168612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168612 prefixEnd_168612 := by exact prefixLift 168612
  have htrace : WordTrace (prefixWord ++ tailWord_168612) baseStart_168612 baseEnd_168612 := by
    simpa [prefixWord, tailWord_168612, baseEnd_168612] using wordTrace_append hprefix tailTrace_168612
  have hstable : (prefixWord ++ tailWord_168612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168612).length < 2 ^ (prefixWord ++ tailWord_168612).sum := by decide
  have hdescent : baseEnd_168612 < baseStart_168612 := by decide
  rcases family_descends (prefixWord ++ tailWord_168612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168629 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 3, 3]
def baseStart_168629 : Nat := 118140960795 + 168629 * 2 ^ 59
def prefixEnd_168629 : Nat := 4983230072969 + 3 ^ 40 * 168629 * 2
def baseEnd_168629 : Nat := 57725152858083981307997

theorem tailTrace_168629 : CollatzResearch.WordTrace tailWord_168629 prefixEnd_168629 57725152858083981307997 := by
  unfold tailWord_168629
  simp only [CollatzResearch.WordTrace]
  refine ⟨6150404906093407385460941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4100269937395604923640627 6150404906093407385460941)
  ·
    refine ⟨2306401839785027769547853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6150404906093407385460941 2306401839785027769547853)
    ·
      refine ⟨864900689919385413580445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2306401839785027769547853 864900689919385413580445)
      ·
        refine ⟨324337758719769530092667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 864900689919385413580445 324337758719769530092667)
        ·
          refine ⟨486506638079654295139001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324337758719769530092667 486506638079654295139001)
          ·
            refine ⟨364879978559740721354251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 486506638079654295139001 364879978559740721354251)
            ·
              refine ⟨547319967839611082031377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364879978559740721354251 547319967839611082031377)
              ·
                refine ⟨410489975879708311523533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547319967839611082031377 410489975879708311523533)
                ·
                  refine ⟨153933740954890616821325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 410489975879708311523533 153933740954890616821325)
                  ·
                    refine ⟨57725152858083981307997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153933740954890616821325 57725152858083981307997)
                    ·
                      rfl

theorem cell22_168629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_168629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168629 prefixEnd_168629 := by exact prefixLift 168629
  have htrace : WordTrace (prefixWord ++ tailWord_168629) baseStart_168629 baseEnd_168629 := by
    simpa [prefixWord, tailWord_168629, baseEnd_168629] using wordTrace_append hprefix tailTrace_168629
  have hstable : (prefixWord ++ tailWord_168629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168629).length < 2 ^ (prefixWord ++ tailWord_168629).sum := by decide
  have hdescent : baseEnd_168629 < baseStart_168629 := by decide
  rcases family_descends (prefixWord ++ tailWord_168629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168732 : List Nat := [2, 2, 3, 1, 1, 4, 2, 7]
def baseStart_168732 : Nat := 118140960795 + 168732 * 2 ^ 59
def prefixEnd_168732 : Nat := 4983230072969 + 3 ^ 40 * 168732 * 2
def baseEnd_168732 : Nat := 6417823540336227331409

theorem tailTrace_168732 : CollatzResearch.WordTrace tailWord_168732 prefixEnd_168732 6417823540336227331409 := by
  unfold tailWord_168732
  simp only [CollatzResearch.WordTrace]
  refine ⟨3077080812360127988230225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4102774416480170650973633 3077080812360127988230225)
  ·
    refine ⟨2307810609270095991172669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3077080812360127988230225 2307810609270095991172669)
    ·
      refine ⟨865428978476285996689751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2307810609270095991172669 865428978476285996689751)
      ·
        refine ⟨1298143467714428995034627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865428978476285996689751 1298143467714428995034627)
        ·
          refine ⟨1947215201571643492551941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298143467714428995034627 1947215201571643492551941)
          ·
            refine ⟨365102850294683154853489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1947215201571643492551941 365102850294683154853489)
            ·
              refine ⟨273827137721012366140117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365102850294683154853489 273827137721012366140117)
              ·
                refine ⟨6417823540336227331409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 273827137721012366140117 6417823540336227331409)
                ·
                  rfl

theorem cell22_168732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 7].length) (baseStart_168732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168732 prefixEnd_168732 := by exact prefixLift 168732
  have htrace : WordTrace (prefixWord ++ tailWord_168732) baseStart_168732 baseEnd_168732 := by
    simpa [prefixWord, tailWord_168732, baseEnd_168732] using wordTrace_append hprefix tailTrace_168732
  have hstable : (prefixWord ++ tailWord_168732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168732).length < 2 ^ (prefixWord ++ tailWord_168732).sum := by decide
  have hdescent : baseEnd_168732 < baseStart_168732 := by decide
  rcases family_descends (prefixWord ++ tailWord_168732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168736 : List Nat := [2, 1, 1, 5, 1, 2, 4, 1, 2, 3]
def baseStart_168736 : Nat := 118140960795 + 168736 * 2 ^ 59
def prefixEnd_168736 : Nat := 4983230072969 + 3 ^ 40 * 168736 * 2
def baseEnd_168736 : Nat := 57761781144771368882669

theorem tailTrace_168736 : CollatzResearch.WordTrace tailWord_168736 prefixEnd_168736 57761781144771368882669 := by
  unfold tailWord_168736
  simp only [CollatzResearch.WordTrace]
  refine ⟨3077153758352882329803031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4102871677803843106404041 3077153758352882329803031)
  ·
    refine ⟨4615730637529323494704547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3077153758352882329803031 4615730637529323494704547)
    ·
      refine ⟨6923595956293985242056821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4615730637529323494704547 6923595956293985242056821)
      ·
        refine ⟨649087120902561116442827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6923595956293985242056821 649087120902561116442827)
        ·
          refine ⟨973630681353841674664241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 649087120902561116442827 973630681353841674664241)
          ·
            refine ⟨730223011015381255998181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 973630681353841674664241 730223011015381255998181)
            ·
              refine ⟨136916814565383985499659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 730223011015381255998181 136916814565383985499659)
              ·
                refine ⟨205375221848075978249489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136916814565383985499659 205375221848075978249489)
                ·
                  refine ⟨154031416386056983687117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205375221848075978249489 154031416386056983687117)
                  ·
                    refine ⟨57761781144771368882669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 154031416386056983687117 57761781144771368882669)
                    ·
                      rfl

theorem cell22_168736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 2, 3].length) (baseStart_168736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168736 prefixEnd_168736 := by exact prefixLift 168736
  have htrace : WordTrace (prefixWord ++ tailWord_168736) baseStart_168736 baseEnd_168736 := by
    simpa [prefixWord, tailWord_168736, baseEnd_168736] using wordTrace_append hprefix tailTrace_168736
  have hstable : (prefixWord ++ tailWord_168736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168736).length < 2 ^ (prefixWord ++ tailWord_168736).sum := by decide
  have hdescent : baseEnd_168736 < baseStart_168736 := by decide
  rcases family_descends (prefixWord ++ tailWord_168736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168745 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 2, 6]
def baseStart_168745 : Nat := 118140960795 + 168745 * 2 ^ 59
def prefixEnd_168745 : Nat := 4983230072969 + 3 ^ 40 * 168745 * 2
def baseEnd_168745 : Nat := 57764862028698345407641

theorem tailTrace_168745 : CollatzResearch.WordTrace tailWord_168745 prefixEnd_168745 57764862028698345407641 := by
  unfold tailWord_168745
  simp only [CollatzResearch.WordTrace]
  refine ⟨6154635773673159196683689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4103090515782106131122459 6154635773673159196683689)
  ·
    refine ⟨4615976830254869397512767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6154635773673159196683689 4615976830254869397512767)
    ·
      refine ⟨6923965245382304096269151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4615976830254869397512767 6923965245382304096269151)
      ·
        refine ⟨10385947868073456144403727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6923965245382304096269151 10385947868073456144403727)
        ·
          refine ⟨15578921802110184216605591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10385947868073456144403727 15578921802110184216605591)
          ·
            refine ⟨23368382703165276324908387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15578921802110184216605591 23368382703165276324908387)
            ·
              refine ⟨35052574054747914487362581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23368382703165276324908387 35052574054747914487362581)
              ·
                refine ⟨1643089408816308491595121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35052574054747914487362581 1643089408816308491595121)
                ·
                  refine ⟨1232317056612231368696341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1643089408816308491595121 1232317056612231368696341)
                  ·
                    refine ⟨57764862028698345407641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1232317056612231368696341 57764862028698345407641)
                    ·
                      rfl

theorem cell22_168745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_168745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168745 prefixEnd_168745 := by exact prefixLift 168745
  have htrace : WordTrace (prefixWord ++ tailWord_168745) baseStart_168745 baseEnd_168745 := by
    simpa [prefixWord, tailWord_168745, baseEnd_168745] using wordTrace_append hprefix tailTrace_168745
  have hstable : (prefixWord ++ tailWord_168745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168745).length < 2 ^ (prefixWord ++ tailWord_168745).sum := by decide
  have hdescent : baseEnd_168745 < baseStart_168745 := by decide
  rcases family_descends (prefixWord ++ tailWord_168745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168772 : List Nat := [2, 3, 4, 2, 2, 1, 2, 2, 4]
def baseStart_168772 : Nat := 118140960795 + 168772 * 2 ^ 59
def prefixEnd_168772 : Nat := 4983230072969 + 3 ^ 40 * 168772 * 2
def baseEnd_168772 : Nat := 19258034893493091660853

theorem tailTrace_168772 : CollatzResearch.WordTrace tailWord_168772 prefixEnd_168772 19258034893493091660853 := by
  unfold tailWord_168772
  simp only [CollatzResearch.WordTrace]
  refine ⟨3077810272287671403958285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4103747029716895205277713 3077810272287671403958285)
  ·
    refine ⟨1154178852107876776484357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3077810272287671403958285 1154178852107876776484357)
    ·
      refine ⟨216408534770226895590817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1154178852107876776484357 216408534770226895590817)
      ·
        refine ⟨162306401077670171693113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216408534770226895590817 162306401077670171693113)
        ·
          refine ⟨121729800808252628769835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162306401077670171693113 121729800808252628769835)
          ·
            refine ⟨182594701212378943154753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121729800808252628769835 182594701212378943154753)
            ·
              refine ⟨136946025909284207366065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182594701212378943154753 136946025909284207366065)
              ·
                refine ⟨102709519431963155524549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136946025909284207366065 102709519431963155524549)
                ·
                  refine ⟨19258034893493091660853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102709519431963155524549 19258034893493091660853)
                  ·
                    rfl

theorem cell22_168772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_168772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168772 prefixEnd_168772 := by exact prefixLift 168772
  have htrace : WordTrace (prefixWord ++ tailWord_168772) baseStart_168772 baseEnd_168772 := by
    simpa [prefixWord, tailWord_168772, baseEnd_168772] using wordTrace_append hprefix tailTrace_168772
  have hstable : (prefixWord ++ tailWord_168772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168772).length < 2 ^ (prefixWord ++ tailWord_168772).sum := by decide
  have hdescent : baseEnd_168772 < baseStart_168772 := by decide
  rcases family_descends (prefixWord ++ tailWord_168772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168777 : List Nat := [1, 2, 1, 1, 2, 5, 1, 4, 5]
def baseStart_168777 : Nat := 118140960795 + 168777 * 2 ^ 59
def prefixEnd_168777 : Nat := 4983230072969 + 3 ^ 40 * 168777 * 2
def baseEnd_168777 : Nat := 19258605427553642869181

theorem tailTrace_168777 : CollatzResearch.WordTrace tailWord_168777 prefixEnd_168777 19258605427553642869181 := by
  unfold tailWord_168777
  simp only [CollatzResearch.WordTrace]
  refine ⟨6155802909557228661848585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4103868606371485774565723 6155802909557228661848585)
  ·
    refine ⟨4616852182167921496386439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6155802909557228661848585 4616852182167921496386439)
    ·
      refine ⟨6925278273251882244579659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4616852182167921496386439 6925278273251882244579659)
      ·
        refine ⟨10387917409877823366869489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6925278273251882244579659 10387917409877823366869489)
        ·
          refine ⟨7790938057408367525152117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10387917409877823366869489 7790938057408367525152117)
          ·
            refine ⟨730400442882034455483011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7790938057408367525152117 730400442882034455483011)
            ·
              refine ⟨1095600664323051683224517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730400442882034455483011 1095600664323051683224517)
              ·
                refine ⟨205425124560572190604597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1095600664323051683224517 205425124560572190604597)
                ·
                  refine ⟨19258605427553642869181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205425124560572190604597 19258605427553642869181)
                  ·
                    rfl

theorem cell22_168777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 5].length) (baseStart_168777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168777 prefixEnd_168777 := by exact prefixLift 168777
  have htrace : WordTrace (prefixWord ++ tailWord_168777) baseStart_168777 baseEnd_168777 := by
    simpa [prefixWord, tailWord_168777, baseEnd_168777] using wordTrace_append hprefix tailTrace_168777
  have hstable : (prefixWord ++ tailWord_168777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168777).length < 2 ^ (prefixWord ++ tailWord_168777).sum := by decide
  have hdescent : baseEnd_168777 < baseStart_168777 := by decide
  rcases family_descends (prefixWord ++ tailWord_168777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168839 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 6]
def baseStart_168839 : Nat := 118140960795 + 168839 * 2 ^ 59
def prefixEnd_168839 : Nat := 4983230072969 + 3 ^ 40 * 168839 * 2
def baseEnd_168839 : Nat := 19265680049904477852451

theorem tailTrace_168839 : CollatzResearch.WordTrace tailWord_168839 prefixEnd_168839 19265680049904477852451 := by
  unfold tailWord_168839
  simp only [CollatzResearch.WordTrace]
  refine ⟨6158064235332613250605571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4105376156888408833737047 6158064235332613250605571)
  ·
    refine ⟨9237096352998919875908357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6158064235332613250605571 9237096352998919875908357)
    ·
      refine ⟨1731955566187297476732817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9237096352998919875908357 1731955566187297476732817)
      ·
        refine ⟨1298966674640473107549613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1731955566187297476732817 1298966674640473107549613)
        ·
          refine ⟨487112502990177415331105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1298966674640473107549613 487112502990177415331105)
          ·
            refine ⟨365334377242633061498329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487112502990177415331105 365334377242633061498329)
            ·
              refine ⟨274000782931974796123747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365334377242633061498329 274000782931974796123747)
              ·
                refine ⟨411001174397962194185621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274000782931974796123747 411001174397962194185621)
                ·
                  refine ⟨19265680049904477852451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 411001174397962194185621 19265680049904477852451)
                  ·
                    rfl

theorem cell22_168839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 6].length) (baseStart_168839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168839 prefixEnd_168839 := by exact prefixLift 168839
  have htrace : WordTrace (prefixWord ++ tailWord_168839) baseStart_168839 baseEnd_168839 := by
    simpa [prefixWord, tailWord_168839, baseEnd_168839] using wordTrace_append hprefix tailTrace_168839
  have hstable : (prefixWord ++ tailWord_168839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168839).length < 2 ^ (prefixWord ++ tailWord_168839).sum := by decide
  have hdescent : baseEnd_168839 < baseStart_168839 := by decide
  rcases family_descends (prefixWord ++ tailWord_168839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168909 : List Nat := [1, 6, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_168909 : Nat := 118140960795 + 168909 * 2 ^ 59
def prefixEnd_168909 : Nat := 4983230072969 + 3 ^ 40 * 168909 * 2
def baseEnd_168909 : Nat := 57821002580256584307139

theorem tailTrace_168909 : CollatzResearch.WordTrace tailWord_168909 prefixEnd_168909 57821002580256584307139 := by
  unfold tailWord_168909
  simp only [CollatzResearch.WordTrace]
  refine ⟨6160617345079015205653781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4107078230052676803769187 6160617345079015205653781)
  ·
    refine ⟨288778938050578837765021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6160617345079015205653781 288778938050578837765021)
    ·
      refine ⟨108292101768967064161883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288778938050578837765021 108292101768967064161883)
      ·
        refine ⟨162438152653450596242825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108292101768967064161883 162438152653450596242825)
        ·
          refine ⟨121828614490087947182119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162438152653450596242825 121828614490087947182119)
          ·
            refine ⟨182742921735131920773179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121828614490087947182119 182742921735131920773179)
            ·
              refine ⟨274114382602697881159769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182742921735131920773179 274114382602697881159769)
              ·
                refine ⟨205585786952023410869827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274114382602697881159769 205585786952023410869827)
                ·
                  refine ⟨308378680428035116304741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205585786952023410869827 308378680428035116304741)
                  ·
                    refine ⟨57821002580256584307139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 308378680428035116304741 57821002580256584307139)
                    ·
                      rfl

theorem cell22_168909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_168909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168909 prefixEnd_168909 := by exact prefixLift 168909
  have htrace : WordTrace (prefixWord ++ tailWord_168909) baseStart_168909 baseEnd_168909 := by
    simpa [prefixWord, tailWord_168909, baseEnd_168909] using wordTrace_append hprefix tailTrace_168909
  have hstable : (prefixWord ++ tailWord_168909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168909).length < 2 ^ (prefixWord ++ tailWord_168909).sum := by decide
  have hdescent : baseEnd_168909 < baseStart_168909 := by decide
  rcases family_descends (prefixWord ++ tailWord_168909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168950 : List Nat := [5, 1, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_168950 : Nat := 118140960795 + 168950 * 2 ^ 59
def prefixEnd_168950 : Nat := 4983230072969 + 3 ^ 40 * 168950 * 2
def baseEnd_168950 : Nat := 57835037718146144032013

theorem tailTrace_168950 : CollatzResearch.WordTrace tailWord_168950 prefixEnd_168950 57835037718146144032013 := by
  unfold tailWord_168950
  simp only [CollatzResearch.WordTrace]
  refine ⟨385132046120654950493519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4108075158620319471930869 385132046120654950493519)
  ·
    refine ⟨577698069180982425740279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 385132046120654950493519 577698069180982425740279)
    ·
      refine ⟨866547103771473638610419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 577698069180982425740279 866547103771473638610419)
      ·
        refine ⟨1299820655657210457915629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866547103771473638610419 1299820655657210457915629)
        ·
          refine ⟨487432745871453921718361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1299820655657210457915629 487432745871453921718361)
          ·
            refine ⟨365574559403590441288771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487432745871453921718361 365574559403590441288771)
            ·
              refine ⟨548361839105385661933157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365574559403590441288771 548361839105385661933157)
              ·
                refine ⟨102817844832259811612467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 548361839105385661933157 102817844832259811612467)
                ·
                  refine ⟨154226767248389717418701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102817844832259811612467 154226767248389717418701)
                  ·
                    refine ⟨57835037718146144032013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 154226767248389717418701 57835037718146144032013)
                    ·
                      rfl

theorem cell22_168950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_168950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168950 prefixEnd_168950 := by exact prefixLift 168950
  have htrace : WordTrace (prefixWord ++ tailWord_168950) baseStart_168950 baseEnd_168950 := by
    simpa [prefixWord, tailWord_168950, baseEnd_168950] using wordTrace_append hprefix tailTrace_168950
  have hstable : (prefixWord ++ tailWord_168950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168950).length < 2 ^ (prefixWord ++ tailWord_168950).sum := by decide
  have hdescent : baseEnd_168950 < baseStart_168950 := by decide
  rcases family_descends (prefixWord ++ tailWord_168950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168974 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 8]
def baseStart_168974 : Nat := 118140960795 + 168974 * 2 ^ 59
def prefixEnd_168974 : Nat := 4983230072969 + 3 ^ 40 * 168974 * 2
def baseEnd_168974 : Nat := 19281084469539360477313

theorem tailTrace_168974 : CollatzResearch.WordTrace tailWord_168974 prefixEnd_168974 19281084469539360477313 := by
  unfold tailWord_168974
  simp only [CollatzResearch.WordTrace]
  refine ⟨770373511230441413346247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4108658726562354204513317 770373511230441413346247)
  ·
    refine ⟨1155560266845662120019371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 770373511230441413346247 1155560266845662120019371)
    ·
      refine ⟨1733340400268493180029057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155560266845662120019371 1733340400268493180029057)
      ·
        refine ⟨1300005300201369885021793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1733340400268493180029057 1300005300201369885021793)
        ·
          refine ⟨975003975151027413766345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1300005300201369885021793 975003975151027413766345)
          ·
            refine ⟨731252981363270560324759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 975003975151027413766345 731252981363270560324759)
            ·
              refine ⟨1096879472044905840487139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731252981363270560324759 1096879472044905840487139)
              ·
                refine ⟨1645319208067358760730709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1096879472044905840487139 1645319208067358760730709)
                ·
                  refine ⟨19281084469539360477313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1645319208067358760730709 19281084469539360477313)
                  ·
                    rfl

theorem cell22_168974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_168974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168974 prefixEnd_168974 := by exact prefixLift 168974
  have htrace : WordTrace (prefixWord ++ tailWord_168974) baseStart_168974 baseEnd_168974 := by
    simpa [prefixWord, tailWord_168974, baseEnd_168974] using wordTrace_append hprefix tailTrace_168974
  have hstable : (prefixWord ++ tailWord_168974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168974).length < 2 ^ (prefixWord ++ tailWord_168974).sum := by decide
  have hdescent : baseEnd_168974 < baseStart_168974 := by decide
  rcases family_descends (prefixWord ++ tailWord_168974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168991 : List Nat := [1, 1, 2, 4, 1, 3, 1, 5, 4]
def baseStart_168991 : Nat := 118140960795 + 168991 * 2 ^ 59
def prefixEnd_168991 : Nat := 4983230072969 + 3 ^ 40 * 168991 * 2
def baseEnd_168991 : Nat := 19283024285345234585629

theorem tailTrace_168991 : CollatzResearch.WordTrace tailWord_168991 prefixEnd_168991 19283024285345234585629 := by
  unfold tailWord_168991
  simp only [CollatzResearch.WordTrace]
  refine ⟨6163608130781943210138827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4109072087187962140092551 6163608130781943210138827)
  ·
    refine ⟨9245412196172914815208241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6163608130781943210138827 9245412196172914815208241)
    ·
      refine ⟨6934059147129686111406181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9245412196172914815208241 6934059147129686111406181)
      ·
        refine ⟨1300136090086816145888659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6934059147129686111406181 1300136090086816145888659)
        ·
          refine ⟨1950204135130224218832989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1300136090086816145888659 1950204135130224218832989)
          ·
            refine ⟨731326550673834082062371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1950204135130224218832989 731326550673834082062371)
            ·
              refine ⟨1096989826010751123093557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731326550673834082062371 1096989826010751123093557)
              ·
                refine ⟨102842796188507917790021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1096989826010751123093557 102842796188507917790021)
                ·
                  refine ⟨19283024285345234585629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102842796188507917790021 19283024285345234585629)
                  ·
                    rfl

theorem cell22_168991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 4].length) (baseStart_168991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168991 prefixEnd_168991 := by exact prefixLift 168991
  have htrace : WordTrace (prefixWord ++ tailWord_168991) baseStart_168991 baseEnd_168991 := by
    simpa [prefixWord, tailWord_168991, baseEnd_168991] using wordTrace_append hprefix tailTrace_168991
  have hstable : (prefixWord ++ tailWord_168991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168991).length < 2 ^ (prefixWord ++ tailWord_168991).sum := by decide
  have hdescent : baseEnd_168991 < baseStart_168991 := by decide
  rcases family_descends (prefixWord ++ tailWord_168991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168993 : List Nat := [1, 2, 3, 2, 3, 1, 4, 1, 1, 4]
def baseStart_168993 : Nat := 118140960795 + 168993 * 2 ^ 59
def prefixEnd_168993 : Nat := 4983230072969 + 3 ^ 40 * 168993 * 2
def baseEnd_168993 : Nat := 57849757496908365206881

theorem tailTrace_168993 : CollatzResearch.WordTrace tailWord_168993 prefixEnd_168993 57849757496908365206881 := by
  unfold tailWord_168993
  simp only [CollatzResearch.WordTrace]
  refine ⟨6163681076774697551711633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4109120717849798367807755 6163681076774697551711633)
  ·
    refine ⟨4622760807581023163783725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6163681076774697551711633 4622760807581023163783725)
    ·
      refine ⟨1733535302842883686418897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4622760807581023163783725 1733535302842883686418897)
      ·
        refine ⟨1300151477132162764814173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1733535302842883686418897 1300151477132162764814173)
        ·
          refine ⟨487556803924561036805315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1300151477132162764814173 487556803924561036805315)
          ·
            refine ⟨731335205886841555207973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487556803924561036805315 731335205886841555207973)
            ·
              refine ⟨137125351103782791601495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 731335205886841555207973 137125351103782791601495)
              ·
                refine ⟨205688026655674187402243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137125351103782791601495 205688026655674187402243)
                ·
                  refine ⟨308532039983511281103365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205688026655674187402243 308532039983511281103365)
                  ·
                    refine ⟨57849757496908365206881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 308532039983511281103365 57849757496908365206881)
                    ·
                      rfl

theorem cell22_168993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_168993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_168993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_168993 prefixEnd_168993 := by exact prefixLift 168993
  have htrace : WordTrace (prefixWord ++ tailWord_168993) baseStart_168993 baseEnd_168993 := by
    simpa [prefixWord, tailWord_168993, baseEnd_168993] using wordTrace_append hprefix tailTrace_168993
  have hstable : (prefixWord ++ tailWord_168993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168993).length < 2 ^ (prefixWord ++ tailWord_168993).sum := by decide
  have hdescent : baseEnd_168993 < baseStart_168993 := by decide
  rcases family_descends (prefixWord ++ tailWord_168993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169004 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 4, 4]
def baseStart_169004 : Nat := 118140960795 + 169004 * 2 ^ 59
def prefixEnd_169004 : Nat := 4983230072969 + 3 ^ 40 * 169004 * 2
def baseEnd_169004 : Nat := 57853523021708003181847

theorem tailTrace_169004 : CollatzResearch.WordTrace tailWord_169004 prefixEnd_169004 57853523021708003181847 := by
  unfold tailWord_169004
  simp only [CollatzResearch.WordTrace]
  refine ⟨3082041139867423215181033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4109388186489897620241377 3082041139867423215181033)
  ·
    refine ⟨2311530854900567411385775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3082041139867423215181033 2311530854900567411385775)
    ·
      refine ⟨3467296282350851117078663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2311530854900567411385775 3467296282350851117078663)
      ·
        refine ⟨5200944423526276675617995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3467296282350851117078663 5200944423526276675617995)
        ·
          refine ⟨7801416635289415013426993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5200944423526276675617995 7801416635289415013426993)
          ·
            refine ⟨5851062476467061260070245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7801416635289415013426993 5851062476467061260070245)
            ·
              refine ⟨1097074214337573986263171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5851062476467061260070245 1097074214337573986263171)
              ·
                refine ⟨1645611321506360979394757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1097074214337573986263171 1645611321506360979394757)
                ·
                  refine ⟨308552122782442683636517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1645611321506360979394757 308552122782442683636517)
                  ·
                    refine ⟨57853523021708003181847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 308552122782442683636517 57853523021708003181847)
                    ·
                      rfl

theorem cell22_169004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_169004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169004 prefixEnd_169004 := by exact prefixLift 169004
  have htrace : WordTrace (prefixWord ++ tailWord_169004) baseStart_169004 baseEnd_169004 := by
    simpa [prefixWord, tailWord_169004, baseEnd_169004] using wordTrace_append hprefix tailTrace_169004
  have hstable : (prefixWord ++ tailWord_169004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169004).length < 2 ^ (prefixWord ++ tailWord_169004).sum := by decide
  have hdescent : baseEnd_169004 < baseStart_169004 := by decide
  rcases family_descends (prefixWord ++ tailWord_169004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169053 : List Nat := [1, 4, 4, 1, 2, 2, 8]
def baseStart_169053 : Nat := 118140960795 + 169053 * 2 ^ 59
def prefixEnd_169053 : Nat := 4983230072969 + 3 ^ 40 * 169053 * 2
def baseEnd_169053 : Nat := 2143344323077341063211

theorem tailTrace_169053 : CollatzResearch.WordTrace tailWord_169053 prefixEnd_169053 2143344323077341063211 := by
  unfold tailWord_169053
  simp only [CollatzResearch.WordTrace]
  refine ⟨6165869456557327798895813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4110579637704885199263875 6165869456557327798895813)
  ·
    refine ⟨1156100523104498962292965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6165869456557327798895813 1156100523104498962292965)
    ·
      refine ⟨216768848082093555429931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1156100523104498962292965 216768848082093555429931)
      ·
        refine ⟨325153272123140333144897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216768848082093555429931 325153272123140333144897)
        ·
          refine ⟨243864954092355249858673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325153272123140333144897 243864954092355249858673)
          ·
            refine ⟨182898715569266437394005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243864954092355249858673 182898715569266437394005)
            ·
              refine ⟨2143344323077341063211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 182898715569266437394005 2143344323077341063211)
              ·
                rfl

theorem cell22_169053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 8].length) (baseStart_169053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169053 prefixEnd_169053 := by exact prefixLift 169053
  have htrace : WordTrace (prefixWord ++ tailWord_169053) baseStart_169053 baseEnd_169053 := by
    simpa [prefixWord, tailWord_169053, baseEnd_169053] using wordTrace_append hprefix tailTrace_169053
  have hstable : (prefixWord ++ tailWord_169053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169053).length < 2 ^ (prefixWord ++ tailWord_169053).sum := by decide
  have hdescent : baseEnd_169053 < baseStart_169053 := by decide
  rcases family_descends (prefixWord ++ tailWord_169053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169079 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 1, 7]
def baseStart_169079 : Nat := 118140960795 + 169079 * 2 ^ 59
def prefixEnd_169079 : Nat := 4983230072969 + 3 ^ 40 * 169079 * 2
def baseEnd_169079 : Nat := 57879197054432807556617

theorem tailTrace_169079 : CollatzResearch.WordTrace tailWord_169079 prefixEnd_169079 57879197054432807556617 := by
  unfold tailWord_169079
  simp only [CollatzResearch.WordTrace]
  refine ⟨6166817754463134239342291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4111211836308756159561527 6166817754463134239342291)
  ·
    refine ⟨9250226631694701359013437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6166817754463134239342291 9250226631694701359013437)
    ·
      refine ⟨3468834986885513009630039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9250226631694701359013437 3468834986885513009630039)
      ·
        refine ⟨5203252480328269514445059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3468834986885513009630039 5203252480328269514445059)
        ·
          refine ⟨7804878720492404271667589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5203252480328269514445059 7804878720492404271667589)
          ·
            refine ⟨1463414760092325800937673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7804878720492404271667589 1463414760092325800937673)
            ·
              refine ⟨1097561070069244350703255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1463414760092325800937673 1097561070069244350703255)
              ·
                refine ⟨1646341605103866526054883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1097561070069244350703255 1646341605103866526054883)
                ·
                  refine ⟨2469512407655799789082325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646341605103866526054883 2469512407655799789082325)
                  ·
                    refine ⟨57879197054432807556617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2469512407655799789082325 57879197054432807556617)
                    ·
                      rfl

theorem cell22_169079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_169079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169079 prefixEnd_169079 := by exact prefixLift 169079
  have htrace : WordTrace (prefixWord ++ tailWord_169079) baseStart_169079 baseEnd_169079 := by
    simpa [prefixWord, tailWord_169079, baseEnd_169079] using wordTrace_append hprefix tailTrace_169079
  have hstable : (prefixWord ++ tailWord_169079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169079).length < 2 ^ (prefixWord ++ tailWord_169079).sum := by decide
  have hdescent : baseEnd_169079 < baseStart_169079 := by decide
  rcases family_descends (prefixWord ++ tailWord_169079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169109 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 10]
def baseStart_169109 : Nat := 118140960795 + 169109 * 2 ^ 59
def prefixEnd_169109 : Nat := 4983230072969 + 3 ^ 40 * 169109 * 2
def baseEnd_169109 : Nat := 19296488889174243102175

theorem tailTrace_169109 : CollatzResearch.WordTrace tailWord_169109 prefixEnd_169109 19296488889174243102175 := by
  unfold tailWord_169109
  simp only [CollatzResearch.WordTrace]
  refine ⟨6167911944354449362934381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4111941296236299575289587 6167911944354449362934381)
  ·
    refine ⟨2312966979132918511100393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6167911944354449362934381 2312966979132918511100393)
    ·
      refine ⟨1734725234349688883325295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2312966979132918511100393 1734725234349688883325295)
      ·
        refine ⟨2602087851524533324987943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1734725234349688883325295 2602087851524533324987943)
        ·
          refine ⟨3903131777286799987481915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2602087851524533324987943 3903131777286799987481915)
          ·
            refine ⟨5854697665930199981222873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3903131777286799987481915 5854697665930199981222873)
            ·
              refine ⟨4391023249447649985917155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5854697665930199981222873 4391023249447649985917155)
              ·
                refine ⟨6586534874171474978875733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4391023249447649985917155 6586534874171474978875733)
                ·
                  refine ⟨19296488889174243102175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 6586534874171474978875733 19296488889174243102175)
                  ·
                    rfl

theorem cell22_169109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_169109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169109 prefixEnd_169109 := by exact prefixLift 169109
  have htrace : WordTrace (prefixWord ++ tailWord_169109) baseStart_169109 baseEnd_169109 := by
    simpa [prefixWord, tailWord_169109, baseEnd_169109] using wordTrace_append hprefix tailTrace_169109
  have hstable : (prefixWord ++ tailWord_169109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169109).length < 2 ^ (prefixWord ++ tailWord_169109).sum := by decide
  have hdescent : baseEnd_169109 < baseStart_169109 := by decide
  rcases family_descends (prefixWord ++ tailWord_169109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169119 : List Nat := [1, 1, 2, 6, 2, 2, 2, 2, 1, 3]
def baseStart_169119 : Nat := 118140960795 + 169119 * 2 ^ 59
def prefixEnd_169119 : Nat := 4983230072969 + 3 ^ 40 * 169119 * 2
def baseEnd_169119 : Nat := 57892889871886036556495

theorem tailTrace_169119 : CollatzResearch.WordTrace tailWord_169119 prefixEnd_169119 57892889871886036556495 := by
  unfold tailWord_169119
  simp only [CollatzResearch.WordTrace]
  refine ⟨6168276674318221070798411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4112184449545480713865607 6168276674318221070798411)
  ·
    refine ⟨9252415011477331606197617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6168276674318221070798411 9252415011477331606197617)
    ·
      refine ⟨6939311258607998704648213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9252415011477331606197617 6939311258607998704648213)
      ·
        refine ⟨325280215247249939280385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6939311258607998704648213 325280215247249939280385)
        ·
          refine ⟨243960161435437454460289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325280215247249939280385 243960161435437454460289)
          ·
            refine ⟨182970121076578090845217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243960161435437454460289 182970121076578090845217)
            ·
              refine ⟨137227590807433568133913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182970121076578090845217 137227590807433568133913)
              ·
                refine ⟨102920693105575176100435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137227590807433568133913 102920693105575176100435)
                ·
                  refine ⟨154381039658362764150653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102920693105575176100435 154381039658362764150653)
                  ·
                    refine ⟨57892889871886036556495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 154381039658362764150653 57892889871886036556495)
                    ·
                      rfl

theorem cell22_169119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 1, 3].length) (baseStart_169119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169119 prefixEnd_169119 := by exact prefixLift 169119
  have htrace : WordTrace (prefixWord ++ tailWord_169119) baseStart_169119 baseEnd_169119 := by
    simpa [prefixWord, tailWord_169119, baseEnd_169119] using wordTrace_append hprefix tailTrace_169119
  have hstable : (prefixWord ++ tailWord_169119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169119).length < 2 ^ (prefixWord ++ tailWord_169119).sum := by decide
  have hdescent : baseEnd_169119 < baseStart_169119 := by decide
  rcases family_descends (prefixWord ++ tailWord_169119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169203 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 3, 3]
def baseStart_169203 : Nat := 118140960795 + 169203 * 2 ^ 59
def prefixEnd_169203 : Nat := 4983230072969 + 3 ^ 40 * 169203 * 2
def baseEnd_169203 : Nat := 57921644788537817456237

theorem tailTrace_169203 : CollatzResearch.WordTrace tailWord_169203 prefixEnd_169203 57921644788537817456237 := by
  unfold tailWord_169203
  simp only [CollatzResearch.WordTrace]
  refine ⟨6171340406013903416856263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4114226937342602277904175 6171340406013903416856263)
  ·
    refine ⟨9257010609020855125284395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6171340406013903416856263 9257010609020855125284395)
    ·
      refine ⟨13885515913531282687926593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9257010609020855125284395 13885515913531282687926593)
      ·
        refine ⟨10414136935148462015944945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13885515913531282687926593 10414136935148462015944945)
        ·
          refine ⟨7810602701361346511958709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10414136935148462015944945 7810602701361346511958709)
          ·
            refine ⟨732244003252626235496129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7810602701361346511958709 732244003252626235496129)
            ·
              refine ⟨549183002439469676622097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 732244003252626235496129 549183002439469676622097)
              ·
                refine ⟨411887251829602257466573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549183002439469676622097 411887251829602257466573)
                ·
                  refine ⟨154457719436100846549965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 411887251829602257466573 154457719436100846549965)
                  ·
                    refine ⟨57921644788537817456237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 154457719436100846549965 57921644788537817456237)
                    ·
                      rfl

theorem cell22_169203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 3].length) (baseStart_169203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169203 prefixEnd_169203 := by exact prefixLift 169203
  have htrace : WordTrace (prefixWord ++ tailWord_169203) baseStart_169203 baseEnd_169203 := by
    simpa [prefixWord, tailWord_169203, baseEnd_169203] using wordTrace_append hprefix tailTrace_169203
  have hstable : (prefixWord ++ tailWord_169203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169203).length < 2 ^ (prefixWord ++ tailWord_169203).sum := by decide
  have hdescent : baseEnd_169203 < baseStart_169203 := by decide
  rcases family_descends (prefixWord ++ tailWord_169203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169250 : List Nat := [3, 3, 1, 1, 4, 1, 1, 3, 5]
def baseStart_169250 : Nat := 118140960795 + 169250 * 2 ^ 59
def prefixEnd_169250 : Nat := 4983230072969 + 3 ^ 40 * 169250 * 2
def baseEnd_169250 : Nat := 19312577949681787177031

theorem tailTrace_169250 : CollatzResearch.WordTrace tailWord_169250 prefixEnd_169250 19312577949681787177031 := by
  unfold tailWord_169250
  simp only [CollatzResearch.WordTrace]
  refine ⟨1543263659210907610954301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4115369757895753629211469 1543263659210907610954301)
  ·
    refine ⟨578723872204090354107863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1543263659210907610954301 578723872204090354107863)
    ·
      refine ⟨868085808306135531161795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 578723872204090354107863 868085808306135531161795)
      ·
        refine ⟨1302128712459203296742693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868085808306135531161795 1302128712459203296742693)
        ·
          refine ⟨244149133586100618139255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1302128712459203296742693 244149133586100618139255)
          ·
            refine ⟨366223700379150927208883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244149133586100618139255 366223700379150927208883)
            ·
              refine ⟨549335550568726390813325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366223700379150927208883 549335550568726390813325)
              ·
                refine ⟨206000831463272396554997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 549335550568726390813325 206000831463272396554997)
                ·
                  refine ⟨19312577949681787177031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 206000831463272396554997 19312577949681787177031)
                  ·
                    rfl

theorem cell22_169250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_169250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169250 prefixEnd_169250 := by exact prefixLift 169250
  have htrace : WordTrace (prefixWord ++ tailWord_169250) baseStart_169250 baseEnd_169250 := by
    simpa [prefixWord, tailWord_169250, baseEnd_169250] using wordTrace_append hprefix tailTrace_169250
  have hstable : (prefixWord ++ tailWord_169250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169250).length < 2 ^ (prefixWord ++ tailWord_169250).sum := by decide
  have hdescent : baseEnd_169250 < baseStart_169250 := by decide
  rcases family_descends (prefixWord ++ tailWord_169250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169280 : List Nat := [2, 1, 1, 2, 2, 1, 7, 1, 1, 4]
def baseStart_169280 : Nat := 118140960795 + 169280 * 2 ^ 59
def prefixEnd_169280 : Nat := 4983230072969 + 3 ^ 40 * 169280 * 2
def baseEnd_169280 : Nat := 57948003462135283281001

theorem tailTrace_169280 : CollatzResearch.WordTrace tailWord_169280 prefixEnd_169280 57948003462135283281001 := by
  unfold tailWord_169280
  simp only [CollatzResearch.WordTrace]
  refine ⟨3087074413367472783704647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4116099217823297044939529 3087074413367472783704647)
  ·
    refine ⟨4630611620051209175556971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3087074413367472783704647 4630611620051209175556971)
    ·
      refine ⟨6945917430076813763335457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4630611620051209175556971 6945917430076813763335457)
      ·
        refine ⟨5209438072557610322501593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6945917430076813763335457 5209438072557610322501593)
        ·
          refine ⟨3907078554418207741876195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5209438072557610322501593 3907078554418207741876195)
          ·
            refine ⟨5860617831627311612814293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3907078554418207741876195 5860617831627311612814293)
            ·
              refine ⟨137358230428765115925335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5860617831627311612814293 137358230428765115925335)
              ·
                refine ⟨206037345643147673888003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137358230428765115925335 206037345643147673888003)
                ·
                  refine ⟨309056018464721510832005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206037345643147673888003 309056018464721510832005)
                  ·
                    refine ⟨57948003462135283281001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 309056018464721510832005 57948003462135283281001)
                    ·
                      rfl

theorem cell22_169280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 1, 4].length) (baseStart_169280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169280 prefixEnd_169280 := by exact prefixLift 169280
  have htrace : WordTrace (prefixWord ++ tailWord_169280) baseStart_169280 baseEnd_169280 := by
    simpa [prefixWord, tailWord_169280, baseEnd_169280] using wordTrace_append hprefix tailTrace_169280
  have hstable : (prefixWord ++ tailWord_169280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169280).length < 2 ^ (prefixWord ++ tailWord_169280).sum := by decide
  have hdescent : baseEnd_169280 < baseStart_169280 := by decide
  rcases family_descends (prefixWord ++ tailWord_169280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169321 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 1, 9]
def baseStart_169321 : Nat := 118140960795 + 169321 * 2 ^ 59
def prefixEnd_169321 : Nat := 4983230072969 + 3 ^ 40 * 169321 * 2
def baseEnd_169321 : Nat := 57962038600024843005875

theorem tailTrace_169321 : CollatzResearch.WordTrace tailWord_169321 prefixEnd_169321 57962038600024843005875 := by
  unfold tailWord_169321
  simp only [CollatzResearch.WordTrace]
  refine ⟨6175644219586409569651817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4117096146390939713101211 6175644219586409569651817)
  ·
    refine ⟨4631733164689807177238863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6175644219586409569651817 4631733164689807177238863)
    ·
      refine ⟨6947599747034710765858295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4631733164689807177238863 6947599747034710765858295)
      ·
        refine ⟨10421399620552066148787443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6947599747034710765858295 10421399620552066148787443)
        ·
          refine ⟨15632099430828099223181165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10421399620552066148787443 15632099430828099223181165)
          ·
            refine ⟨5862037286560537208692937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15632099430828099223181165 5862037286560537208692937)
            ·
              refine ⟨4396527964920402906519703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5862037286560537208692937 4396527964920402906519703)
              ·
                refine ⟨6594791947380604359779555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396527964920402906519703 6594791947380604359779555)
                ·
                  refine ⟨9892187921070906539669333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6594791947380604359779555 9892187921070906539669333)
                  ·
                    refine ⟨57962038600024843005875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 9892187921070906539669333 57962038600024843005875)
                    ·
                      rfl

theorem cell22_169321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_169321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169321 prefixEnd_169321 := by exact prefixLift 169321
  have htrace : WordTrace (prefixWord ++ tailWord_169321) baseStart_169321 baseEnd_169321 := by
    simpa [prefixWord, tailWord_169321, baseEnd_169321] using wordTrace_append hprefix tailTrace_169321
  have hstable : (prefixWord ++ tailWord_169321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169321).length < 2 ^ (prefixWord ++ tailWord_169321).sum := by decide
  have hdescent : baseEnd_169321 < baseStart_169321 := by decide
  rcases family_descends (prefixWord ++ tailWord_169321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169325 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_169325 : Nat := 118140960795 + 169325 * 2 ^ 59
def prefixEnd_169325 : Nat := 4983230072969 + 3 ^ 40 * 169325 * 2
def baseEnd_169325 : Nat := 57963407881770165905863

theorem tailTrace_169325 : CollatzResearch.WordTrace tailWord_169325 prefixEnd_169325 57963407881770165905863 := by
  unfold tailWord_169325
  simp only [CollatzResearch.WordTrace]
  refine ⟨6175790111571918252797429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4117193407714612168531619 6175790111571918252797429)
  ·
    refine ⟨578980322959867336199759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6175790111571918252797429 578980322959867336199759)
    ·
      refine ⟨868470484439801004299639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 578980322959867336199759 868470484439801004299639)
      ·
        refine ⟨1302705726659701506449459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868470484439801004299639 1302705726659701506449459)
        ·
          refine ⟨1954058589989552259674189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1302705726659701506449459 1954058589989552259674189)
          ·
            refine ⟨732771971246082097377821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1954058589989552259674189 732771971246082097377821)
            ·
              refine ⟨274789489217280786516683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 732771971246082097377821 274789489217280786516683)
              ·
                refine ⟨412184233825921179775025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274789489217280786516683 412184233825921179775025)
                ·
                  refine ⟨309138175369440884831269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412184233825921179775025 309138175369440884831269)
                  ·
                    refine ⟨57963407881770165905863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 309138175369440884831269 57963407881770165905863)
                    ·
                      rfl

theorem cell22_169325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_169325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169325 prefixEnd_169325 := by exact prefixLift 169325
  have htrace : WordTrace (prefixWord ++ tailWord_169325) baseStart_169325 baseEnd_169325 := by
    simpa [prefixWord, tailWord_169325, baseEnd_169325] using wordTrace_append hprefix tailTrace_169325
  have hstable : (prefixWord ++ tailWord_169325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169325).length < 2 ^ (prefixWord ++ tailWord_169325).sum := by decide
  have hdescent : baseEnd_169325 < baseStart_169325 := by decide
  rcases family_descends (prefixWord ++ tailWord_169325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169355 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 3, 3]
def baseStart_169355 : Nat := 118140960795 + 169355 * 2 ^ 59
def prefixEnd_169355 : Nat := 4983230072969 + 3 ^ 40 * 169355 * 2
def baseEnd_169355 : Nat := 57973677494860087655771

theorem tailTrace_169355 : CollatzResearch.WordTrace tailWord_169355 prefixEnd_169355 57973677494860087655771 := by
  unfold tailWord_169355
  simp only [CollatzResearch.WordTrace]
  refine ⟨6176884301463233376389519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4117922867642155584259679 6176884301463233376389519)
  ·
    refine ⟨9265326452194850064584279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6176884301463233376389519 9265326452194850064584279)
    ·
      refine ⟨13897989678292275096876419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9265326452194850064584279 13897989678292275096876419)
      ·
        refine ⟨20846984517438412645314629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13897989678292275096876419 20846984517438412645314629)
        ·
          refine ⟨3908809597019702370996493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20846984517438412645314629 3908809597019702370996493)
          ·
            refine ⟨1465803598882388389123685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3908809597019702370996493 1465803598882388389123685)
            ·
              refine ⟨274838174790447822960691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1465803598882388389123685 274838174790447822960691)
              ·
                refine ⟨412257262185671734441037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274838174790447822960691 412257262185671734441037)
                ·
                  refine ⟨154596473319626900415389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412257262185671734441037 154596473319626900415389)
                  ·
                    refine ⟨57973677494860087655771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 154596473319626900415389 57973677494860087655771)
                    ·
                      rfl

theorem cell22_169355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 3].length) (baseStart_169355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169355 prefixEnd_169355 := by exact prefixLift 169355
  have htrace : WordTrace (prefixWord ++ tailWord_169355) baseStart_169355 baseEnd_169355 := by
    simpa [prefixWord, tailWord_169355, baseEnd_169355] using wordTrace_append hprefix tailTrace_169355
  have hstable : (prefixWord ++ tailWord_169355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169355).length < 2 ^ (prefixWord ++ tailWord_169355).sum := by decide
  have hdescent : baseEnd_169355 < baseStart_169355 := by decide
  rcases family_descends (prefixWord ++ tailWord_169355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169374 : List Nat := [4, 3, 1, 2, 2, 2, 2, 6]
def baseStart_169374 : Nat := 118140960795 + 169374 * 2 ^ 59
def prefixEnd_169374 : Nat := 4983230072969 + 3 ^ 40 * 169374 * 2
def baseEnd_169374 : Nat := 6442242398127819047857

theorem tailTrace_169374 : CollatzResearch.WordTrace tailWord_169374 prefixEnd_169374 6442242398127819047857 := by
  unfold tailWord_169374
  simp only [CollatzResearch.WordTrace]
  refine ⟨772197161049299952666397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4118384858929599747554117 772197161049299952666397)
  ·
    refine ⟨289573935393487482249899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 772197161049299952666397 289573935393487482249899)
    ·
      refine ⟨434360903090231223374849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289573935393487482249899 434360903090231223374849)
      ·
        refine ⟨325770677317673417531137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434360903090231223374849 325770677317673417531137)
        ·
          refine ⟨244328007988255063148353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325770677317673417531137 244328007988255063148353)
          ·
            refine ⟨183246005991191297361265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244328007988255063148353 183246005991191297361265)
            ·
              refine ⟨137434504493393473020949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183246005991191297361265 137434504493393473020949)
              ·
                refine ⟨6442242398127819047857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 137434504493393473020949 6442242398127819047857)
                ·
                  rfl

theorem cell22_169374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_169374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169374 prefixEnd_169374 := by exact prefixLift 169374
  have htrace : WordTrace (prefixWord ++ tailWord_169374) baseStart_169374 baseEnd_169374 := by
    simpa [prefixWord, tailWord_169374, baseEnd_169374] using wordTrace_append hprefix tailTrace_169374
  have hstable : (prefixWord ++ tailWord_169374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169374).length < 2 ^ (prefixWord ++ tailWord_169374).sum := by decide
  have hdescent : baseEnd_169374 < baseStart_169374 := by decide
  rcases family_descends (prefixWord ++ tailWord_169374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169445 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 3, 5]
def baseStart_169445 : Nat := 118140960795 + 169445 * 2 ^ 59
def prefixEnd_169445 : Nat := 4983230072969 + 3 ^ 40 * 169445 * 2
def baseEnd_169445 : Nat := 58004486334129852905495

theorem tailTrace_169445 : CollatzResearch.WordTrace tailWord_169445 prefixEnd_169445 58004486334129852905495 := by
  unfold tailWord_169445
  simp only [CollatzResearch.WordTrace]
  refine ⟨6180166871137178747165789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4120111247424785831443859 6180166871137178747165789)
  ·
    refine ⟨2317562576676442030187171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6180166871137178747165789 2317562576676442030187171)
    ·
      refine ⟨3476343865014663045280757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2317562576676442030187171 3476343865014663045280757)
      ·
        refine ⟨325907237345124660495071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3476343865014663045280757 325907237345124660495071)
        ·
          refine ⟨488860856017686990742607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325907237345124660495071 488860856017686990742607)
          ·
            refine ⟨733291284026530486113911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488860856017686990742607 733291284026530486113911)
            ·
              refine ⟨1099936926039795729170867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733291284026530486113911 1099936926039795729170867)
              ·
                refine ⟨1649905389059693593756301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099936926039795729170867 1649905389059693593756301)
                ·
                  refine ⟨618714520897385097658613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1649905389059693593756301 618714520897385097658613)
                  ·
                    refine ⟨58004486334129852905495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 618714520897385097658613 58004486334129852905495)
                    ·
                      rfl

theorem cell22_169445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_169445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169445 prefixEnd_169445 := by exact prefixLift 169445
  have htrace : WordTrace (prefixWord ++ tailWord_169445) baseStart_169445 baseEnd_169445 := by
    simpa [prefixWord, tailWord_169445, baseEnd_169445] using wordTrace_append hprefix tailTrace_169445
  have hstable : (prefixWord ++ tailWord_169445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169445).length < 2 ^ (prefixWord ++ tailWord_169445).sum := by decide
  have hdescent : baseEnd_169445 < baseStart_169445 := by decide
  rcases family_descends (prefixWord ++ tailWord_169445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169464 : List Nat := [2, 1, 2, 1, 1, 7, 2, 2, 4]
def baseStart_169464 : Nat := 118140960795 + 169464 * 2 ^ 59
def prefixEnd_169464 : Nat := 4983230072969 + 3 ^ 40 * 169464 * 2
def baseEnd_169464 : Nat := 19336996807473378893479

theorem tailTrace_169464 : CollatzResearch.WordTrace tailWord_169464 prefixEnd_169464 19336996807473378893479 := by
  unfold tailWord_169464
  simp only [CollatzResearch.WordTrace]
  refine ⟨3090429929034172496053723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4120573238712229994738297 3090429929034172496053723)
  ·
    refine ⟨4635644893551258744080585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3090429929034172496053723 4635644893551258744080585)
    ·
      refine ⟨3476733670163444058060439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4635644893551258744080585 3476733670163444058060439)
      ·
        refine ⟨5215100505245166087090659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3476733670163444058060439 5215100505245166087090659)
        ·
          refine ⟨7822650757867749130635989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5215100505245166087090659 7822650757867749130635989)
          ·
            refine ⟨183343377137525370249281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 7822650757867749130635989 183343377137525370249281)
            ·
              refine ⟨137507532853144027686961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183343377137525370249281 137507532853144027686961)
              ·
                refine ⟨103130649639858020765221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137507532853144027686961 103130649639858020765221)
                ·
                  refine ⟨19336996807473378893479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103130649639858020765221 19336996807473378893479)
                  ·
                    rfl

theorem cell22_169464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 4].length) (baseStart_169464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169464 prefixEnd_169464 := by exact prefixLift 169464
  have htrace : WordTrace (prefixWord ++ tailWord_169464) baseStart_169464 baseEnd_169464 := by
    simpa [prefixWord, tailWord_169464, baseEnd_169464] using wordTrace_append hprefix tailTrace_169464
  have hstable : (prefixWord ++ tailWord_169464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169464).length < 2 ^ (prefixWord ++ tailWord_169464).sum := by decide
  have hdescent : baseEnd_169464 < baseStart_169464 := by decide
  rcases family_descends (prefixWord ++ tailWord_169464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169535 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 2, 5]
def baseStart_169535 : Nat := 118140960795 + 169535 * 2 ^ 59
def prefixEnd_169535 : Nat := 4983230072969 + 3 ^ 40 * 169535 * 2
def baseEnd_169535 : Nat := 58035295173399618155219

theorem tailTrace_169535 : CollatzResearch.WordTrace tailWord_169535 prefixEnd_169535 58035295173399618155219 := by
  unfold tailWord_169535
  simp only [CollatzResearch.WordTrace]
  refine ⟨6183449440811124117942059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4122299627207416078628039 6183449440811124117942059)
  ·
    refine ⟨9275174161216686176913089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6183449440811124117942059 9275174161216686176913089)
    ·
      refine ⟨6956380620912514632684817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9275174161216686176913089 6956380620912514632684817)
      ·
        refine ⟨5217285465684385974513613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6956380620912514632684817 5217285465684385974513613)
        ·
          refine ⟨1956482049631644740442605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5217285465684385974513613 1956482049631644740442605)
          ·
            refine ⟨733680768611866777665977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1956482049631644740442605 733680768611866777665977)
            ·
              refine ⟨550260576458900083249483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733680768611866777665977 550260576458900083249483)
              ·
                refine ⟨825390864688350124874225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550260576458900083249483 825390864688350124874225)
                ·
                  refine ⟨619043148516262593655669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 825390864688350124874225 619043148516262593655669)
                  ·
                    refine ⟨58035295173399618155219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 619043148516262593655669 58035295173399618155219)
                    ·
                      rfl

theorem cell22_169535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_169535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169535 prefixEnd_169535 := by exact prefixLift 169535
  have htrace : WordTrace (prefixWord ++ tailWord_169535) baseStart_169535 baseEnd_169535 := by
    simpa [prefixWord, tailWord_169535, baseEnd_169535] using wordTrace_append hprefix tailTrace_169535
  have hstable : (prefixWord ++ tailWord_169535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169535).length < 2 ^ (prefixWord ++ tailWord_169535).sum := by decide
  have hdescent : baseEnd_169535 < baseStart_169535 := by decide
  rcases family_descends (prefixWord ++ tailWord_169535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169595 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 4, 4]
def baseStart_169595 : Nat := 118140960795 + 169595 * 2 ^ 59
def prefixEnd_169595 : Nat := 4983230072969 + 3 ^ 40 * 169595 * 2
def baseEnd_169595 : Nat := 58055834399579461655035

theorem tailTrace_169595 : CollatzResearch.WordTrace tailWord_169595 prefixEnd_169595 58055834399579461655035 := by
  unfold tailWord_169595
  simp only [CollatzResearch.WordTrace]
  refine ⟨6185637820593754365126239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4123758547062502910084159 6185637820593754365126239)
  ·
    refine ⟨9278456730890631547689359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6185637820593754365126239 9278456730890631547689359)
    ·
      refine ⟨13917685096335947321534039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9278456730890631547689359 13917685096335947321534039)
      ·
        refine ⟨20876527644503920982301059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13917685096335947321534039 20876527644503920982301059)
        ·
          refine ⟨31314791466755881473451589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20876527644503920982301059 31314791466755881473451589)
          ·
            refine ⟨5871523400016727776272173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31314791466755881473451589 5871523400016727776272173)
            ·
              refine ⟨2201821275006272916102065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5871523400016727776272173 2201821275006272916102065)
              ·
                refine ⟨1651365956254704687076549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2201821275006272916102065 1651365956254704687076549)
                ·
                  refine ⟨309631116797757128826853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1651365956254704687076549 309631116797757128826853)
                  ·
                    refine ⟨58055834399579461655035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 309631116797757128826853 58055834399579461655035)
                    ·
                      rfl

theorem cell22_169595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 4].length) (baseStart_169595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169595 prefixEnd_169595 := by exact prefixLift 169595
  have htrace : WordTrace (prefixWord ++ tailWord_169595) baseStart_169595 baseEnd_169595 := by
    simpa [prefixWord, tailWord_169595, baseEnd_169595] using wordTrace_append hprefix tailTrace_169595
  have hstable : (prefixWord ++ tailWord_169595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169595).length < 2 ^ (prefixWord ++ tailWord_169595).sum := by decide
  have hdescent : baseEnd_169595 < baseStart_169595 := by decide
  rcases family_descends (prefixWord ++ tailWord_169595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169612 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 2, 4]
def baseStart_169612 : Nat := 118140960795 + 169612 * 2 ^ 59
def prefixEnd_169612 : Nat := 4983230072969 + 3 ^ 40 * 169612 * 2
def baseEnd_169612 : Nat := 58061653846997083979983

theorem tailTrace_169612 : CollatzResearch.WordTrace tailWord_169612 prefixEnd_169612 58061653846997083979983 := by
  unfold tailWord_169612
  simp only [CollatzResearch.WordTrace]
  refine ⟨3093128930766083134247545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4124171907688110845663393 3093128930766083134247545)
  ·
    refine ⟨2319846698074562350685659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3093128930766083134247545 2319846698074562350685659)
    ·
      refine ⟨3479770047111843526028489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2319846698074562350685659 3479770047111843526028489)
      ·
        refine ⟨2609827535333882644521367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3479770047111843526028489 2609827535333882644521367)
        ·
          refine ⟨3914741303000823966782051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609827535333882644521367 3914741303000823966782051)
          ·
            refine ⟨5872111954501235950173077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914741303000823966782051 5872111954501235950173077)
            ·
              refine ⟨275255247867245435164363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5872111954501235950173077 275255247867245435164363)
              ·
                refine ⟨412882871800868152746545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275255247867245435164363 412882871800868152746545)
                ·
                  refine ⟨309662153850651114559909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412882871800868152746545 309662153850651114559909)
                  ·
                    refine ⟨58061653846997083979983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 309662153850651114559909 58061653846997083979983)
                    ·
                      rfl

theorem cell22_169612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_169612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169612 prefixEnd_169612 := by exact prefixLift 169612
  have htrace : WordTrace (prefixWord ++ tailWord_169612) baseStart_169612 baseEnd_169612 := by
    simpa [prefixWord, tailWord_169612, baseEnd_169612] using wordTrace_append hprefix tailTrace_169612
  have hstable : (prefixWord ++ tailWord_169612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169612).length < 2 ^ (prefixWord ++ tailWord_169612).sum := by decide
  have hdescent : baseEnd_169612 < baseStart_169612 := by decide
  rcases family_descends (prefixWord ++ tailWord_169612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169689 : List Nat := [1, 2, 1, 2, 3, 5, 1, 2, 5]
def baseStart_169689 : Nat := 118140960795 + 169689 * 2 ^ 59
def prefixEnd_169689 : Nat := 4983230072969 + 3 ^ 40 * 169689 * 2
def baseEnd_169689 : Nat := 19362670840198183268249

theorem tailTrace_169689 : CollatzResearch.WordTrace tailWord_169689 prefixEnd_169689 19362670840198183268249 := by
  unfold tailWord_169689
  simp only [CollatzResearch.WordTrace]
  refine ⟨6189066282253208419048121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4126044188168805612698747 6189066282253208419048121)
  ·
    refine ⟨4641799711689906314286091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6189066282253208419048121 4641799711689906314286091)
    ·
      refine ⟨6962699567534859471429137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4641799711689906314286091 6962699567534859471429137)
      ·
        refine ⟨5222024675651144603571853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6962699567534859471429137 5222024675651144603571853)
        ·
          refine ⟨1958259253369179226339445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5222024675651144603571853 1958259253369179226339445)
          ·
            refine ⟨183586805003360552469323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1958259253369179226339445 183586805003360552469323)
            ·
              refine ⟨275380207505040828703985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183586805003360552469323 275380207505040828703985)
              ·
                refine ⟨206535155628780621527989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275380207505040828703985 206535155628780621527989)
                ·
                  refine ⟨19362670840198183268249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 206535155628780621527989 19362670840198183268249)
                  ·
                    rfl

theorem cell22_169689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 5].length) (baseStart_169689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169689 prefixEnd_169689 := by exact prefixLift 169689
  have htrace : WordTrace (prefixWord ++ tailWord_169689) baseStart_169689 baseEnd_169689 := by
    simpa [prefixWord, tailWord_169689, baseEnd_169689] using wordTrace_append hprefix tailTrace_169689
  have hstable : (prefixWord ++ tailWord_169689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169689).length < 2 ^ (prefixWord ++ tailWord_169689).sum := by decide
  have hdescent : baseEnd_169689 < baseStart_169689 := by decide
  rcases family_descends (prefixWord ++ tailWord_169689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169693 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 3, 3]
def baseStart_169693 : Nat := 118140960795 + 169693 * 2 ^ 59
def prefixEnd_169693 : Nat := 4983230072969 + 3 ^ 40 * 169693 * 2
def baseEnd_169693 : Nat := 58089381802339872704735

theorem tailTrace_169693 : CollatzResearch.WordTrace tailWord_169693 prefixEnd_169693 58089381802339872704735 := by
  unfold tailWord_169693
  simp only [CollatzResearch.WordTrace]
  refine ⟨6189212174238717102193733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4126141449492478068129155 6189212174238717102193733)
  ·
    refine ⟨1160477282669759456661325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6189212174238717102193733 1160477282669759456661325)
    ·
      refine ⟨435178981001159796247997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1160477282669759456661325 435178981001159796247997)
      ·
        refine ⟨163192117875434923592999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 435178981001159796247997 163192117875434923592999)
        ·
          refine ⟨244788176813152385389499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163192117875434923592999 244788176813152385389499)
          ·
            refine ⟨367182265219728578084249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244788176813152385389499 367182265219728578084249)
            ·
              refine ⟨275386698914796433563187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367182265219728578084249 275386698914796433563187)
              ·
                refine ⟨413080048372194650344781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275386698914796433563187 413080048372194650344781)
                ·
                  refine ⟨154905018139572993879293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413080048372194650344781 154905018139572993879293)
                  ·
                    refine ⟨58089381802339872704735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 154905018139572993879293 58089381802339872704735)
                    ·
                      rfl

theorem cell22_169693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_169693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169693 prefixEnd_169693 := by exact prefixLift 169693
  have htrace : WordTrace (prefixWord ++ tailWord_169693) baseStart_169693 baseEnd_169693 := by
    simpa [prefixWord, tailWord_169693, baseEnd_169693] using wordTrace_append hprefix tailTrace_169693
  have hstable : (prefixWord ++ tailWord_169693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169693).length < 2 ^ (prefixWord ++ tailWord_169693).sum := by decide
  have hdescent : baseEnd_169693 < baseStart_169693 := by decide
  rcases family_descends (prefixWord ++ tailWord_169693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169749 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 4, 3]
def baseStart_169749 : Nat := 118140960795 + 169749 * 2 ^ 59
def prefixEnd_169749 : Nat := 4983230072969 + 3 ^ 40 * 169749 * 2
def baseEnd_169749 : Nat := 58108551746774393304563

theorem tailTrace_169749 : CollatzResearch.WordTrace tailWord_169749 prefixEnd_169749 58108551746774393304563 := by
  unfold tailWord_169749
  simp only [CollatzResearch.WordTrace]
  refine ⟨6191254662035838666232301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4127503108023892444154867 6191254662035838666232301)
  ·
    refine ⟨2321720498263439499837113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6191254662035838666232301 2321720498263439499837113)
    ·
      refine ⟨1741290373697579624877835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2321720498263439499837113 1741290373697579624877835)
      ·
        refine ⟨2611935560546369437316753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1741290373697579624877835 2611935560546369437316753)
        ·
          refine ⟨1958951670409777077987565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2611935560546369437316753 1958951670409777077987565)
          ·
            refine ⟨734606876403666404245337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1958951670409777077987565 734606876403666404245337)
            ·
              refine ⟨550955157302749803184003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734606876403666404245337 550955157302749803184003)
              ·
                refine ⟨826432735954124704776005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550955157302749803184003 826432735954124704776005)
                ·
                  refine ⟨154956137991398382145501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 826432735954124704776005 154956137991398382145501)
                  ·
                    refine ⟨58108551746774393304563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 154956137991398382145501 58108551746774393304563)
                    ·
                      rfl

theorem cell22_169749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_169749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169749 prefixEnd_169749 := by exact prefixLift 169749
  have htrace : WordTrace (prefixWord ++ tailWord_169749) baseStart_169749 baseEnd_169749 := by
    simpa [prefixWord, tailWord_169749, baseEnd_169749] using wordTrace_append hprefix tailTrace_169749
  have hstable : (prefixWord ++ tailWord_169749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169749).length < 2 ^ (prefixWord ++ tailWord_169749).sum := by decide
  have hdescent : baseEnd_169749 < baseStart_169749 := by decide
  rcases family_descends (prefixWord ++ tailWord_169749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169781 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 2, 4]
def baseStart_169781 : Nat := 118140960795 + 169781 * 2 ^ 59
def prefixEnd_169781 : Nat := 4983230072969 + 3 ^ 40 * 169781 * 2
def baseEnd_169781 : Nat := 58119506000736976504465

theorem tailTrace_169781 : CollatzResearch.WordTrace tailWord_169781 prefixEnd_169781 58119506000736976504465 := by
  unfold tailWord_169781
  simp only [CollatzResearch.WordTrace]
  refine ⟨6192421797919908131397197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4128281198613272087598131 6192421797919908131397197)
  ·
    refine ⟨2322158174219965549273949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6192421797919908131397197 2322158174219965549273949)
    ·
      refine ⟨870809315332487080977731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2322158174219965549273949 870809315332487080977731)
      ·
        refine ⟨1306213972998730621466597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 870809315332487080977731 1306213972998730621466597)
        ·
          refine ⟨244915119937261991524987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1306213972998730621466597 244915119937261991524987)
          ·
            refine ⟨367372679905892987287481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244915119937261991524987 367372679905892987287481)
            ·
              refine ⟨275529509929419740465611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367372679905892987287481 275529509929419740465611)
              ·
                refine ⟨413294264894129610698417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275529509929419740465611 413294264894129610698417)
                ·
                  refine ⟨309970698670597208023813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413294264894129610698417 309970698670597208023813)
                  ·
                    refine ⟨58119506000736976504465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 309970698670597208023813 58119506000736976504465)
                    ·
                      rfl

theorem cell22_169781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_169781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169781 prefixEnd_169781 := by exact prefixLift 169781
  have htrace : WordTrace (prefixWord ++ tailWord_169781) baseStart_169781 baseEnd_169781 := by
    simpa [prefixWord, tailWord_169781, baseEnd_169781] using wordTrace_append hprefix tailTrace_169781
  have hstable : (prefixWord ++ tailWord_169781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169781).length < 2 ^ (prefixWord ++ tailWord_169781).sum := by decide
  have hdescent : baseEnd_169781 < baseStart_169781 := by decide
  rcases family_descends (prefixWord ++ tailWord_169781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169798 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_169798 : Nat := 118140960795 + 169798 * 2 ^ 59
def prefixEnd_169798 : Nat := 4983230072969 + 3 ^ 40 * 169798 * 2
def baseEnd_169798 : Nat := 58125325448154598829413

theorem tailTrace_169798 : CollatzResearch.WordTrace tailWord_169798 prefixEnd_169798 58125325448154598829413 := by
  unfold tailWord_169798
  simp only [CollatzResearch.WordTrace]
  refine ⟨193532557464322501086439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4128694559238880023177365 193532557464322501086439)
  ·
    refine ⟨290298836196483751629659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193532557464322501086439 290298836196483751629659)
    ·
      refine ⟨435448254294725627444489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290298836196483751629659 435448254294725627444489)
      ·
        refine ⟨326586190721044220583367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435448254294725627444489 326586190721044220583367)
        ·
          refine ⟨489879286081566330875051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326586190721044220583367 489879286081566330875051)
          ·
            refine ⟨734818929122349496312577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489879286081566330875051 734818929122349496312577)
            ·
              refine ⟨551114196841762122234433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734818929122349496312577 551114196841762122234433)
              ·
                refine ⟨413335647631321591675825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 551114196841762122234433 413335647631321591675825)
                ·
                  refine ⟨310001735723491193756869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413335647631321591675825 310001735723491193756869)
                  ·
                    refine ⟨58125325448154598829413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 310001735723491193756869 58125325448154598829413)
                    ·
                      rfl

theorem cell22_169798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_169798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169798 prefixEnd_169798 := by exact prefixLift 169798
  have htrace : WordTrace (prefixWord ++ tailWord_169798) baseStart_169798 baseEnd_169798 := by
    simpa [prefixWord, tailWord_169798, baseEnd_169798] using wordTrace_append hprefix tailTrace_169798
  have hstable : (prefixWord ++ tailWord_169798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169798).length < 2 ^ (prefixWord ++ tailWord_169798).sum := by decide
  have hdescent : baseEnd_169798 < baseStart_169798 := by decide
  rcases family_descends (prefixWord ++ tailWord_169798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169824 : List Nat := [2, 1, 1, 3, 3, 2, 2, 3, 5]
def baseStart_169824 : Nat := 118140960795 + 169824 * 2 ^ 59
def prefixEnd_169824 : Nat := 4983230072969 + 3 ^ 40 * 169824 * 2
def baseEnd_169824 : Nat := 19378075259833065893111

theorem tailTrace_169824 : CollatzResearch.WordTrace tailWord_169824 prefixEnd_169824 19378075259833065893111 := by
  unfold tailWord_169824
  simp only [CollatzResearch.WordTrace]
  refine ⟨3096995068382063237606263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4129326757842750983475017 3096995068382063237606263)
  ·
    refine ⟨4645492602573094856409395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3096995068382063237606263 4645492602573094856409395)
    ·
      refine ⟨6968238903859642284614093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4645492602573094856409395 6968238903859642284614093)
      ·
        refine ⟨2613089588947365856730285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6968238903859642284614093 2613089588947365856730285)
        ·
          refine ⟨979908595855262196273857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2613089588947365856730285 979908595855262196273857)
          ·
            refine ⟨734931446891446647205393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 979908595855262196273857 734931446891446647205393)
            ·
              refine ⟨551198585168584985404045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734931446891446647205393 551198585168584985404045)
              ·
                refine ⟨206699469438219369526517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 551198585168584985404045 206699469438219369526517)
                ·
                  refine ⟨19378075259833065893111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 206699469438219369526517 19378075259833065893111)
                  ·
                    rfl

theorem cell22_169824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 5].length) (baseStart_169824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169824 prefixEnd_169824 := by exact prefixLift 169824
  have htrace : WordTrace (prefixWord ++ tailWord_169824) baseStart_169824 baseEnd_169824 := by
    simpa [prefixWord, tailWord_169824, baseEnd_169824] using wordTrace_append hprefix tailTrace_169824
  have hstable : (prefixWord ++ tailWord_169824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169824).length < 2 ^ (prefixWord ++ tailWord_169824).sum := by decide
  have hdescent : baseEnd_169824 < baseStart_169824 := by decide
  rcases family_descends (prefixWord ++ tailWord_169824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169991 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 2, 5]
def baseStart_169991 : Nat := 118140960795 + 169991 * 2 ^ 59
def prefixEnd_169991 : Nat := 4983230072969 + 3 ^ 40 * 169991 * 2
def baseEnd_169991 : Nat := 58191393292366428753821

theorem tailTrace_169991 : CollatzResearch.WordTrace tailWord_169991 prefixEnd_169991 58191393292366428753821 := by
  unfold tailWord_169991
  simp only [CollatzResearch.WordTrace]
  refine ⟨6200081127159113996541827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4133387418106075997694551 6200081127159113996541827)
  ·
    refine ⟨9300121690738670994812741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6200081127159113996541827 9300121690738670994812741)
    ·
      refine ⟨1743772817013500811527389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9300121690738670994812741 1743772817013500811527389)
      ·
        refine ⟨653914806380062804322771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1743772817013500811527389 653914806380062804322771)
        ·
          refine ⟨980872209570094206484157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653914806380062804322771 980872209570094206484157)
          ·
            refine ⟨367827078588785327431559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 980872209570094206484157 367827078588785327431559)
            ·
              refine ⟨551740617883177991147339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367827078588785327431559 551740617883177991147339)
              ·
                refine ⟨827610926824766986721009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551740617883177991147339 827610926824766986721009)
                ·
                  refine ⟨620708195118575240040757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 827610926824766986721009 620708195118575240040757)
                  ·
                    refine ⟨58191393292366428753821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 620708195118575240040757 58191393292366428753821)
                    ·
                      rfl

theorem cell22_169991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_169991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_169991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_169991 prefixEnd_169991 := by exact prefixLift 169991
  have htrace : WordTrace (prefixWord ++ tailWord_169991) baseStart_169991 baseEnd_169991 := by
    simpa [prefixWord, tailWord_169991, baseEnd_169991] using wordTrace_append hprefix tailTrace_169991
  have hstable : (prefixWord ++ tailWord_169991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169991).length < 2 ^ (prefixWord ++ tailWord_169991).sum := by decide
  have hdescent : baseEnd_169991 < baseStart_169991 := by decide
  rcases family_descends (prefixWord ++ tailWord_169991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170038 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_170038 : Nat := 118140960795 + 170038 * 2 ^ 59
def prefixEnd_170038 : Nat := 4983230072969 + 3 ^ 40 * 170038 * 2
def baseEnd_170038 : Nat := 19402494117624657609559

theorem tailTrace_170038 : CollatzResearch.WordTrace tailWord_170038 prefixEnd_170038 19402494117624657609559 := by
  unfold tailWord_170038
  simp only [CollatzResearch.WordTrace]
  refine ⟨387612209874302563968923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4134530238659227349001845 387612209874302563968923)
  ·
    refine ⟨581418314811453845953385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 387612209874302563968923 581418314811453845953385)
    ·
      refine ⟨436063736108590384465039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 581418314811453845953385 436063736108590384465039)
      ·
        refine ⟨654095604162885576697559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436063736108590384465039 654095604162885576697559)
        ·
          refine ⟨981143406244328365046339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654095604162885576697559 981143406244328365046339)
          ·
            refine ⟨1471715109366492547569509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981143406244328365046339 1471715109366492547569509)
            ·
              refine ⟨275946583006217352669283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1471715109366492547569509 275946583006217352669283)
              ·
                refine ⟨413919874509326029003925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275946583006217352669283 413919874509326029003925)
                ·
                  refine ⟨19402494117624657609559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 413919874509326029003925 19402494117624657609559)
                  ·
                    rfl

theorem cell22_170038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_170038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170038 prefixEnd_170038 := by exact prefixLift 170038
  have htrace : WordTrace (prefixWord ++ tailWord_170038) baseStart_170038 baseEnd_170038 := by
    simpa [prefixWord, tailWord_170038, baseEnd_170038] using wordTrace_append hprefix tailTrace_170038
  have hstable : (prefixWord ++ tailWord_170038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170038).length < 2 ^ (prefixWord ++ tailWord_170038).sum := by decide
  have hdescent : baseEnd_170038 < baseStart_170038 := by decide
  rcases family_descends (prefixWord ++ tailWord_170038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170134 : List Nat := [5, 3, 2, 1, 2, 9]
def baseStart_170134 : Nat := 118140960795 + 170134 * 2 ^ 59
def prefixEnd_170134 : Nat := 4983230072969 + 3 ^ 40 * 170134 * 2
def baseEnd_170134 : Nat := 719016606355082992943

theorem tailTrace_170134 : CollatzResearch.WordTrace tailWord_170134 prefixEnd_170134 719016606355082992943 := by
  unfold tailWord_170134
  simp only [CollatzResearch.WordTrace]
  refine ⟨387831047852565588687341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4136864510427366279331637 387831047852565588687341)
  ·
    refine ⟨145436642944712095757753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 387831047852565588687341 145436642944712095757753)
    ·
      refine ⟨109077482208534071818315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145436642944712095757753 109077482208534071818315)
      ·
        refine ⟨163616223312801107727473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109077482208534071818315 163616223312801107727473)
        ·
          refine ⟨122712167484600830795605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163616223312801107727473 122712167484600830795605)
          ·
            refine ⟨719016606355082992943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 122712167484600830795605 719016606355082992943)
            ·
              rfl

theorem cell22_170134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 9].length) (baseStart_170134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170134 prefixEnd_170134 := by exact prefixLift 170134
  have htrace : WordTrace (prefixWord ++ tailWord_170134) baseStart_170134 baseEnd_170134 := by
    simpa [prefixWord, tailWord_170134, baseEnd_170134] using wordTrace_append hprefix tailTrace_170134
  have hstable : (prefixWord ++ tailWord_170134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170134).length < 2 ^ (prefixWord ++ tailWord_170134).sum := by decide
  have hdescent : baseEnd_170134 < baseStart_170134 := by decide
  rcases family_descends (prefixWord ++ tailWord_170134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170190 : List Nat := [4, 1, 1, 1, 4, 1, 1, 5, 4]
def baseStart_170190 : Nat := 118140960795 + 170190 * 2 ^ 59
def prefixEnd_170190 : Nat := 4983230072969 + 3 ^ 40 * 170190 * 2
def baseEnd_170190 : Nat := 19419838353065414342737

theorem tailTrace_170190 : CollatzResearch.WordTrace tailWord_170190 prefixEnd_170190 19419838353065414342737 := by
  unfold tailWord_170190
  simp only [CollatzResearch.WordTrace]
  refine ⟨775917406679771372879503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4138226168958780655357349 775917406679771372879503)
  ·
    refine ⟨1163876110019657059319255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 775917406679771372879503 1163876110019657059319255)
    ·
      refine ⟨1745814165029485588978883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1163876110019657059319255 1745814165029485588978883)
      ·
        refine ⟨2618721247544228383468325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1745814165029485588978883 2618721247544228383468325)
        ·
          refine ⟨491010233914542821900311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2618721247544228383468325 491010233914542821900311)
          ·
            refine ⟨736515350871814232850467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491010233914542821900311 736515350871814232850467)
            ·
              refine ⟨1104773026307721349275701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736515350871814232850467 1104773026307721349275701)
              ·
                refine ⟨103572471216348876494597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1104773026307721349275701 103572471216348876494597)
                ·
                  refine ⟨19419838353065414342737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103572471216348876494597 19419838353065414342737)
                  ·
                    rfl

theorem cell22_170190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_170190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170190 prefixEnd_170190 := by exact prefixLift 170190
  have htrace : WordTrace (prefixWord ++ tailWord_170190) baseStart_170190 baseEnd_170190 := by
    simpa [prefixWord, tailWord_170190, baseEnd_170190] using wordTrace_append hprefix tailTrace_170190
  have hstable : (prefixWord ++ tailWord_170190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170190).length < 2 ^ (prefixWord ++ tailWord_170190).sum := by decide
  have hdescent : baseEnd_170190 < baseStart_170190 := by decide
  rcases family_descends (prefixWord ++ tailWord_170190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170233 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 5, 3]
def baseStart_170233 : Nat := 118140960795 + 170233 * 2 ^ 59
def prefixEnd_170233 : Nat := 4983230072969 + 3 ^ 40 * 170233 * 2
def baseEnd_170233 : Nat := 58274234837958464203079

theorem tailTrace_170233 : CollatzResearch.WordTrace tailWord_170233 prefixEnd_170233 58274234837958464203079 := by
  unfold tailWord_170233
  simp only [CollatzResearch.WordTrace]
  refine ⟨6208907592282389326851353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4139271728188259551234235 6208907592282389326851353)
  ·
    refine ⟨4656680694211791995138515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6208907592282389326851353 4656680694211791995138515)
    ·
      refine ⟨6985021041317687992707773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4656680694211791995138515 6985021041317687992707773)
      ·
        refine ⟨2619382890494132997265415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6985021041317687992707773 2619382890494132997265415)
        ·
          refine ⟨3929074335741199495898123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2619382890494132997265415 3929074335741199495898123)
          ·
            refine ⟨5893611503611799243847185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3929074335741199495898123 5893611503611799243847185)
            ·
              refine ⟨4420208627708849432885389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5893611503611799243847185 4420208627708849432885389)
              ·
                refine ⟨1657578235390818537332021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4420208627708849432885389 1657578235390818537332021)
                ·
                  refine ⟨155397959567889237874877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1657578235390818537332021 155397959567889237874877)
                  ·
                    refine ⟨58274234837958464203079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155397959567889237874877 58274234837958464203079)
                    ·
                      rfl

theorem cell22_170233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 3].length) (baseStart_170233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170233 prefixEnd_170233 := by exact prefixLift 170233
  have htrace : WordTrace (prefixWord ++ tailWord_170233) baseStart_170233 baseEnd_170233 := by
    simpa [prefixWord, tailWord_170233, baseEnd_170233] using wordTrace_append hprefix tailTrace_170233
  have hstable : (prefixWord ++ tailWord_170233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170233).length < 2 ^ (prefixWord ++ tailWord_170233).sum := by decide
  have hdescent : baseEnd_170233 < baseStart_170233 := by decide
  rcases family_descends (prefixWord ++ tailWord_170233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170263 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 7]
def baseStart_170263 : Nat := 118140960795 + 170263 * 2 ^ 59
def prefixEnd_170263 : Nat := 4983230072969 + 3 ^ 40 * 170263 * 2
def baseEnd_170263 : Nat := 19428168150349461984329

theorem tailTrace_170263 : CollatzResearch.WordTrace tailWord_170263 prefixEnd_170263 19428168150349461984329 := by
  unfold tailWord_170263
  simp only [CollatzResearch.WordTrace]
  refine ⟨6210001782173704450443443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4140001188115802966962295 6210001782173704450443443)
  ·
    refine ⟨9315002673260556675665165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6210001782173704450443443 9315002673260556675665165)
    ·
      refine ⟨3493126002472708753374437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9315002673260556675665165 3493126002472708753374437)
      ·
        refine ⟨654961125463632891257707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3493126002472708753374437 654961125463632891257707)
        ·
          refine ⟨982441688195449336886561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654961125463632891257707 982441688195449336886561)
          ·
            refine ⟨736831266146587002664921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 982441688195449336886561 736831266146587002664921)
            ·
              refine ⟨552623449609940251998691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736831266146587002664921 552623449609940251998691)
              ·
                refine ⟨828935174414910377998037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552623449609940251998691 828935174414910377998037)
                ·
                  refine ⟨19428168150349461984329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 828935174414910377998037 19428168150349461984329)
                  ·
                    rfl

theorem cell22_170263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 7].length) (baseStart_170263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170263 prefixEnd_170263 := by exact prefixLift 170263
  have htrace : WordTrace (prefixWord ++ tailWord_170263) baseStart_170263 baseEnd_170263 := by
    simpa [prefixWord, tailWord_170263, baseEnd_170263] using wordTrace_append hprefix tailTrace_170263
  have hstable : (prefixWord ++ tailWord_170263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170263).length < 2 ^ (prefixWord ++ tailWord_170263).sum := by decide
  have hdescent : baseEnd_170263 < baseStart_170263 := by decide
  rcases family_descends (prefixWord ++ tailWord_170263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170340 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_170340 : Nat := 118140960795 + 170340 * 2 ^ 59
def prefixEnd_170340 : Nat := 4983230072969 + 3 ^ 40 * 170340 * 2
def baseEnd_170340 : Nat := 58310863124645851777751

theorem tailTrace_170340 : CollatzResearch.WordTrace tailWord_170340 prefixEnd_170340 58310863124645851777751 := by
  unfold tailWord_170340
  simp only [CollatzResearch.WordTrace]
  refine ⟨3106405101447373300498237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4141873468596497733997649 3106405101447373300498237)
  ·
    refine ⟨1164901913042764987686839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3106405101447373300498237 1164901913042764987686839)
    ·
      refine ⟨1747352869564147481530259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1164901913042764987686839 1747352869564147481530259)
      ·
        refine ⟨2621029304346221222295389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1747352869564147481530259 2621029304346221222295389)
        ·
          refine ⟨982885989129832958360771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2621029304346221222295389 982885989129832958360771)
          ·
            refine ⟨1474328983694749437541157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982885989129832958360771 1474328983694749437541157)
            ·
              refine ⟨276436684442765519538967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1474328983694749437541157 276436684442765519538967)
              ·
                refine ⟨414655026664148279308451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276436684442765519538967 414655026664148279308451)
                ·
                  refine ⟨621982539996222418962677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414655026664148279308451 621982539996222418962677)
                  ·
                    refine ⟨58310863124645851777751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 621982539996222418962677 58310863124645851777751)
                    ·
                      rfl

theorem cell22_170340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_170340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170340 prefixEnd_170340 := by exact prefixLift 170340
  have htrace : WordTrace (prefixWord ++ tailWord_170340) baseStart_170340 baseEnd_170340 := by
    simpa [prefixWord, tailWord_170340, baseEnd_170340] using wordTrace_append hprefix tailTrace_170340
  have hstable : (prefixWord ++ tailWord_170340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170340).length < 2 ^ (prefixWord ++ tailWord_170340).sum := by decide
  have hdescent : baseEnd_170340 < baseStart_170340 := by decide
  rcases family_descends (prefixWord ++ tailWord_170340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170402 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_170402 : Nat := 118140960795 + 170402 * 2 ^ 59
def prefixEnd_170402 : Nat := 4983230072969 + 3 ^ 40 * 170402 * 2
def baseEnd_170402 : Nat := 58332086991698356727561

theorem tailTrace_170402 : CollatzResearch.WordTrace tailWord_170402 prefixEnd_170402 58332086991698356727561 := by
  unfold tailWord_170402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1553767882167532797438365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4143381019113420793168973 1553767882167532797438365)
  ·
    refine ⟨582662955812824799039387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1553767882167532797438365 582662955812824799039387)
    ·
      refine ⟨873994433719237198559081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 582662955812824799039387 873994433719237198559081)
      ·
        refine ⟨655495825289427898919311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 873994433719237198559081 655495825289427898919311)
        ·
          refine ⟨983243737934141848378967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655495825289427898919311 983243737934141848378967)
          ·
            refine ⟨1474865606901212772568451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983243737934141848378967 1474865606901212772568451)
            ·
              refine ⟨2212298410351819158852677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474865606901212772568451 2212298410351819158852677)
              ·
                refine ⟨414805951940966092284877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2212298410351819158852677 414805951940966092284877)
                ·
                  refine ⟨155552231977862284606829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 414805951940966092284877 155552231977862284606829)
                  ·
                    refine ⟨58332086991698356727561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155552231977862284606829 58332086991698356727561)
                    ·
                      rfl

theorem cell22_170402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_170402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170402 prefixEnd_170402 := by exact prefixLift 170402
  have htrace : WordTrace (prefixWord ++ tailWord_170402) baseStart_170402 baseEnd_170402 := by
    simpa [prefixWord, tailWord_170402, baseEnd_170402] using wordTrace_append hprefix tailTrace_170402
  have hstable : (prefixWord ++ tailWord_170402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170402).length < 2 ^ (prefixWord ++ tailWord_170402).sum := by decide
  have hdescent : baseEnd_170402 < baseStart_170402 := by decide
  rcases family_descends (prefixWord ++ tailWord_170402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
