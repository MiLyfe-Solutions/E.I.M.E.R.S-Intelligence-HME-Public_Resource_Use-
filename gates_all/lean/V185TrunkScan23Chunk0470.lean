import V185TrunkScan23Chunk0469

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2780104 : List Nat := [2, 1, 3, 1, 5, 1, 1, 4, 1, 2, 2]
def baseStart_2780104 : Nat := 118140960795 + 2780104 * 2 ^ 59
def prefixEnd_2780104 : Nat := 4983230072969 + 3 ^ 40 * 2780104 * 2
def baseEnd_2780104 : Nat := 1427529621487296064014541

theorem tailTrace_2780104 : CollatzResearch.WordTrace tailWord_2780104 prefixEnd_2780104 1427529621487296064014541 := by
  unfold tailWord_2780104
  simp only [CollatzResearch.WordTrace]
  refine ⟨50699361560082743403617683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67599148746776991204823577 50699361560082743403617683)
  ·
    refine ⟨76049042340124115105426525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50699361560082743403617683 76049042340124115105426525)
    ·
      refine ⟨28518390877546543164534947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76049042340124115105426525 28518390877546543164534947)
      ·
        refine ⟨42777586316319814746802421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28518390877546543164534947 42777586316319814746802421)
        ·
          refine ⟨4010398717154982632512727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42777586316319814746802421 4010398717154982632512727)
          ·
            refine ⟨6015598075732473948769091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4010398717154982632512727 6015598075732473948769091)
            ·
              refine ⟨9023397113598710923153637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6015598075732473948769091 9023397113598710923153637)
              ·
                refine ⟨1691886958799758298091307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9023397113598710923153637 1691886958799758298091307)
                ·
                  refine ⟨2537830438199637447136961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1691886958799758298091307 2537830438199637447136961)
                  ·
                    refine ⟨1903372828649728085352721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2537830438199637447136961 1903372828649728085352721)
                    ·
                      refine ⟨1427529621487296064014541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1903372828649728085352721 1427529621487296064014541)
                      ·
                        rfl

theorem cell23_2780104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_2780104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780104 prefixEnd_2780104 := by exact prefixLift 2780104
  have htrace : WordTrace (prefixWord ++ tailWord_2780104) baseStart_2780104 baseEnd_2780104 := by
    simpa [prefixWord, tailWord_2780104, baseEnd_2780104] using wordTrace_append hprefix tailTrace_2780104
  have hstable : (prefixWord ++ tailWord_2780104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780104).length < 2 ^ (prefixWord ++ tailWord_2780104).sum := by decide
  have hdescent : baseEnd_2780104 < baseStart_2780104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780113 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 5, 3, 2]
def baseStart_2780113 : Nat := 118140960795 + 2780113 * 2 ^ 59
def prefixEnd_2780113 : Nat := 4983230072969 + 3 ^ 40 * 2780113 * 2
def baseEnd_2780113 : Nat := 1427534242813186528801999

theorem tailTrace_2780113 : CollatzResearch.WordTrace tailWord_2780113 prefixEnd_2780113 1427534242813186528801999 := by
  unfold tailWord_2780113
  simp only [CollatzResearch.WordTrace]
  refine ⟨101399051377132881344312993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67599367584755254229541995 101399051377132881344312993)
  ·
    refine ⟨76049288532849661008234745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101399051377132881344312993 76049288532849661008234745)
    ·
      refine ⟨57036966399637245756176059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76049288532849661008234745 57036966399637245756176059)
      ·
        refine ⟨85555449599455868634264089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57036966399637245756176059 85555449599455868634264089)
        ·
          refine ⟨64166587199591901475698067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85555449599455868634264089 64166587199591901475698067)
          ·
            refine ⟨96249880799387852213547101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64166587199591901475698067 96249880799387852213547101)
            ·
              refine ⟨36093705299770444580080163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96249880799387852213547101 36093705299770444580080163)
              ·
                refine ⟨54140557949655666870120245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36093705299770444580080163 54140557949655666870120245)
                ·
                  refine ⟨5075677307780218769073773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54140557949655666870120245 5075677307780218769073773)
                  ·
                    refine ⟨1903378990417582038402665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5075677307780218769073773 1903378990417582038402665)
                    ·
                      refine ⟨1427534242813186528801999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1903378990417582038402665 1427534242813186528801999)
                      ·
                        rfl

theorem cell23_2780113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 3, 2].length) (baseStart_2780113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780113 prefixEnd_2780113 := by exact prefixLift 2780113
  have htrace : WordTrace (prefixWord ++ tailWord_2780113) baseStart_2780113 baseEnd_2780113 := by
    simpa [prefixWord, tailWord_2780113, baseEnd_2780113] using wordTrace_append hprefix tailTrace_2780113
  have hstable : (prefixWord ++ tailWord_2780113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780113).length < 2 ^ (prefixWord ++ tailWord_2780113).sum := by decide
  have hdescent : baseEnd_2780113 < baseStart_2780113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780120 : List Nat := [2, 1, 2, 2, 2, 3, 2, 3, 2, 1, 3]
def baseStart_2780120 : Nat := 118140960795 + 2780120 * 2 ^ 59
def prefixEnd_2780120 : Nat := 4983230072969 + 3 ^ 40 * 2780120 * 2
def baseEnd_2780120 : Nat := 1427537837177768001414467

theorem tailTrace_2780120 : CollatzResearch.WordTrace tailWord_2780120 prefixEnd_2780120 1427537837177768001414467 := by
  unfold tailWord_2780120
  simp only [CollatzResearch.WordTrace]
  refine ⟨50699653344053760769908907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67599537792071681026545209 50699653344053760769908907)
  ·
    refine ⟨76049480016080641154863361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50699653344053760769908907 76049480016080641154863361)
    ·
      refine ⟨57037110012060480866147521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76049480016080641154863361 57037110012060480866147521)
      ·
        refine ⟨42777832509045360649610641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57037110012060480866147521 42777832509045360649610641)
        ·
          refine ⟨32083374381784020487207981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42777832509045360649610641 32083374381784020487207981)
          ·
            refine ⟨12031265393169007682702993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32083374381784020487207981 12031265393169007682702993)
            ·
              refine ⟨9023449044876755762027245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12031265393169007682702993 9023449044876755762027245)
              ·
                refine ⟨3383793391828783410760217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9023449044876755762027245 3383793391828783410760217)
                ·
                  refine ⟨2537845043871587558070163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3383793391828783410760217 2537845043871587558070163)
                  ·
                    refine ⟨3806767565807381337105245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2537845043871587558070163 3806767565807381337105245)
                    ·
                      refine ⟨1427537837177768001414467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3806767565807381337105245 1427537837177768001414467)
                      ·
                        rfl

theorem cell23_2780120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_2780120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780120 prefixEnd_2780120 := by exact prefixLift 2780120
  have htrace : WordTrace (prefixWord ++ tailWord_2780120) baseStart_2780120 baseEnd_2780120 := by
    simpa [prefixWord, tailWord_2780120, baseEnd_2780120] using wordTrace_append hprefix tailTrace_2780120
  have hstable : (prefixWord ++ tailWord_2780120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780120).length < 2 ^ (prefixWord ++ tailWord_2780120).sum := by decide
  have hdescent : baseEnd_2780120 < baseStart_2780120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780148 : List Nat := [2, 6, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2780148 : Nat := 118140960795 + 2780148 * 2 ^ 59
def prefixEnd_2780148 : Nat := 4983230072969 + 3 ^ 40 * 2780148 * 2
def baseEnd_2780148 : Nat := 475850738212031297288113

theorem tailTrace_2780148 : CollatzResearch.WordTrace tailWord_2780148 prefixEnd_2780148 475850738212031297288113 := by
  unfold tailWord_2780148
  simp only [CollatzResearch.WordTrace]
  refine ⟨50700163966003041160918549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67600218621337388214558065 50700163966003041160918549)
  ·
    refine ⟨2376570185906392554418057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50700163966003041160918549 2376570185906392554418057)
    ·
      refine ⟨1782427639429794415813543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2376570185906392554418057 1782427639429794415813543)
      ·
        refine ⟨2673641459144691623720315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1782427639429794415813543 2673641459144691623720315)
        ·
          refine ⟨4010462188717037435580473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2673641459144691623720315 4010462188717037435580473)
          ·
            refine ⟨3007846641537778076685355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4010462188717037435580473 3007846641537778076685355)
            ·
              refine ⟨4511769962306667115028033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3007846641537778076685355 4511769962306667115028033)
              ·
                refine ⟨3383827471730000336271025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4511769962306667115028033 3383827471730000336271025)
                ·
                  refine ⟨2537870603797500252203269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3383827471730000336271025 2537870603797500252203269)
                  ·
                    refine ⟨475850738212031297288113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2537870603797500252203269 475850738212031297288113)
                    ·
                      rfl

theorem cell23_2780148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2780148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780148 prefixEnd_2780148 := by exact prefixLift 2780148
  have htrace : WordTrace (prefixWord ++ tailWord_2780148) baseStart_2780148 baseEnd_2780148 := by
    simpa [prefixWord, tailWord_2780148, baseEnd_2780148] using wordTrace_append hprefix tailTrace_2780148
  have hstable : (prefixWord ++ tailWord_2780148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780148).length < 2 ^ (prefixWord ++ tailWord_2780148).sum := by decide
  have hdescent : baseEnd_2780148 < baseStart_2780148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780183 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 7]
def baseStart_2780183 : Nat := 118140960795 + 2780183 * 2 ^ 59
def prefixEnd_2780183 : Nat := 4983230072969 + 3 ^ 40 * 2780183 * 2
def baseEnd_2780183 : Nat := 158618909606555694991853

theorem tailTrace_2780183 : CollatzResearch.WordTrace tailWord_2780183 prefixEnd_2780183 158618909606555694991853 := by
  unfold tailWord_2780183
  simp only [CollatzResearch.WordTrace]
  refine ⟨101401604486879283299361203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67601069657919522199574135 101401604486879283299361203)
  ·
    refine ⟨152102406730318924949041805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101401604486879283299361203 152102406730318924949041805)
    ·
      refine ⟨57038402523869596855890677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152102406730318924949041805 57038402523869596855890677)
      ·
        refine ⟨5347350236612774705239751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57038402523869596855890677 5347350236612774705239751)
        ·
          refine ⟨8021025354919162057859627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5347350236612774705239751 8021025354919162057859627)
          ·
            refine ⟨12031538032378743086789441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8021025354919162057859627 12031538032378743086789441)
            ·
              refine ⟨9023653524284057315092081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12031538032378743086789441 9023653524284057315092081)
              ·
                refine ⟨6767740143213042986319061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9023653524284057315092081 6767740143213042986319061)
                ·
                  refine ⟨158618909606555694991853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6767740143213042986319061 158618909606555694991853)
                  ·
                    rfl

theorem cell23_2780183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 7].length) (baseStart_2780183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780183 prefixEnd_2780183 := by exact prefixLift 2780183
  have htrace : WordTrace (prefixWord ++ tailWord_2780183) baseStart_2780183 baseEnd_2780183 := by
    simpa [prefixWord, tailWord_2780183, baseEnd_2780183] using wordTrace_append hprefix tailTrace_2780183
  have hstable : (prefixWord ++ tailWord_2780183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780183).length < 2 ^ (prefixWord ++ tailWord_2780183).sum := by decide
  have hdescent : baseEnd_2780183 < baseStart_2780183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780217 : List Nat := [1, 2, 1, 5, 2, 2, 3, 2, 5]
def baseStart_2780217 : Nat := 118140960795 + 2780217 * 2 ^ 59
def prefixEnd_2780217 : Nat := 4983230072969 + 3 ^ 40 * 2780217 * 2
def baseEnd_2780217 : Nat := 158620849422361569100169

theorem tailTrace_2780217 : CollatzResearch.WordTrace tailWord_2780217 prefixEnd_2780217 158620849422361569100169 := by
  unfold tailWord_2780217
  simp only [CollatzResearch.WordTrace]
  refine ⟨101402844568756107106098905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67601896379170738070732603 101402844568756107106098905)
  ·
    refine ⟨76052133426567080329574179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101402844568756107106098905 76052133426567080329574179)
    ·
      refine ⟨114078200139850620494361269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76052133426567080329574179 114078200139850620494361269)
      ·
        refine ⟨10694831263110995671346369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114078200139850620494361269 10694831263110995671346369)
        ·
          refine ⟨8021123447333246753509777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10694831263110995671346369 8021123447333246753509777)
          ·
            refine ⟨6015842585499935065132333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8021123447333246753509777 6015842585499935065132333)
            ·
              refine ⟨2255940969562475649424625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6015842585499935065132333 2255940969562475649424625)
              ·
                refine ⟨1691955727171856737068469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2255940969562475649424625 1691955727171856737068469)
                ·
                  refine ⟨158620849422361569100169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1691955727171856737068469 158620849422361569100169)
                  ·
                    rfl

theorem cell23_2780217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 5].length) (baseStart_2780217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780217 prefixEnd_2780217 := by exact prefixLift 2780217
  have htrace : WordTrace (prefixWord ++ tailWord_2780217) baseStart_2780217 baseEnd_2780217 := by
    simpa [prefixWord, tailWord_2780217, baseEnd_2780217] using wordTrace_append hprefix tailTrace_2780217
  have hstable : (prefixWord ++ tailWord_2780217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780217).length < 2 ^ (prefixWord ++ tailWord_2780217).sum := by decide
  have hdescent : baseEnd_2780217 < baseStart_2780217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780320 : List Nat := [2, 1, 1, 4, 2, 1, 3, 3, 1, 5]
def baseStart_2780320 : Nat := 118140960795 + 2780320 * 2 ^ 59
def prefixEnd_2780320 : Nat := 4983230072969 + 3 ^ 40 * 2780320 * 2
def baseEnd_2780320 : Nat := 475880177769555739637849

theorem tailTrace_2780320 : CollatzResearch.WordTrace tailWord_2780320 prefixEnd_2780320 475880177769555739637849 := by
  unfold tailWord_2780320
  simp only [CollatzResearch.WordTrace]
  refine ⟨50703300643691477848549207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67604400858255303798065609 50703300643691477848549207)
  ·
    refine ⟨76054950965537216772823811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50703300643691477848549207 76054950965537216772823811)
    ·
      refine ⟨114082426448305825159235717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76054950965537216772823811 114082426448305825159235717)
      ·
        refine ⟨21390454959057342217356697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114082426448305825159235717 21390454959057342217356697)
        ·
          refine ⟨16042841219293006663017523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21390454959057342217356697 16042841219293006663017523)
          ·
            refine ⟨24064261828939509994526285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16042841219293006663017523 24064261828939509994526285)
            ·
              refine ⟨9024098185852316247947357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24064261828939509994526285 9024098185852316247947357)
              ·
                refine ⟨3384036819694618592980259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9024098185852316247947357 3384036819694618592980259)
                ·
                  refine ⟨5076055229541927889470389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3384036819694618592980259 5076055229541927889470389)
                  ·
                    refine ⟨475880177769555739637849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5076055229541927889470389 475880177769555739637849)
                    ·
                      rfl

theorem cell23_2780320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 1, 5].length) (baseStart_2780320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780320 prefixEnd_2780320 := by exact prefixLift 2780320
  have htrace : WordTrace (prefixWord ++ tailWord_2780320) baseStart_2780320 baseEnd_2780320 := by
    simpa [prefixWord, tailWord_2780320, baseEnd_2780320] using wordTrace_append hprefix tailTrace_2780320
  have hstable : (prefixWord ++ tailWord_2780320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780320).length < 2 ^ (prefixWord ++ tailWord_2780320).sum := by decide
  have hdescent : baseEnd_2780320 < baseStart_2780320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780360 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 3, 2, 3]
def baseStart_2780360 : Nat := 118140960795 + 2780360 * 2 ^ 59
def prefixEnd_2780360 : Nat := 4983230072969 + 3 ^ 40 * 2780360 * 2
def baseEnd_2780360 : Nat := 1427661072534847062413363

theorem tailTrace_2780360 : CollatzResearch.WordTrace tailWord_2780360 prefixEnd_2780360 1427661072534847062413363 := by
  unfold tailWord_2780360
  simp only [CollatzResearch.WordTrace]
  refine ⟨50704030103619021264277267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67605373471492028352369689 50704030103619021264277267)
  ·
    refine ⟨76056045155428531896415901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50704030103619021264277267 76056045155428531896415901)
    ·
      refine ⟨28521016933285699461155963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76056045155428531896415901 28521016933285699461155963)
      ·
        refine ⟨42781525399928549191733945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28521016933285699461155963 42781525399928549191733945)
        ·
          refine ⟨32086144049946411893800459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42781525399928549191733945 32086144049946411893800459)
          ·
            refine ⟨48129216074919617840700689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32086144049946411893800459 48129216074919617840700689)
            ·
              refine ⟨36096912056189713380525517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48129216074919617840700689 36096912056189713380525517)
              ·
                refine ⟨13536342021071142517697069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36096912056189713380525517 13536342021071142517697069)
                ·
                  refine ⟨5076128257901678444136401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13536342021071142517697069 5076128257901678444136401)
                  ·
                    refine ⟨3807096193426258833102301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5076128257901678444136401 3807096193426258833102301)
                    ·
                      refine ⟨1427661072534847062413363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3807096193426258833102301 1427661072534847062413363)
                      ·
                        rfl

theorem cell23_2780360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_2780360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780360 prefixEnd_2780360 := by exact prefixLift 2780360
  have htrace : WordTrace (prefixWord ++ tailWord_2780360) baseStart_2780360 baseEnd_2780360 := by
    simpa [prefixWord, tailWord_2780360, baseEnd_2780360] using wordTrace_append hprefix tailTrace_2780360
  have hstable : (prefixWord ++ tailWord_2780360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780360).length < 2 ^ (prefixWord ++ tailWord_2780360).sum := by decide
  have hdescent : baseEnd_2780360 < baseStart_2780360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780370 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2780370 : Nat := 118140960795 + 2780370 * 2 ^ 59
def prefixEnd_2780370 : Nat := 4983230072969 + 3 ^ 40 * 2780370 * 2
def baseEnd_2780370 : Nat := 1427666207341392023288317

theorem tailTrace_2780370 : CollatzResearch.WordTrace tailWord_2780370 prefixEnd_2780370 1427666207341392023288317 := by
  unfold tailWord_2780370
  simp only [CollatzResearch.WordTrace]
  refine ⟨25352106234300453559104641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67605616624801209490945709 25352106234300453559104641)
  ·
    refine ⟨19014079675725340169328481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25352106234300453559104641 19014079675725340169328481)
    ·
      refine ⟨14260559756794005126996361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19014079675725340169328481 14260559756794005126996361)
      ·
        refine ⟨10695419817595503845247271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14260559756794005126996361 10695419817595503845247271)
        ·
          refine ⟨16043129726393255767870907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10695419817595503845247271 16043129726393255767870907)
          ·
            refine ⟨24064694589589883651806361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16043129726393255767870907 24064694589589883651806361)
            ·
              refine ⟨18048520942192412738854771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24064694589589883651806361 18048520942192412738854771)
              ·
                refine ⟨27072781413288619108282157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18048520942192412738854771 27072781413288619108282157)
                ·
                  refine ⟨10152293029983232165605809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27072781413288619108282157 10152293029983232165605809)
                  ·
                    refine ⟨7614219772487424124204357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10152293029983232165605809 7614219772487424124204357)
                    ·
                      refine ⟨1427666207341392023288317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7614219772487424124204357 1427666207341392023288317)
                      ·
                        rfl

theorem cell23_2780370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2780370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780370 prefixEnd_2780370 := by exact prefixLift 2780370
  have htrace : WordTrace (prefixWord ++ tailWord_2780370) baseStart_2780370 baseEnd_2780370 := by
    simpa [prefixWord, tailWord_2780370, baseEnd_2780370] using wordTrace_append hprefix tailTrace_2780370
  have hstable : (prefixWord ++ tailWord_2780370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780370).length < 2 ^ (prefixWord ++ tailWord_2780370).sum := by decide
  have hdescent : baseEnd_2780370 < baseStart_2780370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780400 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 1, 9, 2]
def baseStart_2780400 : Nat := 118140960795 + 2780400 * 2 ^ 59
def prefixEnd_2780400 : Nat := 4983230072969 + 3 ^ 40 * 2780400 * 2
def baseEnd_2780400 : Nat := 1427681611761026905913179

theorem tailTrace_2780400 : CollatzResearch.WordTrace tailWord_2780400 prefixEnd_2780400 1427681611761026905913179 := by
  unfold tailWord_2780400
  simp only [CollatzResearch.WordTrace]
  refine ⟨50704759563546564680005327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67606346084728752906673769 50704759563546564680005327)
  ·
    refine ⟨76057139345319847020007991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50704759563546564680005327 76057139345319847020007991)
    ·
      refine ⟨114085709017979770530011987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76057139345319847020007991 114085709017979770530011987)
      ·
        refine ⟨171128563526969655795017981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114085709017979770530011987 171128563526969655795017981)
        ·
          refine ⟨64173211322613620923131743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171128563526969655795017981 64173211322613620923131743)
          ·
            refine ⟨96259816983920431384697615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64173211322613620923131743 96259816983920431384697615)
            ·
              refine ⟨144389725475880647077046423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96259816983920431384697615 144389725475880647077046423)
              ·
                refine ⟨216584588213820970615569635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144389725475880647077046423 216584588213820970615569635)
                ·
                  refine ⟨324876882320731455923354453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216584588213820970615569635 324876882320731455923354453)
                  ·
                    refine ⟨1903575482348035874550905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 324876882320731455923354453 1903575482348035874550905)
                    ·
                      refine ⟨1427681611761026905913179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1903575482348035874550905 1427681611761026905913179)
                      ·
                        rfl

theorem cell23_2780400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 9, 2].length) (baseStart_2780400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780400 prefixEnd_2780400 := by exact prefixLift 2780400
  have htrace : WordTrace (prefixWord ++ tailWord_2780400) baseStart_2780400 baseEnd_2780400 := by
    simpa [prefixWord, tailWord_2780400, baseEnd_2780400] using wordTrace_append hprefix tailTrace_2780400
  have hstable : (prefixWord ++ tailWord_2780400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780400).length < 2 ^ (prefixWord ++ tailWord_2780400).sum := by decide
  have hdescent : baseEnd_2780400 < baseStart_2780400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780407 : List Nat := [1, 1, 3, 1, 1, 1, 2, 7, 2, 1, 3]
def baseStart_2780407 : Nat := 118140960795 + 2780407 * 2 ^ 59
def prefixEnd_2780407 : Nat := 4983230072969 + 3 ^ 40 * 2780407 * 2
def baseEnd_2780407 : Nat := 1427685206125608378525647

theorem tailTrace_2780407 : CollatzResearch.WordTrace tailWord_2780407 prefixEnd_2780407 1427685206125608378525647 := by
  unfold tailWord_2780407
  simp only [CollatzResearch.WordTrace]
  refine ⟨101409774438067769555515475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67606516292045179703676983 101409774438067769555515475)
  ·
    refine ⟨152114661657101654333273213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101409774438067769555515475 152114661657101654333273213)
    ·
      refine ⟨57042998121413120374977455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152114661657101654333273213 57042998121413120374977455)
      ·
        refine ⟨85564497182119680562466183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57042998121413120374977455 85564497182119680562466183)
        ·
          refine ⟨128346745773179520843699275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85564497182119680562466183 128346745773179520843699275)
          ·
            refine ⟨192520118659769281265548913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128346745773179520843699275 192520118659769281265548913)
            ·
              refine ⟨144390088994826960949161685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192520118659769281265548913 144390088994826960949161685)
              ·
                refine ⟨3384142710816256897245977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 144390088994826960949161685 3384142710816256897245977)
                ·
                  refine ⟨2538107033112192672934483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3384142710816256897245977 2538107033112192672934483)
                  ·
                    refine ⟨3807160549668289009401725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2538107033112192672934483 3807160549668289009401725)
                    ·
                      refine ⟨1427685206125608378525647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3807160549668289009401725 1427685206125608378525647)
                      ·
                        rfl

theorem cell23_2780407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_2780407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780407 prefixEnd_2780407 := by exact prefixLift 2780407
  have htrace : WordTrace (prefixWord ++ tailWord_2780407) baseStart_2780407 baseEnd_2780407 := by
    simpa [prefixWord, tailWord_2780407, baseEnd_2780407] using wordTrace_append hprefix tailTrace_2780407
  have hstable : (prefixWord ++ tailWord_2780407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780407).length < 2 ^ (prefixWord ++ tailWord_2780407).sum := by decide
  have hdescent : baseEnd_2780407 < baseStart_2780407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780413 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_2780413 : Nat := 118140960795 + 2780413 * 2 ^ 59
def prefixEnd_2780413 : Nat := 4983230072969 + 3 ^ 40 * 2780413 * 2
def baseEnd_2780413 : Nat := 1427688287009535355050619

theorem tailTrace_2780413 : CollatzResearch.WordTrace tailWord_2780413 prefixEnd_2780413 1427688287009535355050619 := by
  unfold tailWord_2780413
  simp only [CollatzResearch.WordTrace]
  refine ⟨101409993276046032580233893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67606662184030688386822595 101409993276046032580233893)
  ·
    refine ⟨19014373739258631108793855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101409993276046032580233893 19014373739258631108793855)
    ·
      refine ⟨28521560608887946663190783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19014373739258631108793855 28521560608887946663190783)
      ·
        refine ⟨42782340913331919994786175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28521560608887946663190783 42782340913331919994786175)
        ·
          refine ⟨64173511369997879992179263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42782340913331919994786175 64173511369997879992179263)
          ·
            refine ⟨96260267054996819988268895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64173511369997879992179263 96260267054996819988268895)
            ·
              refine ⟨144390400582495229982403343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96260267054996819988268895 144390400582495229982403343)
              ·
                refine ⟨216585600873742844973605015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144390400582495229982403343 216585600873742844973605015)
                ·
                  refine ⟨324878401310614267460407523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216585600873742844973605015 324878401310614267460407523)
                  ·
                    refine ⟨487317601965921401190611285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 324878401310614267460407523 487317601965921401190611285)
                    ·
                      refine ⟨1427688287009535355050619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 487317601965921401190611285 1427688287009535355050619)
                      ·
                        rfl

theorem cell23_2780413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_2780413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780413 prefixEnd_2780413 := by exact prefixLift 2780413
  have htrace : WordTrace (prefixWord ++ tailWord_2780413) baseStart_2780413 baseEnd_2780413 := by
    simpa [prefixWord, tailWord_2780413, baseEnd_2780413] using wordTrace_append hprefix tailTrace_2780413
  have hstable : (prefixWord ++ tailWord_2780413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780413).length < 2 ^ (prefixWord ++ tailWord_2780413).sum := by decide
  have hdescent : baseEnd_2780413 < baseStart_2780413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780443 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 6]
def baseStart_2780443 : Nat := 118140960795 + 2780443 * 2 ^ 59
def prefixEnd_2780443 : Nat := 4983230072969 + 3 ^ 40 * 2780443 * 2
def baseEnd_2780443 : Nat := 1427703691429170237675481

theorem tailTrace_2780443 : CollatzResearch.WordTrace tailWord_2780443 prefixEnd_2780443 1427703691429170237675481 := by
  unfold tailWord_2780443
  simp only [CollatzResearch.WordTrace]
  refine ⟨101411087465937347703825983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67607391643958231802550655 101411087465937347703825983)
  ·
    refine ⟨152116631198906021555738975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101411087465937347703825983 152116631198906021555738975)
    ·
      refine ⟨228174946798359032333608463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152116631198906021555738975 228174946798359032333608463)
      ·
        refine ⟨342262420197538548500412695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228174946798359032333608463 342262420197538548500412695)
        ·
          refine ⟨513393630296307822750619043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342262420197538548500412695 513393630296307822750619043)
          ·
            refine ⟨770090445444461734125928565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513393630296307822750619043 770090445444461734125928565)
            ·
              refine ⟨72195979260418287574305803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 770090445444461734125928565 72195979260418287574305803)
              ·
                refine ⟨108293968890627431361458705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72195979260418287574305803 108293968890627431361458705)
                ·
                  refine ⟨81220476667970573521094029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108293968890627431361458705 81220476667970573521094029)
                  ·
                    refine ⟨30457678750488965070410261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81220476667970573521094029 30457678750488965070410261)
                    ·
                      refine ⟨1427703691429170237675481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30457678750488965070410261 1427703691429170237675481)
                      ·
                        rfl

theorem cell23_2780443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 6].length) (baseStart_2780443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780443 prefixEnd_2780443 := by exact prefixLift 2780443
  have htrace : WordTrace (prefixWord ++ tailWord_2780443) baseStart_2780443 baseEnd_2780443 := by
    simpa [prefixWord, tailWord_2780443, baseEnd_2780443] using wordTrace_append hprefix tailTrace_2780443
  have hstable : (prefixWord ++ tailWord_2780443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780443).length < 2 ^ (prefixWord ++ tailWord_2780443).sum := by decide
  have hdescent : baseEnd_2780443 < baseStart_2780443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780464 : List Nat := [2, 1, 1, 1, 2, 2, 3, 5, 2, 2, 2]
def baseStart_2780464 : Nat := 118140960795 + 2780464 * 2 ^ 59
def prefixEnd_2780464 : Nat := 4983230072969 + 3 ^ 40 * 2780464 * 2
def baseEnd_2780464 : Nat := 1427714474522914655512885

theorem tailTrace_2780464 : CollatzResearch.WordTrace tailWord_2780464 prefixEnd_2780464 1427714474522914655512885 := by
  unfold tailWord_2780464
  simp only [CollatzResearch.WordTrace]
  refine ⟨50705926699430634145170223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67607902265907512193560297 50705926699430634145170223)
  ·
    refine ⟨76058890049145951217755335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50705926699430634145170223 76058890049145951217755335)
    ·
      refine ⟨114088335073718926826633003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76058890049145951217755335 114088335073718926826633003)
      ·
        refine ⟨171132502610578390239949505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114088335073718926826633003 171132502610578390239949505)
        ·
          refine ⟨128349376957933792679962129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171132502610578390239949505 128349376957933792679962129)
          ·
            refine ⟨96262032718450344509971597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128349376957933792679962129 96262032718450344509971597)
            ·
              refine ⟨36098262269418879191239349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96262032718450344509971597 36098262269418879191239349)
              ·
                refine ⟨3384212087758019924178689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36098262269418879191239349 3384212087758019924178689)
                ·
                  refine ⟨2538159065818514943134017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3384212087758019924178689 2538159065818514943134017)
                  ·
                    refine ⟨1903619299363886207350513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2538159065818514943134017 1903619299363886207350513)
                    ·
                      refine ⟨1427714474522914655512885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1903619299363886207350513 1427714474522914655512885)
                      ·
                        rfl

theorem cell23_2780464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 2, 2, 2].length) (baseStart_2780464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780464 prefixEnd_2780464 := by exact prefixLift 2780464
  have htrace : WordTrace (prefixWord ++ tailWord_2780464) baseStart_2780464 baseEnd_2780464 := by
    simpa [prefixWord, tailWord_2780464, baseEnd_2780464] using wordTrace_append hprefix tailTrace_2780464
  have hstable : (prefixWord ++ tailWord_2780464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780464).length < 2 ^ (prefixWord ++ tailWord_2780464).sum := by decide
  have hdescent : baseEnd_2780464 < baseStart_2780464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780480 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 3]
def baseStart_2780480 : Nat := 118140960795 + 2780480 * 2 ^ 59
def prefixEnd_2780480 : Nat := 4983230072969 + 3 ^ 40 * 2780480 * 2
def baseEnd_2780480 : Nat := 1427722690213386592912811

theorem tailTrace_2780480 : CollatzResearch.WordTrace tailWord_2780480 prefixEnd_2780480 1427722690213386592912811 := by
  unfold tailWord_2780480
  simp only [CollatzResearch.WordTrace]
  refine ⟨50706218483401651511461447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67608291311202202015281929 50706218483401651511461447)
  ·
    refine ⟨76059327725102477267192171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50706218483401651511461447 76059327725102477267192171)
    ·
      refine ⟨114088991587653715900788257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76059327725102477267192171 114088991587653715900788257)
      ·
        refine ⟨85566743690740286925591193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114088991587653715900788257 85566743690740286925591193)
        ·
          refine ⟨64175057768055215194193395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85566743690740286925591193 64175057768055215194193395)
          ·
            refine ⟨96262586652082822791290093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64175057768055215194193395 96262586652082822791290093)
            ·
              refine ⟨36098469994531058546733785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96262586652082822791290093 36098469994531058546733785)
              ·
                refine ⟨27073852495898293910050339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36098469994531058546733785 27073852495898293910050339)
                ·
                  refine ⟨40610778743847440865075509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27073852495898293910050339 40610778743847440865075509)
                  ·
                    refine ⟨3807260507235697581100829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40610778743847440865075509 3807260507235697581100829)
                    ·
                      refine ⟨1427722690213386592912811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3807260507235697581100829 1427722690213386592912811)
                      ·
                        rfl

theorem cell23_2780480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_2780480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780480 prefixEnd_2780480 := by exact prefixLift 2780480
  have htrace : WordTrace (prefixWord ++ tailWord_2780480) baseStart_2780480 baseEnd_2780480 := by
    simpa [prefixWord, tailWord_2780480, baseEnd_2780480] using wordTrace_append hprefix tailTrace_2780480
  have hstable : (prefixWord ++ tailWord_2780480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780480).length < 2 ^ (prefixWord ++ tailWord_2780480).sum := by decide
  have hdescent : baseEnd_2780480 < baseStart_2780480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780487 : List Nat := [1, 1, 4, 1, 2, 3, 1, 5, 5]
def baseStart_2780487 : Nat := 118140960795 + 2780487 * 2 ^ 59
def prefixEnd_2780487 : Nat := 4983230072969 + 3 ^ 40 * 2780487 * 2
def baseEnd_2780487 : Nat := 158636253841996451725031

theorem tailTrace_2780487 : CollatzResearch.WordTrace tailWord_2780487 prefixEnd_2780487 158636253841996451725031 := by
  unfold tailWord_2780487
  simp only [CollatzResearch.WordTrace]
  refine ⟨101412692277777943218427715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67608461518518628812285143 101412692277777943218427715)
  ·
    refine ⟨152119038416666914827641573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101412692277777943218427715 152119038416666914827641573)
    ·
      refine ⟨28522319703125046530182795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152119038416666914827641573 28522319703125046530182795)
      ·
        refine ⟨42783479554687569795274193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28522319703125046530182795 42783479554687569795274193)
        ·
          refine ⟨32087609666015677346455645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42783479554687569795274193 32087609666015677346455645)
          ·
            refine ⟨12032853624755879004920867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32087609666015677346455645 12032853624755879004920867)
            ·
              refine ⟨18049280437133818507381301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12032853624755879004920867 18049280437133818507381301)
              ·
                refine ⟨1692120040981295485066997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18049280437133818507381301 1692120040981295485066997)
                ·
                  refine ⟨158636253841996451725031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1692120040981295485066997 158636253841996451725031)
                  ·
                    rfl

theorem cell23_2780487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 5].length) (baseStart_2780487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780487 prefixEnd_2780487 := by exact prefixLift 2780487
  have htrace : WordTrace (prefixWord ++ tailWord_2780487) baseStart_2780487 baseEnd_2780487 := by
    simpa [prefixWord, tailWord_2780487, baseEnd_2780487] using wordTrace_append hprefix tailTrace_2780487
  have hstable : (prefixWord ++ tailWord_2780487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780487).length < 2 ^ (prefixWord ++ tailWord_2780487).sum := by decide
  have hdescent : baseEnd_2780487 < baseStart_2780487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780530 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 2, 8]
def baseStart_2780530 : Nat := 118140960795 + 2780530 * 2 ^ 59
def prefixEnd_2780530 : Nat := 4983230072969 + 3 ^ 40 * 2780530 * 2
def baseEnd_2780530 : Nat := 475916121415370465762527

theorem tailTrace_2780530 : CollatzResearch.WordTrace tailWord_2780530 prefixEnd_2780530 475916121415370465762527 := by
  unfold tailWord_2780530
  simp only [CollatzResearch.WordTrace]
  refine ⟨25353565154155540390560761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67609507077748107708162029 25353565154155540390560761)
  ·
    refine ⟨19015173865616655292920571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25353565154155540390560761 19015173865616655292920571)
    ·
      refine ⟨28522760798424982939380857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19015173865616655292920571 28522760798424982939380857)
      ·
        refine ⟨21392070598818737204535643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28522760798424982939380857 21392070598818737204535643)
        ·
          refine ⟨32088105898228105806803465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21392070598818737204535643 32088105898228105806803465)
          ·
            refine ⟨24066079423671079355102599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32088105898228105806803465 24066079423671079355102599)
            ·
              refine ⟨36099119135506619032653899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24066079423671079355102599 36099119135506619032653899)
              ·
                refine ⟨54148678703259928548980849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36099119135506619032653899 54148678703259928548980849)
                ·
                  refine ⟨40611509027444946411735637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54148678703259928548980849 40611509027444946411735637)
                  ·
                    refine ⟨475916121415370465762527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40611509027444946411735637 475916121415370465762527)
                    ·
                      rfl

theorem cell23_2780530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_2780530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780530 prefixEnd_2780530 := by exact prefixLift 2780530
  have htrace : WordTrace (prefixWord ++ tailWord_2780530) baseStart_2780530 baseEnd_2780530 := by
    simpa [prefixWord, tailWord_2780530, baseEnd_2780530] using wordTrace_append hprefix tailTrace_2780530
  have hstable : (prefixWord ++ tailWord_2780530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780530).length < 2 ^ (prefixWord ++ tailWord_2780530).sum := by decide
  have hdescent : baseEnd_2780530 < baseStart_2780530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780537 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 1, 6, 2]
def baseStart_2780537 : Nat := 118140960795 + 2780537 * 2 ^ 59
def prefixEnd_2780537 : Nat := 4983230072969 + 3 ^ 40 * 2780537 * 2
def baseEnd_2780537 : Nat := 1427751958610692869900049

theorem tailTrace_2780537 : CollatzResearch.WordTrace tailWord_2780537 prefixEnd_2780537 1427751958610692869900049 := by
  unfold tailWord_2780537
  simp only [CollatzResearch.WordTrace]
  refine ⟨101414515927596801757747865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67609677285064534505165243 101414515927596801757747865)
  ·
    refine ⟨76060886945697601318310899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101414515927596801757747865 76060886945697601318310899)
    ·
      refine ⟨114091330418546401977466349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76060886945697601318310899 114091330418546401977466349)
      ·
        refine ⟨42784248906954900741549881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114091330418546401977466349 42784248906954900741549881)
        ·
          refine ⟨32088186680216175556162411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42784248906954900741549881 32088186680216175556162411)
          ·
            refine ⟨48132280020324263334243617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32088186680216175556162411 48132280020324263334243617)
            ·
              refine ⟨36099210015243197500682713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48132280020324263334243617 36099210015243197500682713)
              ·
                refine ⟨27074407511432398125512035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36099210015243197500682713 27074407511432398125512035)
                ·
                  refine ⟨40611611267148597188268053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27074407511432398125512035 40611611267148597188268053)
                  ·
                    refine ⟨1903669278147590493200065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40611611267148597188268053 1903669278147590493200065)
                    ·
                      refine ⟨1427751958610692869900049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1903669278147590493200065 1427751958610692869900049)
                      ·
                        rfl

theorem cell23_2780537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_2780537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780537 prefixEnd_2780537 := by exact prefixLift 2780537
  have htrace : WordTrace (prefixWord ++ tailWord_2780537) baseStart_2780537 baseEnd_2780537 := by
    simpa [prefixWord, tailWord_2780537, baseEnd_2780537] using wordTrace_append hprefix tailTrace_2780537
  have hstable : (prefixWord ++ tailWord_2780537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780537).length < 2 ^ (prefixWord ++ tailWord_2780537).sum := by decide
  have hdescent : baseEnd_2780537 < baseStart_2780537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780607 : List Nat := [1, 1, 2, 2, 2, 1, 1, 7, 1, 5]
def baseStart_2780607 : Nat := 118140960795 + 2780607 * 2 ^ 59
def prefixEnd_2780607 : Nat := 4983230072969 + 3 ^ 40 * 2780607 * 2
def baseEnd_2780607 : Nat := 475929300752169198674909

theorem tailTrace_2780607 : CollatzResearch.WordTrace tailWord_2780607 prefixEnd_2780607 475929300752169198674909 := by
  unfold tailWord_2780607
  simp only [CollatzResearch.WordTrace]
  refine ⟨101417069037343203712796075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67611379358228802475197383 101417069037343203712796075)
  ·
    refine ⟨152125603556014805569194113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101417069037343203712796075 152125603556014805569194113)
    ·
      refine ⟨114094202667011104176895585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152125603556014805569194113 114094202667011104176895585)
      ·
        refine ⟨85570652000258328132671689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114094202667011104176895585 85570652000258328132671689)
        ·
          refine ⟨64177989000193746099503767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85570652000258328132671689 64177989000193746099503767)
          ·
            refine ⟨96266983500290619149255651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64177989000193746099503767 96266983500290619149255651)
            ·
              refine ⟨144400475250435928723883477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96266983500290619149255651 144400475250435928723883477)
              ·
                refine ⟨3384386138682092079466019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 144400475250435928723883477 3384386138682092079466019)
                ·
                  refine ⟨5076579208023138119199029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3384386138682092079466019 5076579208023138119199029)
                  ·
                    refine ⟨475929300752169198674909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5076579208023138119199029 475929300752169198674909)
                    ·
                      rfl

theorem cell23_2780607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 5].length) (baseStart_2780607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780607 prefixEnd_2780607 := by exact prefixLift 2780607
  have htrace : WordTrace (prefixWord ++ tailWord_2780607) baseStart_2780607 baseEnd_2780607 := by
    simpa [prefixWord, tailWord_2780607, baseEnd_2780607] using wordTrace_append hprefix tailTrace_2780607
  have hstable : (prefixWord ++ tailWord_2780607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780607).length < 2 ^ (prefixWord ++ tailWord_2780607).sum := by decide
  have hdescent : baseEnd_2780607 < baseStart_2780607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780654 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 4, 4]
def baseStart_2780654 : Nat := 118140960795 + 2780654 * 2 ^ 59
def prefixEnd_2780654 : Nat := 4983230072969 + 3 ^ 40 * 2780654 * 2
def baseEnd_2780654 : Nat := 475937345282422970712337

theorem tailTrace_2780654 : CollatzResearch.WordTrace tailWord_2780654 prefixEnd_2780654 475937345282422970712337 := by
  unfold tailWord_2780654
  simp only [CollatzResearch.WordTrace]
  refine ⟨12677347908521616342469627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67612522178781953826504677 12677347908521616342469627)
  ·
    refine ⟨19016021862782424513704441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12677347908521616342469627 19016021862782424513704441)
    ·
      refine ⟨14262016397086818385278331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19016021862782424513704441 14262016397086818385278331)
      ·
        refine ⟨21393024595630227577917497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14262016397086818385278331 21393024595630227577917497)
        ·
          refine ⟨16044768446722670683438123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21393024595630227577917497 16044768446722670683438123)
          ·
            refine ⟨24067152670084006025157185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16044768446722670683438123 24067152670084006025157185)
            ·
              refine ⟨18050364502563004518867889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24067152670084006025157185 18050364502563004518867889)
              ·
                refine ⟨13537773376922253389150917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18050364502563004518867889 13537773376922253389150917)
                ·
                  refine ⟨2538332508172922510465797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13537773376922253389150917 2538332508172922510465797)
                  ·
                    refine ⟨475937345282422970712337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2538332508172922510465797 475937345282422970712337)
                    ·
                      rfl

theorem cell23_2780654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_2780654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780654 prefixEnd_2780654 := by exact prefixLift 2780654
  have htrace : WordTrace (prefixWord ++ tailWord_2780654) baseStart_2780654 baseEnd_2780654 := by
    simpa [prefixWord, tailWord_2780654, baseEnd_2780654] using wordTrace_append hprefix tailTrace_2780654
  have hstable : (prefixWord ++ tailWord_2780654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780654).length < 2 ^ (prefixWord ++ tailWord_2780654).sum := by decide
  have hdescent : baseEnd_2780654 < baseStart_2780654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780658 : List Nat := [3, 2, 1, 4, 1, 3, 2, 1, 1, 5]
def baseStart_2780658 : Nat := 118140960795 + 2780658 * 2 ^ 59
def prefixEnd_2780658 : Nat := 4983230072969 + 3 ^ 40 * 2780658 * 2
def baseEnd_2780658 : Nat := 475938029923295632162331

theorem tailTrace_2780658 : CollatzResearch.WordTrace tailWord_2780658 prefixEnd_2780658 475938029923295632162331 := by
  unfold tailWord_2780658
  simp only [CollatzResearch.WordTrace]
  refine ⟨25354732290039609855725657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67612619440105626281935085 25354732290039609855725657)
  ·
    refine ⟨19016049217529707391794243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25354732290039609855725657 19016049217529707391794243)
    ·
      refine ⟨28524073826294561087691365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19016049217529707391794243 28524073826294561087691365)
      ·
        refine ⟨5348263842430230203942131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28524073826294561087691365 5348263842430230203942131)
        ·
          refine ⟨8022395763645345305913197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5348263842430230203942131 8022395763645345305913197)
          ·
            refine ⟨3008398411367004489717449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8022395763645345305913197 3008398411367004489717449)
            ·
              refine ⟨2256298808525253367288087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3008398411367004489717449 2256298808525253367288087)
              ·
                refine ⟨3384448212787880050932131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2256298808525253367288087 3384448212787880050932131)
                ·
                  refine ⟨5076672319181820076398197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3384448212787880050932131 5076672319181820076398197)
                  ·
                    refine ⟨475938029923295632162331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5076672319181820076398197 475938029923295632162331)
                    ·
                      rfl

theorem cell23_2780658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_2780658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780658 prefixEnd_2780658 := by exact prefixLift 2780658
  have htrace : WordTrace (prefixWord ++ tailWord_2780658) baseStart_2780658 baseEnd_2780658 := by
    simpa [prefixWord, tailWord_2780658, baseEnd_2780658] using wordTrace_append hprefix tailTrace_2780658
  have hstable : (prefixWord ++ tailWord_2780658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780658).length < 2 ^ (prefixWord ++ tailWord_2780658).sum := by decide
  have hdescent : baseEnd_2780658 < baseStart_2780658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780747 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 4]
def baseStart_2780747 : Nat := 118140960795 + 2780747 * 2 ^ 59
def prefixEnd_2780747 : Nat := 4983230072969 + 3 ^ 40 * 2780747 * 2
def baseEnd_2780747 : Nat := 1427859789548137048274083

theorem tailTrace_2780747 : CollatzResearch.WordTrace tailWord_2780747 prefixEnd_2780747 1427859789548137048274083 := by
  unfold tailWord_2780747
  simp only [CollatzResearch.WordTrace]
  refine ⟨101422175256836007622892495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67614783504557338415261663 101422175256836007622892495)
  ·
    refine ⟨152133262885254011434338743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101422175256836007622892495 152133262885254011434338743)
    ·
      refine ⟨228199894327881017151508115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152133262885254011434338743 228199894327881017151508115)
      ·
        refine ⟨342299841491821525727262173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228199894327881017151508115 342299841491821525727262173)
        ·
          refine ⟨128362440559433072147723315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 342299841491821525727262173 128362440559433072147723315)
          ·
            refine ⟨192543660839149608221584973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128362440559433072147723315 192543660839149608221584973)
            ·
              refine ⟨72203872814681103083094365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192543660839149608221584973 72203872814681103083094365)
              ·
                refine ⟨27076452305505413656160387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72203872814681103083094365 27076452305505413656160387)
                ·
                  refine ⟨40614678458258120484240581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27076452305505413656160387 40614678458258120484240581)
                  ·
                    refine ⟨7615252210923397590795109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40614678458258120484240581 7615252210923397590795109)
                    ·
                      refine ⟨1427859789548137048274083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7615252210923397590795109 1427859789548137048274083)
                      ·
                        rfl

theorem cell23_2780747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 4].length) (baseStart_2780747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780747 prefixEnd_2780747 := by exact prefixLift 2780747
  have htrace : WordTrace (prefixWord ++ tailWord_2780747) baseStart_2780747 baseEnd_2780747 := by
    simpa [prefixWord, tailWord_2780747, baseEnd_2780747] using wordTrace_append hprefix tailTrace_2780747
  have hstable : (prefixWord ++ tailWord_2780747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780747).length < 2 ^ (prefixWord ++ tailWord_2780747).sum := by decide
  have hdescent : baseEnd_2780747 < baseStart_2780747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780754 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_2780754 : Nat := 118140960795 + 2780754 * 2 ^ 59
def prefixEnd_2780754 : Nat := 4983230072969 + 3 ^ 40 * 2780754 * 2
def baseEnd_2780754 : Nat := 1427863383912718520886551

theorem tailTrace_2780754 : CollatzResearch.WordTrace tailWord_2780754 prefixEnd_2780754 1427863383912718520886551 := by
  unfold tailWord_2780754
  simp only [CollatzResearch.WordTrace]
  refine ⟨25355607641952661954599329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67614953711873765212264877 25355607641952661954599329)
  ·
    refine ⟨19016705731464496465949497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25355607641952661954599329 19016705731464496465949497)
    ·
      refine ⟨14262529298598372349462123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19016705731464496465949497 14262529298598372349462123)
      ·
        refine ⟨21393793947897558524193185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14262529298598372349462123 21393793947897558524193185)
        ·
          refine ⟨16045345460923168893144889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21393793947897558524193185 16045345460923168893144889)
          ·
            refine ⟨12034009095692376669858667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16045345460923168893144889 12034009095692376669858667)
            ·
              refine ⟨18051013643538565004788001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12034009095692376669858667 18051013643538565004788001)
              ·
                refine ⟨13538260232653923753591001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18051013643538565004788001 13538260232653923753591001)
                ·
                  refine ⟨10153695174490442815193251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13538260232653923753591001 10153695174490442815193251)
                  ·
                    refine ⟨15230542761735664222789877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10153695174490442815193251 15230542761735664222789877)
                    ·
                      refine ⟨1427863383912718520886551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15230542761735664222789877 1427863383912718520886551)
                      ·
                        rfl

theorem cell23_2780754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_2780754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780754 prefixEnd_2780754 := by exact prefixLift 2780754
  have htrace : WordTrace (prefixWord ++ tailWord_2780754) baseStart_2780754 baseEnd_2780754 := by
    simpa [prefixWord, tailWord_2780754, baseEnd_2780754] using wordTrace_append hprefix tailTrace_2780754
  have hstable : (prefixWord ++ tailWord_2780754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780754).length < 2 ^ (prefixWord ++ tailWord_2780754).sum := by decide
  have hdescent : baseEnd_2780754 < baseStart_2780754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780757 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 9]
def baseStart_2780757 : Nat := 118140960795 + 2780757 * 2 ^ 59
def prefixEnd_2780757 : Nat := 4983230072969 + 3 ^ 40 * 2780757 * 2
def baseEnd_2780757 : Nat := 158651658261631334349893

theorem tailTrace_2780757 : CollatzResearch.WordTrace tailWord_2780757 prefixEnd_2780757 158651658261631334349893 := by
  unfold tailWord_2780757
  simp only [CollatzResearch.WordTrace]
  refine ⟨101422539986799779330756525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67615026657866519553837683 101422539986799779330756525)
  ·
    refine ⟨38033452495049917249033697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101422539986799779330756525 38033452495049917249033697)
    ·
      refine ⟨28525089371287437936775273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38033452495049917249033697 28525089371287437936775273)
      ·
        refine ⟨21393817028465578452581455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28525089371287437936775273 21393817028465578452581455)
        ·
          refine ⟨32090725542698367678872183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21393817028465578452581455 32090725542698367678872183)
          ·
            refine ⟨48136088314047551518308275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32090725542698367678872183 48136088314047551518308275)
            ·
              refine ⟨72204132471071327277462413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48136088314047551518308275 72204132471071327277462413)
              ·
                refine ⟨27076549676651747729048405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72204132471071327277462413 27076549676651747729048405)
                ·
                  refine ⟨158651658261631334349893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27076549676651747729048405 158651658261631334349893)
                  ·
                    rfl

theorem cell23_2780757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 9].length) (baseStart_2780757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780757 prefixEnd_2780757 := by exact prefixLift 2780757
  have htrace : WordTrace (prefixWord ++ tailWord_2780757) baseStart_2780757 baseEnd_2780757 := by
    simpa [prefixWord, tailWord_2780757, baseEnd_2780757] using wordTrace_append hprefix tailTrace_2780757
  have hstable : (prefixWord ++ tailWord_2780757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780757).length < 2 ^ (prefixWord ++ tailWord_2780757).sum := by decide
  have hdescent : baseEnd_2780757 < baseStart_2780757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780801 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_2780801 : Nat := 118140960795 + 2780801 * 2 ^ 59
def prefixEnd_2780801 : Nat := 4983230072969 + 3 ^ 40 * 2780801 * 2
def baseEnd_2780801 : Nat := 1427887517503479836998835

theorem tailTrace_2780801 : CollatzResearch.WordTrace tailWord_2780801 prefixEnd_2780801 1427887517503479836998835 := by
  unfold tailWord_2780801
  simp only [CollatzResearch.WordTrace]
  refine ⟨101424144798640374845358257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67616096532426916563572171 101424144798640374845358257)
  ·
    refine ⟨76068108598980281134018693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101424144798640374845358257 76068108598980281134018693)
    ·
      refine ⟨14262770362308802712628505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76068108598980281134018693 14262770362308802712628505)
      ·
        refine ⟨10697077771731602034471379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14262770362308802712628505 10697077771731602034471379)
        ·
          refine ⟨16045616657597403051707069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10697077771731602034471379 16045616657597403051707069)
          ·
            refine ⟨6017106246599026144390151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16045616657597403051707069 6017106246599026144390151)
            ·
              refine ⟨9025659369898539216585227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6017106246599026144390151 9025659369898539216585227)
              ·
                refine ⟨13538489054847808824877841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9025659369898539216585227 13538489054847808824877841)
                ·
                  refine ⟨10153866791135856618658381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13538489054847808824877841 10153866791135856618658381)
                  ·
                    refine ⟨3807700046675946231996893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10153866791135856618658381 3807700046675946231996893)
                    ·
                      refine ⟨1427887517503479836998835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3807700046675946231996893 1427887517503479836998835)
                      ·
                        rfl

theorem cell23_2780801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_2780801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780801 prefixEnd_2780801 := by exact prefixLift 2780801
  have htrace : WordTrace (prefixWord ++ tailWord_2780801) baseStart_2780801 baseEnd_2780801 := by
    simpa [prefixWord, tailWord_2780801, baseEnd_2780801] using wordTrace_append hprefix tailTrace_2780801
  have hstable : (prefixWord ++ tailWord_2780801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780801).length < 2 ^ (prefixWord ++ tailWord_2780801).sum := by decide
  have hdescent : baseEnd_2780801 < baseStart_2780801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780817 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 1, 10]
def baseStart_2780817 : Nat := 118140960795 + 2780817 * 2 ^ 59
def prefixEnd_2780817 : Nat := 4983230072969 + 3 ^ 40 * 2780817 * 2
def baseEnd_2780817 : Nat := 475965244397983924799587

theorem tailTrace_2780817 : CollatzResearch.WordTrace tailWord_2780817 prefixEnd_2780817 475965244397983924799587 := by
  unfold tailWord_2780817
  simp only [CollatzResearch.WordTrace]
  refine ⟨101424728366582409577940705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67616485577721606385293803 101424728366582409577940705)
  ·
    refine ⟨76068546274936807183455529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101424728366582409577940705 76068546274936807183455529)
    ·
      refine ⟨57051409706202605387591647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76068546274936807183455529 57051409706202605387591647)
      ·
        refine ⟨85577114559303908081387471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57051409706202605387591647 85577114559303908081387471)
        ·
          refine ⟨128365671838955862122081207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85577114559303908081387471 128365671838955862122081207)
          ·
            refine ⟨192548507758433793183121811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128365671838955862122081207 192548507758433793183121811)
            ·
              refine ⟨288822761637650689774682717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192548507758433793183121811 288822761637650689774682717)
              ·
                refine ⟨108308535614119008665506019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288822761637650689774682717 108308535614119008665506019)
                ·
                  refine ⟨162462803421178512998259029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108308535614119008665506019 162462803421178512998259029)
                  ·
                    refine ⟨475965244397983924799587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 162462803421178512998259029 475965244397983924799587)
                    ·
                      rfl

theorem cell23_2780817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_2780817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780817 prefixEnd_2780817 := by exact prefixLift 2780817
  have htrace : WordTrace (prefixWord ++ tailWord_2780817) baseStart_2780817 baseEnd_2780817 := by
    simpa [prefixWord, tailWord_2780817, baseEnd_2780817] using wordTrace_append hprefix tailTrace_2780817
  have hstable : (prefixWord ++ tailWord_2780817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780817).length < 2 ^ (prefixWord ++ tailWord_2780817).sum := by decide
  have hdescent : baseEnd_2780817 < baseStart_2780817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780851 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 3, 4]
def baseStart_2780851 : Nat := 118140960795 + 2780851 * 2 ^ 59
def prefixEnd_2780851 : Nat := 4983230072969 + 3 ^ 40 * 2780851 * 2
def baseEnd_2780851 : Nat := 475971063845401547124535

theorem tailTrace_2780851 : CollatzResearch.WordTrace tailWord_2780851 prefixEnd_2780851 475971063845401547124535 := by
  unfold tailWord_2780851
  simp only [CollatzResearch.WordTrace]
  refine ⟨101425968448459233384678407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67617312298972822256452271 101425968448459233384678407)
  ·
    refine ⟨152138952672688850077017611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101425968448459233384678407 152138952672688850077017611)
    ·
      refine ⟨228208429009033275115526417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152138952672688850077017611 228208429009033275115526417)
      ·
        refine ⟨171156321756774956336644813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228208429009033275115526417 171156321756774956336644813)
        ·
          refine ⟨64183620658790608626241805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171156321756774956336644813 64183620658790608626241805)
          ·
            refine ⟨24068857747046478234840677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64183620658790608626241805 24068857747046478234840677)
            ·
              refine ⟨4512910827571214669032627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24068857747046478234840677 4512910827571214669032627)
              ·
                refine ⟨6769366241356822003548941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4512910827571214669032627 6769366241356822003548941)
                ·
                  refine ⟨2538512340508808251330853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6769366241356822003548941 2538512340508808251330853)
                  ·
                    refine ⟨475971063845401547124535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2538512340508808251330853 475971063845401547124535)
                    ·
                      rfl

theorem cell23_2780851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 4].length) (baseStart_2780851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780851 prefixEnd_2780851 := by exact prefixLift 2780851
  have htrace : WordTrace (prefixWord ++ tailWord_2780851) baseStart_2780851 baseEnd_2780851 := by
    simpa [prefixWord, tailWord_2780851, baseEnd_2780851] using wordTrace_append hprefix tailTrace_2780851
  have hstable : (prefixWord ++ tailWord_2780851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780851).length < 2 ^ (prefixWord ++ tailWord_2780851).sum := by decide
  have hdescent : baseEnd_2780851 < baseStart_2780851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780908 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 3]
def baseStart_2780908 : Nat := 118140960795 + 2780908 * 2 ^ 59
def prefixEnd_2780908 : Nat := 4983230072969 + 3 ^ 40 * 2780908 * 2
def baseEnd_2780908 : Nat := 1427942459933510918360843

theorem tailTrace_2780908 : CollatzResearch.WordTrace tailWord_2780908 prefixEnd_2780908 1427942459933510918360843 := by
  unfold tailWord_2780908
  simp only [CollatzResearch.WordTrace]
  refine ⟨50714023704626366059751689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67618698272835154746335585 50714023704626366059751689)
  ·
    refine ⟨38035517778469774544813767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50714023704626366059751689 38035517778469774544813767)
    ·
      refine ⟨57053276667704661817220651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38035517778469774544813767 57053276667704661817220651)
      ·
        refine ⟨85579915001556992725830977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57053276667704661817220651 85579915001556992725830977)
        ·
          refine ⟨64184936251167744544373233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85579915001556992725830977 64184936251167744544373233)
          ·
            refine ⟨48138702188375808408279925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64184936251167744544373233 48138702188375808408279925)
            ·
              refine ⟨4513003330160232038276243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48138702188375808408279925 4513003330160232038276243)
              ·
                refine ⟨6769504995240348057414365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4513003330160232038276243 6769504995240348057414365)
                ·
                  refine ⟨2538564373215130521530387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6769504995240348057414365 2538564373215130521530387)
                  ·
                    refine ⟨3807846559822695782295581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2538564373215130521530387 3807846559822695782295581)
                    ·
                      refine ⟨1427942459933510918360843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3807846559822695782295581 1427942459933510918360843)
                      ·
                        rfl

theorem cell23_2780908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_2780908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780908 prefixEnd_2780908 := by exact prefixLift 2780908
  have htrace : WordTrace (prefixWord ++ tailWord_2780908) baseStart_2780908 baseEnd_2780908 := by
    simpa [prefixWord, tailWord_2780908, baseEnd_2780908] using wordTrace_append hprefix tailTrace_2780908
  have hstable : (prefixWord ++ tailWord_2780908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780908).length < 2 ^ (prefixWord ++ tailWord_2780908).sum := by decide
  have hdescent : baseEnd_2780908 < baseStart_2780908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780931 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 2, 6, 2]
def baseStart_2780931 : Nat := 118140960795 + 2780931 * 2 ^ 59
def prefixEnd_2780931 : Nat := 4983230072969 + 3 ^ 40 * 2780931 * 2
def baseEnd_2780931 : Nat := 1427954269988564328373237

theorem tailTrace_2780931 : CollatzResearch.WordTrace tailWord_2780931 prefixEnd_2780931 1427954269988564328373237 := by
  unfold tailWord_2780931
  simp only [CollatzResearch.WordTrace]
  refine ⟨101428886288169407047590647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67619257525446271365060431 101428886288169407047590647)
  ·
    refine ⟨152143329432254110571385971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101428886288169407047590647 152143329432254110571385971)
    ·
      refine ⟨228214994148381165857078957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152143329432254110571385971 228214994148381165857078957)
      ·
        refine ⟨85580622805642937196404609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228214994148381165857078957 85580622805642937196404609)
        ·
          refine ⟨64185467104232202897303457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85580622805642937196404609 64185467104232202897303457)
          ·
            refine ⟨48139100328174152172977593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64185467104232202897303457 48139100328174152172977593)
            ·
              refine ⟨36104325246130614129733195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48139100328174152172977593 36104325246130614129733195)
              ·
                refine ⟨54156487869195921194599793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36104325246130614129733195 54156487869195921194599793)
                ·
                  refine ⟨40617365901896940895949845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54156487869195921194599793 40617365901896940895949845)
                  ·
                    refine ⟨1903939026651419104497649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40617365901896940895949845 1903939026651419104497649)
                    ·
                      refine ⟨1427954269988564328373237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1903939026651419104497649 1427954269988564328373237)
                      ·
                        rfl

theorem cell23_2780931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 6, 2].length) (baseStart_2780931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780931 prefixEnd_2780931 := by exact prefixLift 2780931
  have htrace : WordTrace (prefixWord ++ tailWord_2780931) baseStart_2780931 baseEnd_2780931 := by
    simpa [prefixWord, tailWord_2780931, baseEnd_2780931] using wordTrace_append hprefix tailTrace_2780931
  have hstable : (prefixWord ++ tailWord_2780931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780931).length < 2 ^ (prefixWord ++ tailWord_2780931).sum := by decide
  have hdescent : baseEnd_2780931 < baseStart_2780931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780954 : List Nat := [3, 1, 1, 3, 2, 13]
def baseStart_2780954 : Nat := 118140960795 + 2780954 * 2 ^ 59
def prefixEnd_2780954 : Nat := 4983230072969 + 3 ^ 40 * 2780954 * 2
def baseEnd_2780954 : Nat := 5876403621578673820517

theorem tailTrace_2780954 : CollatzResearch.WordTrace tailWord_2780954 prefixEnd_2780954 5876403621578673820517 := by
  unfold tailWord_2780954
  simp only [CollatzResearch.WordTrace]
  refine ⟨25357431291771520493919479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67619816778057387983785277 25357431291771520493919479)
  ·
    refine ⟨38036146937657280740879219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25357431291771520493919479 38036146937657280740879219)
    ·
      refine ⟨57054220406485921111318829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38036146937657280740879219 57054220406485921111318829)
      ·
        refine ⟨21395332652432220416744561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57054220406485921111318829 21395332652432220416744561)
        ·
          refine ⟨16046499489324165312558421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21395332652432220416744561 16046499489324165312558421)
          ·
            refine ⟨5876403621578673820517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 16046499489324165312558421 5876403621578673820517)
            ·
              rfl

theorem cell23_2780954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 13].length) (baseStart_2780954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780954 prefixEnd_2780954 := by exact prefixLift 2780954
  have htrace : WordTrace (prefixWord ++ tailWord_2780954) baseStart_2780954 baseEnd_2780954 := by
    simpa [prefixWord, tailWord_2780954, baseEnd_2780954] using wordTrace_append hprefix tailTrace_2780954
  have hstable : (prefixWord ++ tailWord_2780954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780954).length < 2 ^ (prefixWord ++ tailWord_2780954).sum := by decide
  have hdescent : baseEnd_2780954 < baseStart_2780954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780968 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_2780968 : Nat := 118140960795 + 2780968 * 2 ^ 59
def prefixEnd_2780968 : Nat := 4983230072969 + 3 ^ 40 * 2780968 * 2
def baseEnd_2780968 : Nat := 1427973268772780683610567

theorem tailTrace_2780968 : CollatzResearch.WordTrace tailWord_2780968 prefixEnd_2780968 1427973268772780683610567 := by
  unfold tailWord_2780968
  simp only [CollatzResearch.WordTrace]
  refine ⟨50715117894517681183343779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67620157192690241577791705 50715117894517681183343779)
  ·
    refine ⟨76072676841776521775015669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50715117894517681183343779 76072676841776521775015669)
    ·
      refine ⟨7131813453916548916407719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76072676841776521775015669 7131813453916548916407719)
      ·
        refine ⟨10697720180874823374611579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7131813453916548916407719 10697720180874823374611579)
        ·
          refine ⟨16046580271312235061917369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10697720180874823374611579 16046580271312235061917369)
          ·
            refine ⟨12034935203484176296438027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16046580271312235061917369 12034935203484176296438027)
            ·
              refine ⟨18052402805226264444657041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12034935203484176296438027 18052402805226264444657041)
              ·
                refine ⟨13539302103919698333492781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18052402805226264444657041 13539302103919698333492781)
                ·
                  refine ⟨5077238288969886875059793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13539302103919698333492781 5077238288969886875059793)
                  ·
                    refine ⟨3807928716727415156294845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5077238288969886875059793 3807928716727415156294845)
                    ·
                      refine ⟨1427973268772780683610567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3807928716727415156294845 1427973268772780683610567)
                      ·
                        rfl

theorem cell23_2780968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_2780968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780968 prefixEnd_2780968 := by exact prefixLift 2780968
  have htrace : WordTrace (prefixWord ++ tailWord_2780968) baseStart_2780968 baseEnd_2780968 := by
    simpa [prefixWord, tailWord_2780968, baseEnd_2780968] using wordTrace_append hprefix tailTrace_2780968
  have hstable : (prefixWord ++ tailWord_2780968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780968).length < 2 ^ (prefixWord ++ tailWord_2780968).sum := by decide
  have hdescent : baseEnd_2780968 < baseStart_2780968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780978 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4]
def baseStart_2780978 : Nat := 118140960795 + 2780978 * 2 ^ 59
def prefixEnd_2780978 : Nat := 4983230072969 + 3 ^ 40 * 2780978 * 2
def baseEnd_2780978 : Nat := 1427978403579325644485521

theorem tailTrace_2780978 : CollatzResearch.WordTrace tailWord_2780978 prefixEnd_2780978 1427978403579325644485521 := by
  unfold tailWord_2780978
  simp only [CollatzResearch.WordTrace]
  refine ⟨25357650129749783518637897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67620400345999422716367725 25357650129749783518637897)
  ·
    refine ⟨19018237597312337638978423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25357650129749783518637897 19018237597312337638978423)
    ·
      refine ⟨28527356395968506458467635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19018237597312337638978423 28527356395968506458467635)
      ·
        refine ⟨42791034593952759687701453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28527356395968506458467635 42791034593952759687701453)
        ·
          refine ⟨16046637972732284882888045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42791034593952759687701453 16046637972732284882888045)
          ·
            refine ⟨6017489239774606831083017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16046637972732284882888045 6017489239774606831083017)
            ·
              refine ⟨4513116929830955123312263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6017489239774606831083017 4513116929830955123312263)
              ·
                refine ⟨6769675394746432684968395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4513116929830955123312263 6769675394746432684968395)
                ·
                  refine ⟨10154513092119649027452593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6769675394746432684968395 10154513092119649027452593)
                  ·
                    refine ⟨7615884819089736770589445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10154513092119649027452593 7615884819089736770589445)
                    ·
                      refine ⟨1427978403579325644485521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7615884819089736770589445 1427978403579325644485521)
                      ·
                        rfl

theorem cell23_2780978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_2780978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780978 prefixEnd_2780978 := by exact prefixLift 2780978
  have htrace : WordTrace (prefixWord ++ tailWord_2780978) baseStart_2780978 baseEnd_2780978 := by
    simpa [prefixWord, tailWord_2780978, baseEnd_2780978] using wordTrace_append hprefix tailTrace_2780978
  have hstable : (prefixWord ++ tailWord_2780978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780978).length < 2 ^ (prefixWord ++ tailWord_2780978).sum := by decide
  have hdescent : baseEnd_2780978 < baseStart_2780978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780982 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_2780982 : Nat := 118140960795 + 2780982 * 2 ^ 59
def prefixEnd_2780982 : Nat := 4983230072969 + 3 ^ 40 * 2780982 * 2
def baseEnd_2780982 : Nat := 1427980457501943628835503

theorem tailTrace_2780982 : CollatzResearch.WordTrace tailWord_2780982 prefixEnd_2780982 1427980457501943628835503 := by
  unfold tailWord_2780982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6339421650686540172356075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67620497607323095171798133 6339421650686540172356075)
  ·
    refine ⟨9509132476029810258534113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6339421650686540172356075 9509132476029810258534113)
    ·
      refine ⟨7131849357022357693900585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9509132476029810258534113 7131849357022357693900585)
      ·
        refine ⟨5348887017766768270425439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7131849357022357693900585 5348887017766768270425439)
        ·
          refine ⟨8023330526650152405638159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5348887017766768270425439 8023330526650152405638159)
          ·
            refine ⟨12034995789975228608457239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8023330526650152405638159 12034995789975228608457239)
            ·
              refine ⟨18052493684962842912685859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12034995789975228608457239 18052493684962842912685859)
              ·
                refine ⟨27078740527444264369028789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18052493684962842912685859 27078740527444264369028789)
                ·
                  refine ⟨2538631924447899784596449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27078740527444264369028789 2538631924447899784596449)
                  ·
                    refine ⟨1903973943335924838447337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2538631924447899784596449 1903973943335924838447337)
                    ·
                      refine ⟨1427980457501943628835503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1903973943335924838447337 1427980457501943628835503)
                      ·
                        rfl

theorem cell23_2780982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_2780982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780982 prefixEnd_2780982 := by exact prefixLift 2780982
  have htrace : WordTrace (prefixWord ++ tailWord_2780982) baseStart_2780982 baseEnd_2780982 := by
    simpa [prefixWord, tailWord_2780982, baseEnd_2780982] using wordTrace_append hprefix tailTrace_2780982
  have hstable : (prefixWord ++ tailWord_2780982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780982).length < 2 ^ (prefixWord ++ tailWord_2780982).sum := by decide
  have hdescent : baseEnd_2780982 < baseStart_2780982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781015 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 4, 1, 3]
def baseStart_2781015 : Nat := 118140960795 + 2781015 * 2 ^ 59
def prefixEnd_2781015 : Nat := 4983230072969 + 3 ^ 40 * 2781015 * 2
def baseEnd_2781015 : Nat := 1427997402363541999722851

theorem tailTrace_2781015 : CollatzResearch.WordTrace tailWord_2781015 prefixEnd_2781015 1427997402363541999722851 := by
  unfold tailWord_2781015
  simp only [CollatzResearch.WordTrace]
  refine ⟨101431950019865089393648499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67621300013243392929098999 101431950019865089393648499)
  ·
    refine ⟨152147925029797634090472749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101431950019865089393648499 152147925029797634090472749)
    ·
      refine ⟨57055471886174112783927281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152147925029797634090472749 57055471886174112783927281)
      ·
        refine ⟨42791603914630584587945461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57055471886174112783927281 42791603914630584587945461)
        ·
          refine ⟨4011712866996617305119887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42791603914630584587945461 4011712866996617305119887)
          ·
            refine ⟨6017569300494925957679831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4011712866996617305119887 6017569300494925957679831)
            ·
              refine ⟨9026353950742388936519747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6017569300494925957679831 9026353950742388936519747)
              ·
                refine ⟨13539530926113583404779621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9026353950742388936519747 13539530926113583404779621)
                ·
                  refine ⟨2538662048646296888396179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13539530926113583404779621 2538662048646296888396179)
                  ·
                    refine ⟨3807993072969445332594269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2538662048646296888396179 3807993072969445332594269)
                    ·
                      refine ⟨1427997402363541999722851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3807993072969445332594269 1427997402363541999722851)
                      ·
                        rfl

theorem cell23_2781015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_2781015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781015 prefixEnd_2781015 := by exact prefixLift 2781015
  have htrace : WordTrace (prefixWord ++ tailWord_2781015) baseStart_2781015 baseEnd_2781015 := by
    simpa [prefixWord, tailWord_2781015, baseEnd_2781015] using wordTrace_append hprefix tailTrace_2781015
  have hstable : (prefixWord ++ tailWord_2781015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781015).length < 2 ^ (prefixWord ++ tailWord_2781015).sum := by decide
  have hdescent : baseEnd_2781015 < baseStart_2781015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781031 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 2, 6]
def baseStart_2781031 : Nat := 118140960795 + 2781031 * 2 ^ 59
def prefixEnd_2781031 : Nat := 4983230072969 + 3 ^ 40 * 2781031 * 2
def baseEnd_2781031 : Nat := 476001872684671312374259

theorem tailTrace_2781031 : CollatzResearch.WordTrace tailWord_2781031 prefixEnd_2781031 476001872684671312374259 := by
  unfold tailWord_2781031
  simp only [CollatzResearch.WordTrace]
  refine ⟨101432533587807124126230947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67621689058538082750820631 101432533587807124126230947)
  ·
    refine ⟨152148800381710686189346421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101432533587807124126230947 152148800381710686189346421)
    ·
      refine ⟨14263950035785376830251227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152148800381710686189346421 14263950035785376830251227)
      ·
        refine ⟨21395925053678065245376841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14263950035785376830251227 21395925053678065245376841)
        ·
          refine ⟨16046943790258548934032631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21395925053678065245376841 16046943790258548934032631)
          ·
            refine ⟨24070415685387823401048947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16046943790258548934032631 24070415685387823401048947)
            ·
              refine ⟨36105623528081735101573421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24070415685387823401048947 36105623528081735101573421)
              ·
                refine ⟨13539608823030650663090033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36105623528081735101573421 13539608823030650663090033)
                ·
                  refine ⟨10154706617272987997317525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13539608823030650663090033 10154706617272987997317525)
                  ·
                    refine ⟨476001872684671312374259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10154706617272987997317525 476001872684671312374259)
                    ·
                      rfl

theorem cell23_2781031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_2781031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781031 prefixEnd_2781031 := by exact prefixLift 2781031
  have htrace : WordTrace (prefixWord ++ tailWord_2781031) baseStart_2781031 baseEnd_2781031 := by
    simpa [prefixWord, tailWord_2781031, baseEnd_2781031] using wordTrace_append hprefix tailTrace_2781031
  have hstable : (prefixWord ++ tailWord_2781031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781031).length < 2 ^ (prefixWord ++ tailWord_2781031).sum := by decide
  have hdescent : baseEnd_2781031 < baseStart_2781031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781032 : List Nat := [2, 1, 4, 2, 1, 1, 5, 1, 2, 1, 3]
def baseStart_2781032 : Nat := 118140960795 + 2781032 * 2 ^ 59
def prefixEnd_2781032 : Nat := 4983230072969 + 3 ^ 40 * 2781032 * 2
def baseEnd_2781032 : Nat := 1428006131534668433210273

theorem tailTrace_2781032 : CollatzResearch.WordTrace tailWord_2781032 prefixEnd_2781032 1428006131534668433210273 := by
  unfold tailWord_2781032
  simp only [CollatzResearch.WordTrace]
  refine ⟨50716285030401750648508675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67621713373869000864678233 50716285030401750648508675)
  ·
    refine ⟨76074427545602625972763013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50716285030401750648508675 76074427545602625972763013)
    ·
      refine ⟨14263955164800492369893065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76074427545602625972763013 14263955164800492369893065)
      ·
        refine ⟨10697966373600369277419799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14263955164800492369893065 10697966373600369277419799)
        ·
          refine ⟨16046949560400553916129699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10697966373600369277419799 16046949560400553916129699)
          ·
            refine ⟨24070424340600830874194549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16046949560400553916129699 24070424340600830874194549)
            ·
              refine ⟨2256602281931327894455739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24070424340600830874194549 2256602281931327894455739)
              ·
                refine ⟨3384903422896991841683609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2256602281931327894455739 3384903422896991841683609)
                ·
                  refine ⟨2538677567172743881262707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3384903422896991841683609 2538677567172743881262707)
                  ·
                    refine ⟨3808016350759115821894061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2538677567172743881262707 3808016350759115821894061)
                    ·
                      refine ⟨1428006131534668433210273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3808016350759115821894061 1428006131534668433210273)
                      ·
                        rfl

theorem cell23_2781032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_2781032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781032 prefixEnd_2781032 := by exact prefixLift 2781032
  have htrace : WordTrace (prefixWord ++ tailWord_2781032) baseStart_2781032 baseEnd_2781032 := by
    simpa [prefixWord, tailWord_2781032, baseEnd_2781032] using wordTrace_append hprefix tailTrace_2781032
  have hstable : (prefixWord ++ tailWord_2781032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781032).length < 2 ^ (prefixWord ++ tailWord_2781032).sum := by decide
  have hdescent : baseEnd_2781032 < baseStart_2781032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781041 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 2, 1, 5]
def baseStart_2781041 : Nat := 118140960795 + 2781041 * 2 ^ 59
def prefixEnd_2781041 : Nat := 4983230072969 + 3 ^ 40 * 2781041 * 2
def baseEnd_2781041 : Nat := 1428010752860558897997731

theorem tailTrace_2781041 : CollatzResearch.WordTrace tailWord_2781041 prefixEnd_2781041 1428010752860558897997731 := by
  unfold tailWord_2781041
  simp only [CollatzResearch.WordTrace]
  refine ⟨101432898317770895834094977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67621932211847263889396651 101432898317770895834094977)
  ·
    refine ⟨76074673738328171875571233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101432898317770895834094977 76074673738328171875571233)
    ·
      refine ⟨57056005303746128906678425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76074673738328171875571233 57056005303746128906678425)
      ·
        refine ⟨42792003977809596680008819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57056005303746128906678425 42792003977809596680008819)
        ·
          refine ⟨64188005966714395020013229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42792003977809596680008819 64188005966714395020013229)
          ·
            refine ⟨24070502237517898132504961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64188005966714395020013229 24070502237517898132504961)
            ·
              refine ⟨18052876678138423599378721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24070502237517898132504961 18052876678138423599378721)
              ·
                refine ⟨13539657508603817699534041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18052876678138423599378721 13539657508603817699534041)
                ·
                  refine ⟨10154743131452863274650531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13539657508603817699534041 10154743131452863274650531)
                  ·
                    refine ⟨15232114697179294911975797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10154743131452863274650531 15232114697179294911975797)
                    ·
                      refine ⟨1428010752860558897997731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15232114697179294911975797 1428010752860558897997731)
                      ·
                        rfl

theorem cell23_2781041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_2781041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781041 prefixEnd_2781041 := by exact prefixLift 2781041
  have htrace : WordTrace (prefixWord ++ tailWord_2781041) baseStart_2781041 baseEnd_2781041 := by
    simpa [prefixWord, tailWord_2781041, baseEnd_2781041] using wordTrace_append hprefix tailTrace_2781041
  have hstable : (prefixWord ++ tailWord_2781041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781041).length < 2 ^ (prefixWord ++ tailWord_2781041).sum := by decide
  have hdescent : baseEnd_2781041 < baseStart_2781041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781089 : List Nat := [1, 2, 3, 4, 2, 1, 1, 3, 2, 2, 2]
def baseStart_2781089 : Nat := 118140960795 + 2781089 * 2 ^ 59
def prefixEnd_2781089 : Nat := 4983230072969 + 3 ^ 40 * 2781089 * 2
def baseEnd_2781089 : Nat := 1428035399931974710197511

theorem tailTrace_2781089 : CollatzResearch.WordTrace tailWord_2781089 prefixEnd_2781089 1428035399931974710197511 := by
  unfold tailWord_2781089
  simp only [CollatzResearch.WordTrace]
  refine ⟨101434649021597000031842321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67623099347731333354561547 101434649021597000031842321)
  ·
    refine ⟨76075986766197750023881741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101434649021597000031842321 76075986766197750023881741)
    ·
      refine ⟨28528495037324156258955653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76075986766197750023881741 28528495037324156258955653)
      ·
        refine ⟨5349092819498279298554185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28528495037324156258955653 5349092819498279298554185)
        ·
          refine ⟨4011819614623709473915639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5349092819498279298554185 4011819614623709473915639)
          ·
            refine ⟨6017729421935564210873459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4011819614623709473915639 6017729421935564210873459)
            ·
              refine ⟨9026594132903346316310189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6017729421935564210873459 9026594132903346316310189)
              ·
                refine ⟨3384972799838754868616321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9026594132903346316310189 3384972799838754868616321)
                ·
                  refine ⟨2538729599879066151462241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3384972799838754868616321 2538729599879066151462241)
                  ·
                    refine ⟨1904047199909299613596681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2538729599879066151462241 1904047199909299613596681)
                    ·
                      refine ⟨1428035399931974710197511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1904047199909299613596681 1428035399931974710197511)
                      ·
                        rfl

theorem cell23_2781089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_2781089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781089 prefixEnd_2781089 := by exact prefixLift 2781089
  have htrace : WordTrace (prefixWord ++ tailWord_2781089) baseStart_2781089 baseEnd_2781089 := by
    simpa [prefixWord, tailWord_2781089, baseEnd_2781089] using wordTrace_append hprefix tailTrace_2781089
  have hstable : (prefixWord ++ tailWord_2781089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781089).length < 2 ^ (prefixWord ++ tailWord_2781089).sum := by decide
  have hdescent : baseEnd_2781089 < baseStart_2781089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781091 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 6, 5]
def baseStart_2781091 : Nat := 118140960795 + 2781091 * 2 ^ 59
def prefixEnd_2781091 : Nat := 4983230072969 + 3 ^ 40 * 2781091 * 2
def baseEnd_2781091 : Nat := 476012142297761234124167

theorem tailTrace_2781091 : CollatzResearch.WordTrace tailWord_2781091 prefixEnd_2781091 476012142297761234124167 := by
  unfold tailWord_2781091
  simp only [CollatzResearch.WordTrace]
  refine ⟨101434721967589754373415127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67623147978393169582276751 101434721967589754373415127)
  ·
    refine ⟨152152082951384631560122691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101434721967589754373415127 152152082951384631560122691)
    ·
      refine ⟨228228124427076947340184037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152152082951384631560122691 228228124427076947340184037)
      ·
        refine ⟨42792773330076927626284507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228228124427076947340184037 42792773330076927626284507)
        ·
          refine ⟨64189159995115391439426761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42792773330076927626284507 64189159995115391439426761)
          ·
            refine ⟨48141869996336543579570071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64189159995115391439426761 48141869996336543579570071)
            ·
              refine ⟨72212804994504815369355107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48141869996336543579570071 72212804994504815369355107)
              ·
                refine ⟨108319207491757223054032661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72212804994504815369355107 108319207491757223054032661)
                ·
                  refine ⟨5077462851176119830657781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108319207491757223054032661 5077462851176119830657781)
                  ·
                    refine ⟨476012142297761234124167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5077462851176119830657781 476012142297761234124167)
                    ·
                      rfl

theorem cell23_2781091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 5].length) (baseStart_2781091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781091 prefixEnd_2781091 := by exact prefixLift 2781091
  have htrace : WordTrace (prefixWord ++ tailWord_2781091) baseStart_2781091 baseEnd_2781091 := by
    simpa [prefixWord, tailWord_2781091, baseEnd_2781091] using wordTrace_append hprefix tailTrace_2781091
  have hstable : (prefixWord ++ tailWord_2781091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781091).length < 2 ^ (prefixWord ++ tailWord_2781091).sum := by decide
  have hdescent : baseEnd_2781091 < baseStart_2781091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781118 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_2781118 : Nat := 118140960795 + 2781118 * 2 ^ 59
def prefixEnd_2781118 : Nat := 4983230072969 + 3 ^ 40 * 2781118 * 2
def baseEnd_2781118 : Nat := 1428050290870955096734877

theorem tailTrace_2781118 : CollatzResearch.WordTrace tailWord_2781118 prefixEnd_2781118 1428050290870955096734877 := by
  unfold tailWord_2781118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12679463342311492248081001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67623804492327958656432005 12679463342311492248081001)
  ·
    refine ⟨9509597506733619186060751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12679463342311492248081001 9509597506733619186060751)
    ·
      refine ⟨14264396260100428779091127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9509597506733619186060751 14264396260100428779091127)
      ·
        refine ⟨21396594390150643168636691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14264396260100428779091127 21396594390150643168636691)
        ·
          refine ⟨32094891585225964752955037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21396594390150643168636691 32094891585225964752955037)
          ·
            refine ⟨12035584344459736782358139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32094891585225964752955037 12035584344459736782358139)
            ·
              refine ⟨18053376516689605173537209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12035584344459736782358139 18053376516689605173537209)
              ·
                refine ⟨13540032387517203880152907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18053376516689605173537209 13540032387517203880152907)
                ·
                  refine ⟨20310048581275805820229361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13540032387517203880152907 20310048581275805820229361)
                  ·
                    refine ⟨15232536435956854365172021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20310048581275805820229361 15232536435956854365172021)
                    ·
                      refine ⟨1428050290870955096734877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15232536435956854365172021 1428050290870955096734877)
                      ·
                        rfl

theorem cell23_2781118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_2781118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781118 prefixEnd_2781118 := by exact prefixLift 2781118
  have htrace : WordTrace (prefixWord ++ tailWord_2781118) baseStart_2781118 baseEnd_2781118 := by
    simpa [prefixWord, tailWord_2781118, baseEnd_2781118] using wordTrace_append hprefix tailTrace_2781118
  have hstable : (prefixWord ++ tailWord_2781118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781118).length < 2 ^ (prefixWord ++ tailWord_2781118).sum := by decide
  have hdescent : baseEnd_2781118 < baseStart_2781118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781131 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 5]
def baseStart_2781131 : Nat := 118140960795 + 2781131 * 2 ^ 59
def prefixEnd_2781131 : Nat := 4983230072969 + 3 ^ 40 * 2781131 * 2
def baseEnd_2781131 : Nat := 1428056966119463545872317

theorem tailTrace_2781131 : CollatzResearch.WordTrace tailWord_2781131 prefixEnd_2781131 1428056966119463545872317 := by
  unfold tailWord_2781131
  simp only [CollatzResearch.WordTrace]
  refine ⟨101436180887444841204871247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67624120591629894136580831 101436180887444841204871247)
  ·
    refine ⟨152154271331167261807306871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101436180887444841204871247 152154271331167261807306871)
    ·
      refine ⟨228231406996750892710960307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152154271331167261807306871 228231406996750892710960307)
      ·
        refine ⟨342347110495126339066440461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228231406996750892710960307 342347110495126339066440461)
        ·
          refine ⟨128380166435672377149915173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 342347110495126339066440461 128380166435672377149915173)
          ·
            refine ⟨24071281206688570715609095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128380166435672377149915173 24071281206688570715609095)
            ·
              refine ⟨36106921810032856073413643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24071281206688570715609095 36106921810032856073413643)
              ·
                refine ⟨54160382715049284110120465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36106921810032856073413643 54160382715049284110120465)
                ·
                  refine ⟨40620287036286963082590349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54160382715049284110120465 40620287036286963082590349)
                  ·
                    refine ⟨15232607638607611155971381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40620287036286963082590349 15232607638607611155971381)
                    ·
                      refine ⟨1428056966119463545872317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15232607638607611155971381 1428056966119463545872317)
                      ·
                        rfl

theorem cell23_2781131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 5].length) (baseStart_2781131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781131 prefixEnd_2781131 := by exact prefixLift 2781131
  have htrace : WordTrace (prefixWord ++ tailWord_2781131) baseStart_2781131 baseEnd_2781131 := by
    simpa [prefixWord, tailWord_2781131, baseEnd_2781131] using wordTrace_append hprefix tailTrace_2781131
  have hstable : (prefixWord ++ tailWord_2781131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781131).length < 2 ^ (prefixWord ++ tailWord_2781131).sum := by decide
  have hdescent : baseEnd_2781131 < baseStart_2781131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781155 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 3, 4]
def baseStart_2781155 : Nat := 118140960795 + 2781155 * 2 ^ 59
def prefixEnd_2781155 : Nat := 4983230072969 + 3 ^ 40 * 2781155 * 2
def baseEnd_2781155 : Nat := 476023096551723817324069

theorem tailTrace_2781155 : CollatzResearch.WordTrace tailWord_2781155 prefixEnd_2781155 476023096551723817324069 := by
  unfold tailWord_2781155
  simp only [CollatzResearch.WordTrace]
  refine ⟨101437056239357893303744919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67624704159571928869163279 101437056239357893303744919)
  ·
    refine ⟨152155584359036839955617379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101437056239357893303744919 152155584359036839955617379)
    ·
      refine ⟨228233376538555259933426069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152155584359036839955617379 228233376538555259933426069)
      ·
        refine ⟨10698439525244777809379347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 228233376538555259933426069 10698439525244777809379347)
        ·
          refine ⟨16047659287867166714069021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10698439525244777809379347 16047659287867166714069021)
          ·
            refine ⟨6017872232950187517775883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16047659287867166714069021 6017872232950187517775883)
            ·
              refine ⟨9026808349425281276663825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6017872232950187517775883 9026808349425281276663825)
              ·
                refine ⟨6770106262068960957497869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9026808349425281276663825 6770106262068960957497869)
                ·
                  refine ⟨2538789848275860359061701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6770106262068960957497869 2538789848275860359061701)
                  ·
                    refine ⟨476023096551723817324069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2538789848275860359061701 476023096551723817324069)
                    ·
                      rfl

theorem cell23_2781155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 4].length) (baseStart_2781155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781155 prefixEnd_2781155 := by exact prefixLift 2781155
  have htrace : WordTrace (prefixWord ++ tailWord_2781155) baseStart_2781155 baseEnd_2781155 := by
    simpa [prefixWord, tailWord_2781155, baseEnd_2781155] using wordTrace_append hprefix tailTrace_2781155
  have hstable : (prefixWord ++ tailWord_2781155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781155).length < 2 ^ (prefixWord ++ tailWord_2781155).sum := by decide
  have hdescent : baseEnd_2781155 < baseStart_2781155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781171 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 6]
def baseStart_2781171 : Nat := 118140960795 + 2781171 * 2 ^ 59
def prefixEnd_2781171 : Nat := 4983230072969 + 3 ^ 40 * 2781171 * 2
def baseEnd_2781171 : Nat := 1428077505345643389372133

theorem tailTrace_2781171 : CollatzResearch.WordTrace tailWord_2781171 prefixEnd_2781171 1428077505345643389372133 := by
  unfold tailWord_2781171
  simp only [CollatzResearch.WordTrace]
  refine ⟨101437639807299928036327367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67625093204866618690884911 101437639807299928036327367)
  ·
    refine ⟨152156459710949892054491051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101437639807299928036327367 152156459710949892054491051)
    ·
      refine ⟨228234689566424838081736577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152156459710949892054491051 228234689566424838081736577)
      ·
        refine ⟨171176017174818628561302433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228234689566424838081736577 171176017174818628561302433)
        ·
          refine ⟨128382012881113971420976825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171176017174818628561302433 128382012881113971420976825)
          ·
            refine ⟨96286509660835478565732619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128382012881113971420976825 96286509660835478565732619)
            ·
              refine ⟨144429764491253217848598929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96286509660835478565732619 144429764491253217848598929)
              ·
                refine ⟨108322323368439913386449197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144429764491253217848598929 108322323368439913386449197)
                ·
                  refine ⟨40620871263164967519918449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108322323368439913386449197 40620871263164967519918449)
                  ·
                    refine ⟨30465653447373725639938837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40620871263164967519918449 30465653447373725639938837)
                    ·
                      refine ⟨1428077505345643389372133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30465653447373725639938837 1428077505345643389372133)
                      ·
                        rfl

theorem cell23_2781171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_2781171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781171 prefixEnd_2781171 := by exact prefixLift 2781171
  have htrace : WordTrace (prefixWord ++ tailWord_2781171) baseStart_2781171 baseEnd_2781171 := by
    simpa [prefixWord, tailWord_2781171, baseEnd_2781171] using wordTrace_append hprefix tailTrace_2781171
  have hstable : (prefixWord ++ tailWord_2781171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781171).length < 2 ^ (prefixWord ++ tailWord_2781171).sum := by decide
  have hdescent : baseEnd_2781171 < baseStart_2781171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781212 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_2781212 : Nat := 118140960795 + 2781212 * 2 ^ 59
def prefixEnd_2781212 : Nat := 4983230072969 + 3 ^ 40 * 2781212 * 2
def baseEnd_2781212 : Nat := 1428098558052477728959445

theorem tailTrace_2781212 : CollatzResearch.WordTrace tailWord_2781212 prefixEnd_2781212 1428098558052477728959445 := by
  unfold tailWord_2781212
  simp only [CollatzResearch.WordTrace]
  refine ⟨50719567600075696019284945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67626090133434261359046593 50719567600075696019284945)
  ·
    refine ⟨38039675700056772014463709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50719567600075696019284945 38039675700056772014463709)
    ·
      refine ⟨14264878387521289505423891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38039675700056772014463709 14264878387521289505423891)
      ·
        refine ⟨21397317581281934258135837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14264878387521289505423891 21397317581281934258135837)
        ·
          refine ⟨8023994092980725346800939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21397317581281934258135837 8023994092980725346800939)
          ·
            refine ⟨12035991139471088020201409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8023994092980725346800939 12035991139471088020201409)
            ·
              refine ⟨9026993354603316015151057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12035991139471088020201409 9026993354603316015151057)
              ·
                refine ⟨6770245015952487011363293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9026993354603316015151057 6770245015952487011363293)
                ·
                  refine ⟨2538841880982182629261235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6770245015952487011363293 2538841880982182629261235)
                  ·
                    refine ⟨3808262821473273943891853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2538841880982182629261235 3808262821473273943891853)
                    ·
                      refine ⟨1428098558052477728959445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3808262821473273943891853 1428098558052477728959445)
                      ·
                        rfl

theorem cell23_2781212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_2781212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781212 prefixEnd_2781212 := by exact prefixLift 2781212
  have htrace : WordTrace (prefixWord ++ tailWord_2781212) baseStart_2781212 baseEnd_2781212 := by
    simpa [prefixWord, tailWord_2781212, baseEnd_2781212] using wordTrace_append hprefix tailTrace_2781212
  have hstable : (prefixWord ++ tailWord_2781212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781212).length < 2 ^ (prefixWord ++ tailWord_2781212).sum := by decide
  have hdescent : baseEnd_2781212 < baseStart_2781212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781215 : List Nat := [1, 1, 2, 4, 1, 2, 4, 2, 1, 5]
def baseStart_2781215 : Nat := 118140960795 + 2781215 * 2 ^ 59
def prefixEnd_2781215 : Nat := 4983230072969 + 3 ^ 40 * 2781215 * 2
def baseEnd_2781215 : Nat := 476033366164813739073977

theorem tailTrace_2781215 : CollatzResearch.WordTrace tailWord_2781215 prefixEnd_2781215 476033366164813739073977 := by
  unfold tailWord_2781215
  simp only [CollatzResearch.WordTrace]
  refine ⟨101439244619140523550929099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67626163079427015700619399 101439244619140523550929099)
  ·
    refine ⟨152158866928710785326393649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101439244619140523550929099 152158866928710785326393649)
    ·
      refine ⟨114119150196533088994795237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152158866928710785326393649 114119150196533088994795237)
      ·
        refine ⟨21397340661849954186524107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114119150196533088994795237 21397340661849954186524107)
        ·
          refine ⟨32096010992774931279786161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21397340661849954186524107 32096010992774931279786161)
          ·
            refine ⟨24072008244581198459839621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32096010992774931279786161 24072008244581198459839621)
            ·
              refine ⟨4513501545858974711219929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24072008244581198459839621 4513501545858974711219929)
              ·
                refine ⟨3385126159394231033414947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4513501545858974711219929 3385126159394231033414947)
                ·
                  refine ⟨5077689239091346550122421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3385126159394231033414947 5077689239091346550122421)
                  ·
                    refine ⟨476033366164813739073977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5077689239091346550122421 476033366164813739073977)
                    ·
                      rfl

theorem cell23_2781215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 5].length) (baseStart_2781215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781215 prefixEnd_2781215 := by exact prefixLift 2781215
  have htrace : WordTrace (prefixWord ++ tailWord_2781215) baseStart_2781215 baseEnd_2781215 := by
    simpa [prefixWord, tailWord_2781215, baseEnd_2781215] using wordTrace_append hprefix tailTrace_2781215
  have hstable : (prefixWord ++ tailWord_2781215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781215).length < 2 ^ (prefixWord ++ tailWord_2781215).sum := by decide
  have hdescent : baseEnd_2781215 < baseStart_2781215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781223 : List Nat := [1, 1, 7, 1, 3, 1, 1, 3, 1, 4]
def baseStart_2781223 : Nat := 118140960795 + 2781223 * 2 ^ 59
def prefixEnd_2781223 : Nat := 4983230072969 + 3 ^ 40 * 2781223 * 2
def baseEnd_2781223 : Nat := 476034735446559061973965

theorem tailTrace_2781223 : CollatzResearch.WordTrace tailWord_2781223 prefixEnd_2781223 476034735446559061973965 := by
  unfold tailWord_2781223
  simp only [CollatzResearch.WordTrace]
  refine ⟨101439536403111540917220323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67626357602074360611480215 101439536403111540917220323)
  ·
    refine ⟨152159304604667311375830485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101439536403111540917220323 152159304604667311375830485)
    ·
      refine ⟨3566233701671890110371027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 152159304604667311375830485 3566233701671890110371027)
      ·
        refine ⟨5349350552507835165556541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3566233701671890110371027 5349350552507835165556541)
        ·
          refine ⟨2006006457190438187083703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5349350552507835165556541 2006006457190438187083703)
          ·
            refine ⟨3009009685785657280625555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006006457190438187083703 3009009685785657280625555)
            ·
              refine ⟨4513514528678485920938333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3009009685785657280625555 4513514528678485920938333)
              ·
                refine ⟨1692567948254432220351875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4513514528678485920938333 1692567948254432220351875)
                ·
                  refine ⟨2538851922381648330527813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692567948254432220351875 2538851922381648330527813)
                  ·
                    refine ⟨476034735446559061973965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2538851922381648330527813 476034735446559061973965)
                    ·
                      rfl

theorem cell23_2781223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_2781223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781223 prefixEnd_2781223 := by exact prefixLift 2781223
  have htrace : WordTrace (prefixWord ++ tailWord_2781223) baseStart_2781223 baseEnd_2781223 := by
    simpa [prefixWord, tailWord_2781223, baseEnd_2781223] using wordTrace_append hprefix tailTrace_2781223
  have hstable : (prefixWord ++ tailWord_2781223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781223).length < 2 ^ (prefixWord ++ tailWord_2781223).sum := by decide
  have hdescent : baseEnd_2781223 < baseStart_2781223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781235 : List Nat := [1, 1, 1, 2, 4, 1, 4, 3, 1, 1, 4]
def baseStart_2781235 : Nat := 118140960795 + 2781235 * 2 ^ 59
def prefixEnd_2781235 : Nat := 4983230072969 + 3 ^ 40 * 2781235 * 2
def baseEnd_2781235 : Nat := 1428110368107531138971839

theorem tailTrace_2781235 : CollatzResearch.WordTrace tailWord_2781235 prefixEnd_2781235 1428110368107531138971839 := by
  unfold tailWord_2781235
  simp only [CollatzResearch.WordTrace]
  refine ⟨101439974079068066966657159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67626649386045377977771439 101439974079068066966657159)
  ·
    refine ⟨152159961118602100449985739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101439974079068066966657159 152159961118602100449985739)
    ·
      refine ⟨228239941677903150674978609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152159961118602100449985739 228239941677903150674978609)
      ·
        refine ⟨171179956258427363006233957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228239941677903150674978609 171179956258427363006233957)
        ·
          refine ⟨32096241798455130563668867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171179956258427363006233957 32096241798455130563668867)
          ·
            refine ⟨48144362697682695845503301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32096241798455130563668867 48144362697682695845503301)
            ·
              refine ⟨9027068005815505471031869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48144362697682695845503301 9027068005815505471031869)
              ·
                refine ⟨3385150502180814551636951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9027068005815505471031869 3385150502180814551636951)
                ·
                  refine ⟨5077725753271221827455427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3385150502180814551636951 5077725753271221827455427)
                  ·
                    refine ⟨7616588629906832741183141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5077725753271221827455427 7616588629906832741183141)
                    ·
                      refine ⟨1428110368107531138971839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7616588629906832741183141 1428110368107531138971839)
                      ·
                        rfl

theorem cell23_2781235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 1, 4].length) (baseStart_2781235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781235 prefixEnd_2781235 := by exact prefixLift 2781235
  have htrace : WordTrace (prefixWord ++ tailWord_2781235) baseStart_2781235 baseEnd_2781235 := by
    simpa [prefixWord, tailWord_2781235, baseEnd_2781235] using wordTrace_append hprefix tailTrace_2781235
  have hstable : (prefixWord ++ tailWord_2781235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781235).length < 2 ^ (prefixWord ++ tailWord_2781235).sum := by decide
  have hdescent : baseEnd_2781235 < baseStart_2781235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781245 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 4, 4]
def baseStart_2781245 : Nat := 118140960795 + 2781245 * 2 ^ 59
def prefixEnd_2781245 : Nat := 4983230072969 + 3 ^ 40 * 2781245 * 2
def baseEnd_2781245 : Nat := 476038500971358699948931

theorem tailTrace_2781245 : CollatzResearch.WordTrace tailWord_2781245 prefixEnd_2781245 476038500971358699948931 := by
  unfold tailWord_2781245
  simp only [CollatzResearch.WordTrace]
  refine ⟨101440338809031838674521189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67626892539354559116347459 101440338809031838674521189)
  ·
    refine ⟨19020063526693469751472723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101440338809031838674521189 19020063526693469751472723)
    ·
      refine ⟨28530095290040204627209085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19020063526693469751472723 28530095290040204627209085)
      ·
        refine ⟨10698785733765076735203407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28530095290040204627209085 10698785733765076735203407)
        ·
          refine ⟨16048178600647615102805111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10698785733765076735203407 16048178600647615102805111)
          ·
            refine ⟨24072267900971422654207667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16048178600647615102805111 24072267900971422654207667)
            ·
              refine ⟨36108401851457133981311501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24072267900971422654207667 36108401851457133981311501)
              ·
                refine ⟨13540650694296425242991813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36108401851457133981311501 13540650694296425242991813)
                ·
                  refine ⟨2538872005180579733060965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13540650694296425242991813 2538872005180579733060965)
                  ·
                    refine ⟨476038500971358699948931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2538872005180579733060965 476038500971358699948931)
                    ·
                      rfl

theorem cell23_2781245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_2781245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781245 prefixEnd_2781245 := by exact prefixLift 2781245
  have htrace : WordTrace (prefixWord ++ tailWord_2781245) baseStart_2781245 baseEnd_2781245 := by
    simpa [prefixWord, tailWord_2781245, baseEnd_2781245] using wordTrace_append hprefix tailTrace_2781245
  have hstable : (prefixWord ++ tailWord_2781245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781245).length < 2 ^ (prefixWord ++ tailWord_2781245).sum := by decide
  have hdescent : baseEnd_2781245 < baseStart_2781245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781246 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_2781246 : Nat := 118140960795 + 2781246 * 2 ^ 59
def prefixEnd_2781246 : Nat := 4983230072969 + 3 ^ 40 * 2781246 * 2
def baseEnd_2781246 : Nat := 1428116016394730595934289

theorem tailTrace_2781246 : CollatzResearch.WordTrace tailWord_2781246 prefixEnd_2781246 1428116016394730595934289 := by
  unfold tailWord_2781246
  simp only [CollatzResearch.WordTrace]
  refine ⟨12680046910253526980663449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67626916854685477230205061 12680046910253526980663449)
  ·
    refine ⟨9510035182690145235497587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12680046910253526980663449 9510035182690145235497587)
    ·
      refine ⟨14265052774035217853246381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9510035182690145235497587 14265052774035217853246381)
      ·
        refine ⟨5349394790263206694967393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14265052774035217853246381 5349394790263206694967393)
        ·
          refine ⟨4012046092697405021225545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5349394790263206694967393 4012046092697405021225545)
          ·
            refine ⟨3009034569523053765919159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4012046092697405021225545 3009034569523053765919159)
            ·
              refine ⟨4513551854284580648878739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3009034569523053765919159 4513551854284580648878739)
              ·
                refine ⟨6770327781426870973318109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4513551854284580648878739 6770327781426870973318109)
                ·
                  refine ⟨2538872918035076614994291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6770327781426870973318109 2538872918035076614994291)
                  ·
                    refine ⟨3808309377052614922491437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2538872918035076614994291 3808309377052614922491437)
                    ·
                      refine ⟨1428116016394730595934289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3808309377052614922491437 1428116016394730595934289)
                      ·
                        rfl

theorem cell23_2781246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_2781246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781246 prefixEnd_2781246 := by exact prefixLift 2781246
  have htrace : WordTrace (prefixWord ++ tailWord_2781246) baseStart_2781246 baseEnd_2781246 := by
    simpa [prefixWord, tailWord_2781246, baseEnd_2781246] using wordTrace_append hprefix tailTrace_2781246
  have hstable : (prefixWord ++ tailWord_2781246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781246).length < 2 ^ (prefixWord ++ tailWord_2781246).sum := by decide
  have hdescent : baseEnd_2781246 < baseStart_2781246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781248 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 6]
def baseStart_2781248 : Nat := 118140960795 + 2781248 * 2 ^ 59
def prefixEnd_2781248 : Nat := 4983230072969 + 3 ^ 40 * 2781248 * 2
def baseEnd_2781248 : Nat := 1428117043356039588109279

theorem tailTrace_2781248 : CollatzResearch.WordTrace tailWord_2781248 prefixEnd_2781248 1428117043356039588109279 := by
  unfold tailWord_2781248
  simp only [CollatzResearch.WordTrace]
  refine ⟨50720224114010485093440199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67626965485347313457920265 50720224114010485093440199)
  ·
    refine ⟨76080336171015727640160299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50720224114010485093440199 76080336171015727640160299)
    ·
      refine ⟨114120504256523591460240449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76080336171015727640160299 114120504256523591460240449)
      ·
        refine ⟨85590378192392693595180337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114120504256523591460240449 85590378192392693595180337)
        ·
          refine ⟨64192783644294520196385253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85590378192392693595180337 64192783644294520196385253)
          ·
            refine ⟨12036146933305222536822235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64192783644294520196385253 12036146933305222536822235)
            ·
              refine ⟨18054220399957833805233353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12036146933305222536822235 18054220399957833805233353)
              ·
                refine ⟨13540665299968375353925015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18054220399957833805233353 13540665299968375353925015)
                ·
                  refine ⟨20310997949952563030887523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13540665299968375353925015 20310997949952563030887523)
                  ·
                    refine ⟨30466496924928844546331285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20310997949952563030887523 30466496924928844546331285)
                    ·
                      refine ⟨1428117043356039588109279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30466496924928844546331285 1428117043356039588109279)
                      ·
                        rfl

theorem cell23_2781248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_2781248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781248 prefixEnd_2781248 := by exact prefixLift 2781248
  have htrace : WordTrace (prefixWord ++ tailWord_2781248) baseStart_2781248 baseEnd_2781248 := by
    simpa [prefixWord, tailWord_2781248, baseEnd_2781248] using wordTrace_append hprefix tailTrace_2781248
  have hstable : (prefixWord ++ tailWord_2781248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781248).length < 2 ^ (prefixWord ++ tailWord_2781248).sum := by decide
  have hdescent : baseEnd_2781248 < baseStart_2781248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781255 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 3]
def baseStart_2781255 : Nat := 118140960795 + 2781255 * 2 ^ 59
def prefixEnd_2781255 : Nat := 4983230072969 + 3 ^ 40 * 2781255 * 2
def baseEnd_2781255 : Nat := 1428120637720621060721747

theorem tailTrace_2781255 : CollatzResearch.WordTrace tailWord_2781255 prefixEnd_2781255 1428120637720621060721747 := by
  unfold tailWord_2781255
  simp only [CollatzResearch.WordTrace]
  refine ⟨101440703538995610382385219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67627135692663740254923479 101440703538995610382385219)
  ·
    refine ⟨152161055308493415573577829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101440703538995610382385219 152161055308493415573577829)
    ·
      refine ⟨28530197870342515420045843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152161055308493415573577829 28530197870342515420045843)
      ·
        refine ⟨42795296805513773130068765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28530197870342515420045843 42795296805513773130068765)
        ·
          refine ⟨16048236302067664923775787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42795296805513773130068765 16048236302067664923775787)
          ·
            refine ⟨24072354453101497385663681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16048236302067664923775787 24072354453101497385663681)
            ·
              refine ⟨18054265839826123039247761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24072354453101497385663681 18054265839826123039247761)
              ·
                refine ⟨13540699379869592279435821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18054265839826123039247761 13540699379869592279435821)
                ·
                  refine ⟨5077762267451097104788433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13540699379869592279435821 5077762267451097104788433)
                  ·
                    refine ⟨3808321700588322828591325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5077762267451097104788433 3808321700588322828591325)
                    ·
                      refine ⟨1428120637720621060721747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3808321700588322828591325 1428120637720621060721747)
                      ·
                        rfl

theorem cell23_2781255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_2781255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781255 prefixEnd_2781255 := by exact prefixLift 2781255
  have htrace : WordTrace (prefixWord ++ tailWord_2781255) baseStart_2781255 baseEnd_2781255 := by
    simpa [prefixWord, tailWord_2781255, baseEnd_2781255] using wordTrace_append hprefix tailTrace_2781255
  have hstable : (prefixWord ++ tailWord_2781255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781255).length < 2 ^ (prefixWord ++ tailWord_2781255).sum := by decide
  have hdescent : baseEnd_2781255 < baseStart_2781255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781262 : List Nat := [4, 1, 1, 1, 1, 5, 1, 3, 2, 4]
def baseStart_2781262 : Nat := 118140960795 + 2781262 * 2 ^ 59
def prefixEnd_2781262 : Nat := 4983230072969 + 3 ^ 40 * 2781262 * 2
def baseEnd_2781262 : Nat := 476041410695067511111405

theorem tailTrace_2781262 : CollatzResearch.WordTrace tailWord_2781262 prefixEnd_2781262 476041410695067511111405 := by
  unfold tailWord_2781262
  simp only [CollatzResearch.WordTrace]
  refine ⟨12680119856246281322236255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67627305899980167051926693 12680119856246281322236255)
  ·
    refine ⟨19020179784369421983354383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12680119856246281322236255 19020179784369421983354383)
    ·
      refine ⟨28530269676554132975031575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19020179784369421983354383 28530269676554132975031575)
      ·
        refine ⟨42795404514831199462547363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28530269676554132975031575 42795404514831199462547363)
        ·
          refine ⟨64193106772246799193821045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42795404514831199462547363 64193106772246799193821045)
          ·
            refine ⟨6018103759898137424420723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64193106772246799193821045 6018103759898137424420723)
            ·
              refine ⟨9027155639847206136631085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6018103759898137424420723 9027155639847206136631085)
              ·
                refine ⟨3385183364942702301236657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9027155639847206136631085 3385183364942702301236657)
                ·
                  refine ⟨2538887523707026725927493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3385183364942702301236657 2538887523707026725927493)
                  ·
                    refine ⟨476041410695067511111405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2538887523707026725927493 476041410695067511111405)
                    ·
                      rfl

theorem cell23_2781262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_2781262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781262 prefixEnd_2781262 := by exact prefixLift 2781262
  have htrace : WordTrace (prefixWord ++ tailWord_2781262) baseStart_2781262 baseEnd_2781262 := by
    simpa [prefixWord, tailWord_2781262, baseEnd_2781262] using wordTrace_append hprefix tailTrace_2781262
  have hstable : (prefixWord ++ tailWord_2781262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781262).length < 2 ^ (prefixWord ++ tailWord_2781262).sum := by decide
  have hdescent : baseEnd_2781262 < baseStart_2781262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781272 : List Nat := [2, 1, 2, 2, 1, 4, 3, 2, 1, 2, 3]
def baseStart_2781272 : Nat := 118140960795 + 2781272 * 2 ^ 59
def prefixEnd_2781272 : Nat := 4983230072969 + 3 ^ 40 * 2781272 * 2
def baseEnd_2781272 : Nat := 1428129366891747494209169

theorem tailTrace_2781272 : CollatzResearch.WordTrace tailWord_2781272 prefixEnd_2781272 1428129366891747494209169 := by
  unfold tailWord_2781272
  simp only [CollatzResearch.WordTrace]
  refine ⟨50720661789967011142877035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67627549053289348190502713 50720661789967011142877035)
  ·
    refine ⟨76080992684950516714315553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50720661789967011142877035 76080992684950516714315553)
    ·
      refine ⟨57060744513712887535736665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76080992684950516714315553 57060744513712887535736665)
      ·
        refine ⟨42795558385284665651802499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57060744513712887535736665 42795558385284665651802499)
        ·
          refine ⟨64193337577926998477703749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42795558385284665651802499 64193337577926998477703749)
          ·
            refine ⟨12036250795861312214569453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64193337577926998477703749 12036250795861312214569453)
            ·
              refine ⟨4513594048447992080463545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12036250795861312214569453 4513594048447992080463545)
              ·
                refine ⟨3385195536335994060347659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4513594048447992080463545 3385195536335994060347659)
                ·
                  refine ⟨5077793304503991090521489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3385195536335994060347659 5077793304503991090521489)
                  ·
                    refine ⟨3808344978377993317891117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5077793304503991090521489 3808344978377993317891117)
                    ·
                      refine ⟨1428129366891747494209169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3808344978377993317891117 1428129366891747494209169)
                      ·
                        rfl

theorem cell23_2781272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_2781272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781272 prefixEnd_2781272 := by exact prefixLift 2781272
  have htrace : WordTrace (prefixWord ++ tailWord_2781272) baseStart_2781272 baseEnd_2781272 := by
    simpa [prefixWord, tailWord_2781272, baseEnd_2781272] using wordTrace_append hprefix tailTrace_2781272
  have hstable : (prefixWord ++ tailWord_2781272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781272).length < 2 ^ (prefixWord ++ tailWord_2781272).sum := by decide
  have hdescent : baseEnd_2781272 < baseStart_2781272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781285 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 3, 3, 3]
def baseStart_2781285 : Nat := 118140960795 + 2781285 * 2 ^ 59
def prefixEnd_2781285 : Nat := 4983230072969 + 3 ^ 40 * 2781285 * 2
def baseEnd_2781285 : Nat := 1428136042140255943346609

theorem tailTrace_2781285 : CollatzResearch.WordTrace tailWord_2781285 prefixEnd_2781285 1428136042140255943346609 := by
  unfold tailWord_2781285
  simp only [CollatzResearch.WordTrace]
  refine ⟨101441797728886925505977309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67627865152591283670651539 101441797728886925505977309)
  ·
    refine ⟨38040674148332597064741491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101441797728886925505977309 38040674148332597064741491)
    ·
      refine ⟨57061011222498895597112237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38040674148332597064741491 57061011222498895597112237)
      ·
        refine ⟨21397879208437085848917089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57061011222498895597112237 21397879208437085848917089)
        ·
          refine ⟨16048409406327814386687817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21397879208437085848917089 16048409406327814386687817)
          ·
            refine ⟨12036307054745860790015863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16048409406327814386687817 12036307054745860790015863)
            ·
              refine ⟨18054460582118791185023795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12036307054745860790015863 18054460582118791185023795)
              ·
                refine ⟨27081690873178186777535693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18054460582118791185023795 27081690873178186777535693)
                ·
                  refine ⟨10155634077441820041575885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27081690873178186777535693 10155634077441820041575885)
                  ·
                    refine ⟨3808362779040682515590957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10155634077441820041575885 3808362779040682515590957)
                    ·
                      refine ⟨1428136042140255943346609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3808362779040682515590957 1428136042140255943346609)
                      ·
                        rfl

theorem cell23_2781285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_2781285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781285 prefixEnd_2781285 := by exact prefixLift 2781285
  have htrace : WordTrace (prefixWord ++ tailWord_2781285) baseStart_2781285 baseEnd_2781285 := by
    simpa [prefixWord, tailWord_2781285, baseEnd_2781285] using wordTrace_append hprefix tailTrace_2781285
  have hstable : (prefixWord ++ tailWord_2781285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781285).length < 2 ^ (prefixWord ++ tailWord_2781285).sum := by decide
  have hdescent : baseEnd_2781285 < baseStart_2781285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781303 : List Nat := [1, 1, 3, 1, 1, 7, 2, 2, 1, 2, 2]
def baseStart_2781303 : Nat := 118140960795 + 2781303 * 2 ^ 59
def prefixEnd_2781303 : Nat := 4983230072969 + 3 ^ 40 * 2781303 * 2
def baseEnd_2781303 : Nat := 1428145284792036872921527

theorem tailTrace_2781303 : CollatzResearch.WordTrace tailWord_2781303 prefixEnd_2781303 1428145284792036872921527 := by
  unfold tailWord_2781303
  simp only [CollatzResearch.WordTrace]
  refine ⟨101442454242821714580132563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67628302828547809720088375 101442454242821714580132563)
  ·
    refine ⟨152163681364232571870198845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101442454242821714580132563 152163681364232571870198845)
    ·
      refine ⟨57061380511587214451324567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152163681364232571870198845 57061380511587214451324567)
      ·
        refine ⟨85592070767380821676986851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57061380511587214451324567 85592070767380821676986851)
        ·
          refine ⟨128388106151071232515480277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85592070767380821676986851 128388106151071232515480277)
          ·
            refine ⟨3009096237915732012081569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 128388106151071232515480277 3009096237915732012081569)
            ·
              refine ⟨2256822178436799009061177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3009096237915732012081569 2256822178436799009061177)
              ·
                refine ⟨1692616633827599256795883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2256822178436799009061177 1692616633827599256795883)
                ·
                  refine ⟨2538924950741398885193825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692616633827599256795883 2538924950741398885193825)
                  ·
                    refine ⟨1904193713056049163895369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2538924950741398885193825 1904193713056049163895369)
                    ·
                      refine ⟨1428145284792036872921527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1904193713056049163895369 1428145284792036872921527)
                      ·
                        rfl

theorem cell23_2781303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 1, 2, 2].length) (baseStart_2781303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781303 prefixEnd_2781303 := by exact prefixLift 2781303
  have htrace : WordTrace (prefixWord ++ tailWord_2781303) baseStart_2781303 baseEnd_2781303 := by
    simpa [prefixWord, tailWord_2781303, baseEnd_2781303] using wordTrace_append hprefix tailTrace_2781303
  have hstable : (prefixWord ++ tailWord_2781303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781303).length < 2 ^ (prefixWord ++ tailWord_2781303).sum := by decide
  have hdescent : baseEnd_2781303 < baseStart_2781303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781346 : List Nat := [3, 3, 1, 3, 1, 2, 1, 3, 1, 3, 2]
def baseStart_2781346 : Nat := 118140960795 + 2781346 * 2 ^ 59
def prefixEnd_2781346 : Nat := 4983230072969 + 3 ^ 40 * 2781346 * 2
def baseEnd_2781346 : Nat := 1428167364460180204683829

theorem tailTrace_2781346 : CollatzResearch.WordTrace tailWord_2781346 prefixEnd_2781346 1428167364460180204683829 := by
  unfold tailWord_2781346
  simp only [CollatzResearch.WordTrace]
  refine ⟨25361005645416483230986973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67629348387777288615965261 25361005645416483230986973)
  ·
    refine ⟨9510377117031181211620115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25361005645416483230986973 9510377117031181211620115)
    ·
      refine ⟨14265565675546771817430173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9510377117031181211620115 14265565675546771817430173)
      ·
        refine ⟨5349587128330039431536315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14265565675546771817430173 5349587128330039431536315)
        ·
          refine ⟨8024380692495059147304473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5349587128330039431536315 8024380692495059147304473)
          ·
            refine ⟨6018285519371294360478355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8024380692495059147304473 6018285519371294360478355)
            ·
              refine ⟨9027428279056941540717533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6018285519371294360478355 9027428279056941540717533)
              ·
                refine ⟨3385285604646353077769075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9027428279056941540717533 3385285604646353077769075)
                ·
                  refine ⟨5077928406969529616653613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3385285604646353077769075 5077928406969529616653613)
                  ·
                    refine ⟨1904223152613573606245105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5077928406969529616653613 1904223152613573606245105)
                    ·
                      refine ⟨1428167364460180204683829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1904223152613573606245105 1428167364460180204683829)
                      ·
                        rfl

theorem cell23_2781346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_2781346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781346 prefixEnd_2781346 := by exact prefixLift 2781346
  have htrace : WordTrace (prefixWord ++ tailWord_2781346) baseStart_2781346 baseEnd_2781346 := by
    simpa [prefixWord, tailWord_2781346, baseEnd_2781346] using wordTrace_append hprefix tailTrace_2781346
  have hstable : (prefixWord ++ tailWord_2781346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781346).length < 2 ^ (prefixWord ++ tailWord_2781346).sum := by decide
  have hdescent : baseEnd_2781346 < baseStart_2781346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781432 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 2, 4, 2]
def baseStart_2781432 : Nat := 118140960795 + 2781432 * 2 ^ 59
def prefixEnd_2781432 : Nat := 4983230072969 + 3 ^ 40 * 2781432 * 2
def baseEnd_2781432 : Nat := 1428211523796466868208433

theorem tailTrace_2781432 : CollatzResearch.WordTrace tailWord_2781432 prefixEnd_2781432 1428211523796466868208433 := by
  unfold tailWord_2781432
  simp only [CollatzResearch.WordTrace]
  refine ⟨50723579629677184805789275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67631439506236246407719033 50723579629677184805789275)
  ·
    refine ⟨76085369444515777208683913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50723579629677184805789275 76085369444515777208683913)
    ·
      refine ⟨57064027083386832906512935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76085369444515777208683913 57064027083386832906512935)
      ·
        refine ⟨85596040625080249359769403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57064027083386832906512935 85596040625080249359769403)
        ·
          refine ⟨128394060937620374039654105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85596040625080249359769403 128394060937620374039654105)
          ·
            refine ⟨96295545703215280529740579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128394060937620374039654105 96295545703215280529740579)
            ·
              refine ⟨144443318554822920794610869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96295545703215280529740579 144443318554822920794610869)
              ·
                refine ⟨13541561114514648824494769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144443318554822920794610869 13541561114514648824494769)
                ·
                  refine ⟨10156170835885986618371077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13541561114514648824494769 10156170835885986618371077)
                  ·
                    refine ⟨1904282031728622490944577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10156170835885986618371077 1904282031728622490944577)
                    ·
                      refine ⟨1428211523796466868208433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1904282031728622490944577 1428211523796466868208433)
                      ·
                        rfl

theorem cell23_2781432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 2, 4, 2].length) (baseStart_2781432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781432 prefixEnd_2781432 := by exact prefixLift 2781432
  have htrace : WordTrace (prefixWord ++ tailWord_2781432) baseStart_2781432 baseEnd_2781432 := by
    simpa [prefixWord, tailWord_2781432, baseEnd_2781432] using wordTrace_append hprefix tailTrace_2781432
  have hstable : (prefixWord ++ tailWord_2781432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781432).length < 2 ^ (prefixWord ++ tailWord_2781432).sum := by decide
  have hdescent : baseEnd_2781432 < baseStart_2781432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781472 : List Nat := [2, 1, 1, 5, 2, 1, 1, 4, 6]
def baseStart_2781472 : Nat := 118140960795 + 2781472 * 2 ^ 59
def prefixEnd_2781472 : Nat := 4983230072969 + 3 ^ 40 * 2781472 * 2
def baseEnd_2781472 : Nat := 158692451446960745745361

theorem tailTrace_2781472 : CollatzResearch.WordTrace tailWord_2781472 prefixEnd_2781472 158692451446960745745361 := by
  unfold tailWord_2781472
  simp only [CollatzResearch.WordTrace]
  refine ⟨50724309089604728221517335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67632412119472970962023113 50724309089604728221517335)
  ·
    refine ⟨76086463634407092332276003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50724309089604728221517335 76086463634407092332276003)
    ·
      refine ⟨114129695451610638498414005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76086463634407092332276003 114129695451610638498414005)
      ·
        refine ⟨10699658948588497359226313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114129695451610638498414005 10699658948588497359226313)
        ·
          refine ⟨8024744211441373019419735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10699658948588497359226313 8024744211441373019419735)
          ·
            refine ⟨12037116317162059529129603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8024744211441373019419735 12037116317162059529129603)
            ·
              refine ⟨18055674475743089293694405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12037116317162059529129603 18055674475743089293694405)
              ·
                refine ⟨3385438964201829242567701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18055674475743089293694405 3385438964201829242567701)
                ·
                  refine ⟨158692451446960745745361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3385438964201829242567701 158692451446960745745361)
                  ·
                    rfl

theorem cell23_2781472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 6].length) (baseStart_2781472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781472 prefixEnd_2781472 := by exact prefixLift 2781472
  have htrace : WordTrace (prefixWord ++ tailWord_2781472) baseStart_2781472 baseEnd_2781472 := by
    simpa [prefixWord, tailWord_2781472, baseEnd_2781472] using wordTrace_append hprefix tailTrace_2781472
  have hstable : (prefixWord ++ tailWord_2781472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781472).length < 2 ^ (prefixWord ++ tailWord_2781472).sum := by decide
  have hdescent : baseEnd_2781472 < baseStart_2781472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781475 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 6]
def baseStart_2781475 : Nat := 118140960795 + 2781475 * 2 ^ 59
def prefixEnd_2781475 : Nat := 4983230072969 + 3 ^ 40 * 2781475 * 2
def baseEnd_2781475 : Nat := 1428233603464610199970735

theorem tailTrace_2781475 : CollatzResearch.WordTrace tailWord_2781475 prefixEnd_2781475 1428233603464610199970735 := by
  unfold tailWord_2781475
  simp only [CollatzResearch.WordTrace]
  refine ⟨101448727598198587955393879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67632485065465725303595919 101448727598198587955393879)
  ·
    refine ⟨152173091397297881933090819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101448727598198587955393879 152173091397297881933090819)
    ·
      refine ⟨228259637095946822899636229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152173091397297881933090819 228259637095946822899636229)
      ·
        refine ⟨42798681955490029293681793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228259637095946822899636229 42798681955490029293681793)
        ·
          refine ⟨32099011466617521970261345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42798681955490029293681793 32099011466617521970261345)
          ·
            refine ⟨24074258599963141477696009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32099011466617521970261345 24074258599963141477696009)
            ·
              refine ⟨18055693949972356108272007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24074258599963141477696009 18055693949972356108272007)
              ·
                refine ⟨27083540924958534162408011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18055693949972356108272007 27083540924958534162408011)
                ·
                  refine ⟨40625311387437801243612017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27083540924958534162408011 40625311387437801243612017)
                  ·
                    refine ⟨30468983540578350932709013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40625311387437801243612017 30468983540578350932709013)
                    ·
                      refine ⟨1428233603464610199970735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30468983540578350932709013 1428233603464610199970735)
                      ·
                        rfl

theorem cell23_2781475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_2781475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781475 prefixEnd_2781475 := by exact prefixLift 2781475
  have htrace : WordTrace (prefixWord ++ tailWord_2781475) baseStart_2781475 baseEnd_2781475 := by
    simpa [prefixWord, tailWord_2781475, baseEnd_2781475] using wordTrace_append hprefix tailTrace_2781475
  have hstable : (prefixWord ++ tailWord_2781475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781475).length < 2 ^ (prefixWord ++ tailWord_2781475).sum := by decide
  have hdescent : baseEnd_2781475 < baseStart_2781475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781476 : List Nat := [2, 3, 1, 3, 1, 3, 1, 4, 1, 4]
def baseStart_2781476 : Nat := 118140960795 + 2781476 * 2 ^ 59
def prefixEnd_2781476 : Nat := 4983230072969 + 3 ^ 40 * 2781476 * 2
def baseEnd_2781476 : Nat := 476078038981754898686077

theorem tailTrace_2781476 : CollatzResearch.WordTrace tailWord_2781476 prefixEnd_2781476 476078038981754898686077 := by
  unfold tailWord_2781476
  simp only [CollatzResearch.WordTrace]
  refine ⟨50724382035597482563090141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67632509380796643417453521 50724382035597482563090141)
  ·
    refine ⟨19021643263349055961158803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50724382035597482563090141 19021643263349055961158803)
    ·
      refine ⟨28532464895023583941738205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19021643263349055961158803 28532464895023583941738205)
      ·
        refine ⟨10699674335633843978151827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28532464895023583941738205 10699674335633843978151827)
        ·
          refine ⟨16049511503450765967227741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10699674335633843978151827 16049511503450765967227741)
          ·
            refine ⟨6018566813794037237710403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16049511503450765967227741 6018566813794037237710403)
            ·
              refine ⟨9027850220691055856565605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6018566813794037237710403 9027850220691055856565605)
              ·
                refine ⟨1692721916379572973106051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9027850220691055856565605 1692721916379572973106051)
                ·
                  refine ⟨2539082874569359459659077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692721916379572973106051 2539082874569359459659077)
                  ·
                    refine ⟨476078038981754898686077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2539082874569359459659077 476078038981754898686077)
                    ·
                      rfl

theorem cell23_2781476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_2781476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781476 prefixEnd_2781476 := by exact prefixLift 2781476
  have htrace : WordTrace (prefixWord ++ tailWord_2781476) baseStart_2781476 baseEnd_2781476 := by
    simpa [prefixWord, tailWord_2781476, baseEnd_2781476] using wordTrace_append hprefix tailTrace_2781476
  have hstable : (prefixWord ++ tailWord_2781476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781476).length < 2 ^ (prefixWord ++ tailWord_2781476).sum := by decide
  have hdescent : baseEnd_2781476 < baseStart_2781476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781515 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 3, 6]
def baseStart_2781515 : Nat := 118140960795 + 2781515 * 2 ^ 59
def prefixEnd_2781515 : Nat := 4983230072969 + 3 ^ 40 * 2781515 * 2
def baseEnd_2781515 : Nat := 476084714230263347823517

theorem tailTrace_2781515 : CollatzResearch.WordTrace tailWord_2781515 prefixEnd_2781515 476084714230263347823517 := by
  unfold tailWord_2781515
  simp only [CollatzResearch.WordTrace]
  refine ⟨101450186518053674786849999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67633457678702449857899999 101450186518053674786849999)
  ·
    refine ⟨152175279777080512180274999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101450186518053674786849999 152175279777080512180274999)
    ·
      refine ⟨228262919665620768270412499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152175279777080512180274999 228262919665620768270412499)
      ·
        refine ⟨342394379498431152405618749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228262919665620768270412499 342394379498431152405618749)
        ·
          refine ⟨128397892311911682152107031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 342394379498431152405618749 128397892311911682152107031)
          ·
            refine ⟨192596838467867523228160547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128397892311911682152107031 192596838467867523228160547)
            ·
              refine ⟨288895257701801284842240821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192596838467867523228160547 288895257701801284842240821)
              ·
                refine ⟨27083930409543870453960077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 288895257701801284842240821 27083930409543870453960077)
                ·
                  refine ⟨10156473903578951420235029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27083930409543870453960077 10156473903578951420235029)
                  ·
                    refine ⟨476084714230263347823517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10156473903578951420235029 476084714230263347823517)
                    ·
                      rfl

theorem cell23_2781515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 6].length) (baseStart_2781515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781515 prefixEnd_2781515 := by exact prefixLift 2781515
  have htrace : WordTrace (prefixWord ++ tailWord_2781515) baseStart_2781515 baseEnd_2781515 := by
    simpa [prefixWord, tailWord_2781515, baseEnd_2781515] using wordTrace_append hprefix tailTrace_2781515
  have hstable : (prefixWord ++ tailWord_2781515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781515).length < 2 ^ (prefixWord ++ tailWord_2781515).sum := by decide
  have hdescent : baseEnd_2781515 < baseStart_2781515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781545 : List Nat := [1, 2, 1, 1, 1, 3, 4, 10]
def baseStart_2781545 : Nat := 118140960795 + 2781545 * 2 ^ 59
def prefixEnd_2781545 : Nat := 4983230072969 + 3 ^ 40 * 2781545 * 2
def baseEnd_2781545 : Nat := 52898872115200923188719

theorem tailTrace_2781545 : CollatzResearch.WordTrace tailWord_2781545 prefixEnd_2781545 52898872115200923188719 := by
  unfold tailWord_2781545
  simp only [CollatzResearch.WordTrace]
  refine ⟨101451280707944989910442089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67634187138629993273628059 101451280707944989910442089)
  ·
    refine ⟨76088460530958742432831567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101451280707944989910442089 76088460530958742432831567)
    ·
      refine ⟨114132690796438113649247351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76088460530958742432831567 114132690796438113649247351)
      ·
        refine ⟨171199036194657170473871027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114132690796438113649247351 171199036194657170473871027)
        ·
          refine ⟨256798554291985755710806541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171199036194657170473871027 256798554291985755710806541)
          ·
            refine ⟨96299457859494658391552453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256798554291985755710806541 96299457859494658391552453)
            ·
              refine ⟨18056148348655248448416085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96299457859494658391552453 18056148348655248448416085)
              ·
                refine ⟨52898872115200923188719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18056148348655248448416085 52898872115200923188719)
                ·
                  rfl

theorem cell23_2781545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 10].length) (baseStart_2781545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781545 prefixEnd_2781545 := by exact prefixLift 2781545
  have htrace : WordTrace (prefixWord ++ tailWord_2781545) baseStart_2781545 baseEnd_2781545 := by
    simpa [prefixWord, tailWord_2781545, baseEnd_2781545] using wordTrace_append hprefix tailTrace_2781545
  have hstable : (prefixWord ++ tailWord_2781545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781545).length < 2 ^ (prefixWord ++ tailWord_2781545).sum := by decide
  have hdescent : baseEnd_2781545 < baseStart_2781545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781552 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 6]
def baseStart_2781552 : Nat := 118140960795 + 2781552 * 2 ^ 59
def prefixEnd_2781552 : Nat := 4983230072969 + 3 ^ 40 * 2781552 * 2
def baseEnd_2781552 : Nat := 1428273141475006398707881

theorem tailTrace_2781552 : CollatzResearch.WordTrace tailWord_2781552 prefixEnd_2781552 1428273141475006398707881 := by
  unfold tailWord_2781552
  simp only [CollatzResearch.WordTrace]
  refine ⟨50725768009459815052973455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67634357345946420070631273 50725768009459815052973455)
  ·
    refine ⟨76088652014189722579460183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50725768009459815052973455 76088652014189722579460183)
    ·
      refine ⟨114132978021284583869190275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76088652014189722579460183 114132978021284583869190275)
      ·
        refine ⟨171199467031926875803785413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114132978021284583869190275 171199467031926875803785413)
        ·
          refine ⟨32099900068486289213209765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171199467031926875803785413 32099900068486289213209765)
          ·
            refine ⟨6018731262841179227476831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32099900068486289213209765 6018731262841179227476831)
            ·
              refine ⟨9028096894261768841215247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6018731262841179227476831 9028096894261768841215247)
              ·
                refine ⟨13542145341392653261822871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9028096894261768841215247 13542145341392653261822871)
                ·
                  refine ⟨20313218012088979892734307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13542145341392653261822871 20313218012088979892734307)
                  ·
                    refine ⟨30469827018133469839101461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20313218012088979892734307 30469827018133469839101461)
                    ·
                      refine ⟨1428273141475006398707881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30469827018133469839101461 1428273141475006398707881)
                      ·
                        rfl

theorem cell23_2781552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_2781552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781552 prefixEnd_2781552 := by exact prefixLift 2781552
  have htrace : WordTrace (prefixWord ++ tailWord_2781552) baseStart_2781552 baseEnd_2781552 := by
    simpa [prefixWord, tailWord_2781552, baseEnd_2781552] using wordTrace_append hprefix tailTrace_2781552
  have hstable : (prefixWord ++ tailWord_2781552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781552).length < 2 ^ (prefixWord ++ tailWord_2781552).sum := by decide
  have hdescent : baseEnd_2781552 < baseStart_2781552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781555 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 7]
def baseStart_2781555 : Nat := 118140960795 + 2781555 * 2 ^ 59
def prefixEnd_2781555 : Nat := 4983230072969 + 3 ^ 40 * 2781555 * 2
def baseEnd_2781555 : Nat := 1428274681916969886970367

theorem tailTrace_2781555 : CollatzResearch.WordTrace tailWord_2781555 prefixEnd_2781555 1428274681916969886970367 := by
  unfold tailWord_2781555
  simp only [CollatzResearch.WordTrace]
  refine ⟨101451645437908761618306119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67634430291939174412204079 101451645437908761618306119)
  ·
    refine ⟨152177468156863142427459179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101451645437908761618306119 152177468156863142427459179)
    ·
      refine ⟨228266202235294713641188769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152177468156863142427459179 228266202235294713641188769)
      ·
        refine ⟨171199651676471035230891577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228266202235294713641188769 171199651676471035230891577)
        ·
          refine ⟨128399738757353276423168683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171199651676471035230891577 128399738757353276423168683)
          ·
            refine ⟨192599608136029914634753025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128399738757353276423168683 192599608136029914634753025)
            ·
              refine ⟨144449706102022435976064769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192599608136029914634753025 144449706102022435976064769)
              ·
                refine ⟨108337279576516826982048577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144449706102022435976064769 108337279576516826982048577)
                ·
                  refine ⟨81252959682387620236536433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108337279576516826982048577 81252959682387620236536433)
                  ·
                    refine ⟨60939719761790715177402325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81252959682387620236536433 60939719761790715177402325)
                    ·
                      refine ⟨1428274681916969886970367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60939719761790715177402325 1428274681916969886970367)
                      ·
                        rfl

theorem cell23_2781555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_2781555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781555 prefixEnd_2781555 := by exact prefixLift 2781555
  have htrace : WordTrace (prefixWord ++ tailWord_2781555) baseStart_2781555 baseEnd_2781555 := by
    simpa [prefixWord, tailWord_2781555, baseEnd_2781555] using wordTrace_append hprefix tailTrace_2781555
  have hstable : (prefixWord ++ tailWord_2781555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781555).length < 2 ^ (prefixWord ++ tailWord_2781555).sum := by decide
  have hdescent : baseEnd_2781555 < baseStart_2781555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781610 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2781610 : Nat := 118140960795 + 2781610 * 2 ^ 59
def prefixEnd_2781610 : Nat := 4983230072969 + 3 ^ 40 * 2781610 * 2
def baseEnd_2781610 : Nat := 1428302923352967171782615

theorem tailTrace_2781610 : CollatzResearch.WordTrace tailWord_2781610 prefixEnd_2781610 1428302923352967171782615 := by
  unfold tailWord_2781610
  simp only [CollatzResearch.WordTrace]
  refine ⟨25363412863177376502889571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67635767635139670674372189 25363412863177376502889571)
  ·
    refine ⟨38045119294766064754334357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25363412863177376502889571 38045119294766064754334357)
    ·
      refine ⟨1783364966942159285359423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38045119294766064754334357 1783364966942159285359423)
      ·
        refine ⟨2675047450413238928039135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1783364966942159285359423 2675047450413238928039135)
        ·
          refine ⟨4012571175619858392058703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2675047450413238928039135 4012571175619858392058703)
          ·
            refine ⟨6018856763429787588088055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4012571175619858392058703 6018856763429787588088055)
            ·
              refine ⟨9028285145144681382132083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6018856763429787588088055 9028285145144681382132083)
              ·
                refine ⟨13542427717717022073198125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9028285145144681382132083 13542427717717022073198125)
                ·
                  refine ⟨5078410394143883277449297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13542427717717022073198125 5078410394143883277449297)
                  ·
                    refine ⟨3808807795607912458086973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5078410394143883277449297 3808807795607912458086973)
                    ·
                      refine ⟨1428302923352967171782615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3808807795607912458086973 1428302923352967171782615)
                      ·
                        rfl

theorem cell23_2781610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2781610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781610 prefixEnd_2781610 := by exact prefixLift 2781610
  have htrace : WordTrace (prefixWord ++ tailWord_2781610) baseStart_2781610 baseEnd_2781610 := by
    simpa [prefixWord, tailWord_2781610, baseEnd_2781610] using wordTrace_append hprefix tailTrace_2781610
  have hstable : (prefixWord ++ tailWord_2781610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781610).length < 2 ^ (prefixWord ++ tailWord_2781610).sum := by decide
  have hdescent : baseEnd_2781610 < baseStart_2781610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781663 : List Nat := [1, 1, 2, 3, 3, 2, 2, 3, 2, 2, 2]
def baseStart_2781663 : Nat := 118140960795 + 2781663 * 2 ^ 59
def prefixEnd_2781663 : Nat := 4983230072969 + 3 ^ 40 * 2781663 * 2
def baseEnd_2781663 : Nat := 1428330137827655464419871

theorem tailTrace_2781663 : CollatzResearch.WordTrace tailWord_2781663 prefixEnd_2781663 1428330137827655464419871 := by
  unfold tailWord_2781663
  simp only [CollatzResearch.WordTrace]
  refine ⟨101455584521517496063237643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67637056347678330708825095 101455584521517496063237643)
  ·
    refine ⟨152183376782276244094856465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101455584521517496063237643 152183376782276244094856465)
    ·
      refine ⟨114137532586707183071142349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152183376782276244094856465 114137532586707183071142349)
      ·
        refine ⟨42801574720015193651678381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114137532586707183071142349 42801574720015193651678381)
        ·
          refine ⟨16050590520005697619379393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42801574720015193651678381 16050590520005697619379393)
          ·
            refine ⟨12037942890004273214534545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16050590520005697619379393 12037942890004273214534545)
            ·
              refine ⟨9028457167503204910900909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12037942890004273214534545 9028457167503204910900909)
              ·
                refine ⟨3385671437813701841587841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9028457167503204910900909 3385671437813701841587841)
                ·
                  refine ⟨2539253578360276381190881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3385671437813701841587841 2539253578360276381190881)
                  ·
                    refine ⟨1904440183770207285893161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2539253578360276381190881 1904440183770207285893161)
                    ·
                      refine ⟨1428330137827655464419871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1904440183770207285893161 1428330137827655464419871)
                      ·
                        rfl

theorem cell23_2781663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_2781663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781663 prefixEnd_2781663 := by exact prefixLift 2781663
  have htrace : WordTrace (prefixWord ++ tailWord_2781663) baseStart_2781663 baseEnd_2781663 := by
    simpa [prefixWord, tailWord_2781663, baseEnd_2781663] using wordTrace_append hprefix tailTrace_2781663
  have hstable : (prefixWord ++ tailWord_2781663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781663).length < 2 ^ (prefixWord ++ tailWord_2781663).sum := by decide
  have hdescent : baseEnd_2781663 < baseStart_2781663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781716 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2781716 : Nat := 118140960795 + 2781716 * 2 ^ 59
def prefixEnd_2781716 : Nat := 4983230072969 + 3 ^ 40 * 2781716 * 2
def baseEnd_2781716 : Nat := 476119117434114585685709

theorem tailTrace_2781716 : CollatzResearch.WordTrace tailWord_2781716 prefixEnd_2781716 476119117434114585685709 := by
  unfold tailWord_2781716
  simp only [CollatzResearch.WordTrace]
  refine ⟨50728758795162743057458501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67638345060216990743278001 50728758795162743057458501)
  ·
    refine ⟨9511642274093014323273469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50728758795162743057458501 9511642274093014323273469)
    ·
      refine ⟨3566865852784880371227551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9511642274093014323273469 3566865852784880371227551)
      ·
        refine ⟨5350298779177320556841327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3566865852784880371227551 5350298779177320556841327)
        ·
          refine ⟨8025448168765980835261991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5350298779177320556841327 8025448168765980835261991)
          ·
            refine ⟨12038172253148971252892987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8025448168765980835261991 12038172253148971252892987)
            ·
              refine ⟨18057258379723456879339481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12038172253148971252892987 18057258379723456879339481)
              ·
                refine ⟨13542943784792592659504611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18057258379723456879339481 13542943784792592659504611)
                ·
                  refine ⟨20314415677188888989256917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13542943784792592659504611 20314415677188888989256917)
                  ·
                    refine ⟨476119117434114585685709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20314415677188888989256917 476119117434114585685709)
                    ·
                      rfl

theorem cell23_2781716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2781716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781716 prefixEnd_2781716 := by exact prefixLift 2781716
  have htrace : WordTrace (prefixWord ++ tailWord_2781716) baseStart_2781716 baseEnd_2781716 := by
    simpa [prefixWord, tailWord_2781716, baseEnd_2781716] using wordTrace_append hprefix tailTrace_2781716
  have hstable : (prefixWord ++ tailWord_2781716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781716).length < 2 ^ (prefixWord ++ tailWord_2781716).sum := by decide
  have hdescent : baseEnd_2781716 < baseStart_2781716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781736 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2781736 : Nat := 118140960795 + 2781736 * 2 ^ 59
def prefixEnd_2781736 : Nat := 4983230072969 + 3 ^ 40 * 2781736 * 2
def baseEnd_2781736 : Nat := 1428367621915433678807035

theorem tailTrace_2781736 : CollatzResearch.WordTrace tailWord_2781736 prefixEnd_2781736 1428367621915433678807035 := by
  unfold tailWord_2781736
  simp only [CollatzResearch.WordTrace]
  refine ⟨50729123525126514765322531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67638831366835353020430041 50729123525126514765322531)
  ·
    refine ⟨76093685287689772147983797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50729123525126514765322531 76093685287689772147983797)
    ·
      refine ⟨7133782995720916138873481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76093685287689772147983797 7133782995720916138873481)
      ·
        refine ⟨5350337246790687104155111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7133782995720916138873481 5350337246790687104155111)
        ·
          refine ⟨8025505870186030656232667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5350337246790687104155111 8025505870186030656232667)
          ·
            refine ⟨12038258805279045984349001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8025505870186030656232667 12038258805279045984349001)
            ·
              refine ⟨9028694103959284488261751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12038258805279045984349001 9028694103959284488261751)
              ·
                refine ⟨13543041155938926732392627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9028694103959284488261751 13543041155938926732392627)
                ·
                  refine ⟨20314561733908390098588941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13543041155938926732392627 20314561733908390098588941)
                  ·
                    refine ⟨7617960650215646286970853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20314561733908390098588941 7617960650215646286970853)
                    ·
                      refine ⟨1428367621915433678807035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7617960650215646286970853 1428367621915433678807035)
                      ·
                        rfl

theorem cell23_2781736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2781736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781736 prefixEnd_2781736 := by exact prefixLift 2781736
  have htrace : WordTrace (prefixWord ++ tailWord_2781736) baseStart_2781736 baseEnd_2781736 := by
    simpa [prefixWord, tailWord_2781736, baseEnd_2781736] using wordTrace_append hprefix tailTrace_2781736
  have hstable : (prefixWord ++ tailWord_2781736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781736).length < 2 ^ (prefixWord ++ tailWord_2781736).sum := by decide
  have hdescent : baseEnd_2781736 < baseStart_2781736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781739 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 3]
def baseStart_2781739 : Nat := 118140960795 + 2781739 * 2 ^ 59
def prefixEnd_2781739 : Nat := 4983230072969 + 3 ^ 40 * 2781739 * 2
def baseEnd_2781739 : Nat := 1428369162357397167069521

theorem tailTrace_2781739 : CollatzResearch.WordTrace tailWord_2781739 prefixEnd_2781739 1428369162357397167069521 := by
  unfold tailWord_2781739
  simp only [CollatzResearch.WordTrace]
  refine ⟨101458356469242161043004271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67638904312828107362002847 101458356469242161043004271)
  ·
    refine ⟨152187534703863241564506407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101458356469242161043004271 152187534703863241564506407)
    ·
      refine ⟨228281302055794862346759611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152187534703863241564506407 228281302055794862346759611)
      ·
        refine ⟨342421953083692293520139417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228281302055794862346759611 342421953083692293520139417)
        ·
          refine ⟨256816464812769220140104563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342421953083692293520139417 256816464812769220140104563)
          ·
            refine ⟨385224697219153830210156845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256816464812769220140104563 385224697219153830210156845)
            ·
              refine ⟨144459261457182686328808817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 385224697219153830210156845 144459261457182686328808817)
              ·
                refine ⟨108344446092887014746606613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144459261457182686328808817 108344446092887014746606613)
                ·
                  refine ⟨5078645910604078816247185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108344446092887014746606613 5078645910604078816247185)
                  ·
                    refine ⟨3808984432953059112185389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5078645910604078816247185 3808984432953059112185389)
                    ·
                      refine ⟨1428369162357397167069521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3808984432953059112185389 1428369162357397167069521)
                      ·
                        rfl

theorem cell23_2781739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 3].length) (baseStart_2781739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781739 prefixEnd_2781739 := by exact prefixLift 2781739
  have htrace : WordTrace (prefixWord ++ tailWord_2781739) baseStart_2781739 baseEnd_2781739 := by
    simpa [prefixWord, tailWord_2781739, baseEnd_2781739] using wordTrace_append hprefix tailTrace_2781739
  have hstable : (prefixWord ++ tailWord_2781739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781739).length < 2 ^ (prefixWord ++ tailWord_2781739).sum := by decide
  have hdescent : baseEnd_2781739 < baseStart_2781739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781756 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 4, 2, 3]
def baseStart_2781756 : Nat := 118140960795 + 2781756 * 2 ^ 59
def prefixEnd_2781756 : Nat := 4983230072969 + 3 ^ 40 * 2781756 * 2
def baseEnd_2781756 : Nat := 1428377891528523600556943

theorem tailTrace_2781756 : CollatzResearch.WordTrace tailWord_2781756 prefixEnd_2781756 1428377891528523600556943 := by
  unfold tailWord_2781756
  simp only [CollatzResearch.WordTrace]
  refine ⟨50729488255090286473186561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67639317673453715297582081 50729488255090286473186561)
  ·
    refine ⟨38047116191317714854889921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50729488255090286473186561 38047116191317714854889921)
    ·
      refine ⟨28535337143488286141167441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38047116191317714854889921 28535337143488286141167441)
      ·
        refine ⟨21401502857616214605875581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28535337143488286141167441 21401502857616214605875581)
        ·
          refine ⟨8025563571606080477203343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21401502857616214605875581 8025563571606080477203343)
          ·
            refine ⟨12038345357409120715805015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8025563571606080477203343 12038345357409120715805015)
            ·
              refine ⟨18057518036113681073707523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12038345357409120715805015 18057518036113681073707523)
              ·
                refine ⟨27086277054170521610561285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18057518036113681073707523 27086277054170521610561285)
                ·
                  refine ⟨5078676947656972801980241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27086277054170521610561285 5078676947656972801980241)
                  ·
                    refine ⟨3809007710742729601485181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5078676947656972801980241 3809007710742729601485181)
                    ·
                      refine ⟨1428377891528523600556943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3809007710742729601485181 1428377891528523600556943)
                      ·
                        rfl

theorem cell23_2781756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_2781756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781756 prefixEnd_2781756 := by exact prefixLift 2781756
  have htrace : WordTrace (prefixWord ++ tailWord_2781756) baseStart_2781756 baseEnd_2781756 := by
    simpa [prefixWord, tailWord_2781756, baseEnd_2781756] using wordTrace_append hprefix tailTrace_2781756
  have hstable : (prefixWord ++ tailWord_2781756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781756).length < 2 ^ (prefixWord ++ tailWord_2781756).sum := by decide
  have hdescent : baseEnd_2781756 < baseStart_2781756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781759 : List Nat := [1, 1, 2, 2, 3, 2, 2, 4, 6]
def baseStart_2781759 : Nat := 118140960795 + 2781759 * 2 ^ 59
def prefixEnd_2781759 : Nat := 4983230072969 + 3 ^ 40 * 2781759 * 2
def baseEnd_2781759 : Nat := 158708825774498565424381

theorem tailTrace_2781759 : CollatzResearch.WordTrace tailWord_2781759 prefixEnd_2781759 158708825774498565424381 := by
  unfold tailWord_2781759
  simp only [CollatzResearch.WordTrace]
  refine ⟨101459085929169704458732331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67639390619446469639154887 101459085929169704458732331)
  ·
    refine ⟨152188628893754556688098497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101459085929169704458732331 152188628893754556688098497)
    ·
      refine ⟨114141471670315917516073873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152188628893754556688098497 114141471670315917516073873)
      ·
        refine ⟨85606103752736938137055405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114141471670315917516073873 85606103752736938137055405)
        ·
          refine ⟨32102288907276351801395777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85606103752736938137055405 32102288907276351801395777)
          ·
            refine ⟨24076716680457263851046833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32102288907276351801395777 24076716680457263851046833)
            ·
              refine ⟨18057537510342947888285125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24076716680457263851046833 18057537510342947888285125)
              ·
                refine ⟨3385788283189302729053461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18057537510342947888285125 3385788283189302729053461)
                ·
                  refine ⟨158708825774498565424381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3385788283189302729053461 158708825774498565424381)
                  ·
                    rfl

theorem cell23_2781759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 6].length) (baseStart_2781759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781759 prefixEnd_2781759 := by exact prefixLift 2781759
  have htrace : WordTrace (prefixWord ++ tailWord_2781759) baseStart_2781759 baseEnd_2781759 := by
    simpa [prefixWord, tailWord_2781759, baseEnd_2781759] using wordTrace_append hprefix tailTrace_2781759
  have hstable : (prefixWord ++ tailWord_2781759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781759).length < 2 ^ (prefixWord ++ tailWord_2781759).sum := by decide
  have hdescent : baseEnd_2781759 < baseStart_2781759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781814 : List Nat := [5, 1, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_2781814 : Nat := 118140960795 + 2781814 * 2 ^ 59
def prefixEnd_2781814 : Nat := 4983230072969 + 3 ^ 40 * 2781814 * 2
def baseEnd_2781814 : Nat := 476135891135494791210559

theorem tailTrace_2781814 : CollatzResearch.WordTrace tailWord_2781814 prefixEnd_2781814 476135891135494791210559 := by
  unfold tailWord_2781814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6341318246498153053249031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67640727962646965901322997 6341318246498153053249031)
  ·
    refine ⟨9511977369747229579873547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6341318246498153053249031 9511977369747229579873547)
    ·
      refine ⟨14267966054620844369810321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9511977369747229579873547 14267966054620844369810321)
      ·
        refine ⟨10700974540965633277357741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14267966054620844369810321 10700974540965633277357741)
        ·
          refine ⟨4012865452862112479009153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10700974540965633277357741 4012865452862112479009153)
          ·
            refine ⟨3009649089646584359256865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4012865452862112479009153 3009649089646584359256865)
            ·
              refine ⟨2257236817234938269442649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3009649089646584359256865 2257236817234938269442649)
              ·
                refine ⟨1692927612926203702081987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2257236817234938269442649 1692927612926203702081987)
                ·
                  refine ⟨2539391419389305553122981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692927612926203702081987 2539391419389305553122981)
                  ·
                    refine ⟨476135891135494791210559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2539391419389305553122981 476135891135494791210559)
                    ·
                      rfl

theorem cell23_2781814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_2781814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781814 prefixEnd_2781814 := by exact prefixLift 2781814
  have htrace : WordTrace (prefixWord ++ tailWord_2781814) baseStart_2781814 baseEnd_2781814 := by
    simpa [prefixWord, tailWord_2781814, baseEnd_2781814] using wordTrace_append hprefix tailTrace_2781814
  have hstable : (prefixWord ++ tailWord_2781814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781814).length < 2 ^ (prefixWord ++ tailWord_2781814).sum := by decide
  have hdescent : baseEnd_2781814 < baseStart_2781814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781839 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 4]
def baseStart_2781839 : Nat := 118140960795 + 2781839 * 2 ^ 59
def prefixEnd_2781839 : Nat := 4983230072969 + 3 ^ 40 * 2781839 * 2
def baseEnd_2781839 : Nat := 1428420510422846775819061

theorem tailTrace_2781839 : CollatzResearch.WordTrace tailWord_2781839 prefixEnd_2781839 1428420510422846775819061 := by
  unfold tailWord_2781839
  simp only [CollatzResearch.WordTrace]
  refine ⟨101462003768879878121644571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67641335845919918747763047 101462003768879878121644571)
  ·
    refine ⟨152193005653319817182466857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101462003768879878121644571 152193005653319817182466857)
    ·
      refine ⟨114144754239989862886850143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152193005653319817182466857 114144754239989862886850143)
      ·
        refine ⟨171217131359984794330275215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114144754239989862886850143 171217131359984794330275215)
        ·
          refine ⟨256825697039977191495412823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171217131359984794330275215 256825697039977191495412823)
          ·
            refine ⟨385238545559965787243119235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256825697039977191495412823 385238545559965787243119235)
            ·
              refine ⟨577857818339948680864678853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385238545559965787243119235 577857818339948680864678853)
              ·
                refine ⟨108348340938740377662127285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 577857818339948680864678853 108348340938740377662127285)
                ·
                  refine ⟨10157656963006910405824433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108348340938740377662127285 10157656963006910405824433)
                  ·
                    refine ⟨7618242722255182804368325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10157656963006910405824433 7618242722255182804368325)
                    ·
                      refine ⟨1428420510422846775819061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7618242722255182804368325 1428420510422846775819061)
                      ·
                        rfl

theorem cell23_2781839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_2781839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781839 prefixEnd_2781839 := by exact prefixLift 2781839
  have htrace : WordTrace (prefixWord ++ tailWord_2781839) baseStart_2781839 baseEnd_2781839 := by
    simpa [prefixWord, tailWord_2781839, baseEnd_2781839] using wordTrace_append hprefix tailTrace_2781839
  have hstable : (prefixWord ++ tailWord_2781839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781839).length < 2 ^ (prefixWord ++ tailWord_2781839).sum := by decide
  have hdescent : baseEnd_2781839 < baseStart_2781839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781843 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 3, 2, 2]
def baseStart_2781843 : Nat := 118140960795 + 2781843 * 2 ^ 59
def prefixEnd_2781843 : Nat := 4983230072969 + 3 ^ 40 * 2781843 * 2
def baseEnd_2781843 : Nat := 1428422564345464760169043

theorem tailTrace_2781843 : CollatzResearch.WordTrace tailWord_2781843 prefixEnd_2781843 1428422564345464760169043 := by
  unfold tailWord_2781843
  simp only [CollatzResearch.WordTrace]
  refine ⟨101462149660865386804790183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67641433107243591203193455 101462149660865386804790183)
  ·
    refine ⟨152193224491298080207185275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101462149660865386804790183 152193224491298080207185275)
    ·
      refine ⟨228289836736947120310777913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152193224491298080207185275 228289836736947120310777913)
      ·
        refine ⟨171217377552710340233083435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228289836736947120310777913 171217377552710340233083435)
        ·
          refine ⟨256826066329065510349625153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171217377552710340233083435 256826066329065510349625153)
          ·
            refine ⟨192619549746799132762218865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256826066329065510349625153 192619549746799132762218865)
            ·
              refine ⟨144464662310099349571664149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192619549746799132762218865 144464662310099349571664149)
              ·
                refine ⟨6771781045785907011171757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 144464662310099349571664149 6771781045785907011171757)
                ·
                  refine ⟨2539417892169715129189409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6771781045785907011171757 2539417892169715129189409)
                  ·
                    refine ⟨1904563419127286346892057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2539417892169715129189409 1904563419127286346892057)
                    ·
                      refine ⟨1428422564345464760169043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1904563419127286346892057 1428422564345464760169043)
                      ·
                        rfl

theorem cell23_2781843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 2, 2].length) (baseStart_2781843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781843 prefixEnd_2781843 := by exact prefixLift 2781843
  have htrace : WordTrace (prefixWord ++ tailWord_2781843) baseStart_2781843 baseEnd_2781843 := by
    simpa [prefixWord, tailWord_2781843, baseEnd_2781843] using wordTrace_append hprefix tailTrace_2781843
  have hstable : (prefixWord ++ tailWord_2781843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781843).length < 2 ^ (prefixWord ++ tailWord_2781843).sum := by decide
  have hdescent : baseEnd_2781843 < baseStart_2781843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781857 : List Nat := [1, 2, 3, 3, 4, 1, 2, 1, 1, 5]
def baseStart_2781857 : Nat := 118140960795 + 2781857 * 2 ^ 59
def prefixEnd_2781857 : Nat := 4983230072969 + 3 ^ 40 * 2781857 * 2
def baseEnd_2781857 : Nat := 476143251024875901797993

theorem tailTrace_2781857 : CollatzResearch.WordTrace tailWord_2781857 prefixEnd_2781857 476143251024875901797993 := by
  unfold tailWord_2781857
  simp only [CollatzResearch.WordTrace]
  refine ⟨101462660282814667195799825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67641773521876444797199883 101462660282814667195799825)
  ·
    refine ⟨76096995212111000396849869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101462660282814667195799825 76096995212111000396849869)
    ·
      refine ⟨28536373204541625148818701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76096995212111000396849869 28536373204541625148818701)
      ·
        refine ⟨10701139951703109430807013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28536373204541625148818701 10701139951703109430807013)
        ·
          refine ⟨2006463740944333018276315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10701139951703109430807013 2006463740944333018276315)
          ·
            refine ⟨3009695611416499527414473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006463740944333018276315 3009695611416499527414473)
            ·
              refine ⟨2257271708562374645560855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3009695611416499527414473 2257271708562374645560855)
              ·
                refine ⟨3385907562843561968341283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2257271708562374645560855 3385907562843561968341283)
                ·
                  refine ⟨5078861344265342952511925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3385907562843561968341283 5078861344265342952511925)
                  ·
                    refine ⟨476143251024875901797993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5078861344265342952511925 476143251024875901797993)
                    ·
                      rfl

theorem cell23_2781857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_2781857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781857 prefixEnd_2781857 := by exact prefixLift 2781857
  have htrace : WordTrace (prefixWord ++ tailWord_2781857) baseStart_2781857 baseEnd_2781857 := by
    simpa [prefixWord, tailWord_2781857, baseEnd_2781857] using wordTrace_append hprefix tailTrace_2781857
  have hstable : (prefixWord ++ tailWord_2781857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781857).length < 2 ^ (prefixWord ++ tailWord_2781857).sum := by decide
  have hdescent : baseEnd_2781857 < baseStart_2781857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781870 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2781870 : Nat := 118140960795 + 2781870 * 2 ^ 59
def prefixEnd_2781870 : Nat := 4983230072969 + 3 ^ 40 * 2781870 * 2
def baseEnd_2781870 : Nat := 476145476107712051510473

theorem tailTrace_2781870 : CollatzResearch.WordTrace tailWord_2781870 prefixEnd_2781870 476145476107712051510473 := by
  unfold tailWord_2781870
  simp only [CollatzResearch.WordTrace]
  refine ⟨12682891803970946302002883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67642089621178380277348709 12682891803970946302002883)
  ·
    refine ⟨19024337705956419453004325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12682891803970946302002883 19024337705956419453004325)
    ·
      refine ⟨3567063319866828647438311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19024337705956419453004325 3567063319866828647438311)
      ·
        refine ⟨5350594979800242971157467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3567063319866828647438311 5350594979800242971157467)
        ·
          refine ⟨8025892469700364456736201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5350594979800242971157467 8025892469700364456736201)
          ·
            refine ⟨6019419352275273342552151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8025892469700364456736201 6019419352275273342552151)
            ·
              refine ⟨9029129028412910013828227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6019419352275273342552151 9029129028412910013828227)
              ·
                refine ⟨13543693542619365020742341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9029129028412910013828227 13543693542619365020742341)
                ·
                  refine ⟨2539442539241130941389189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13543693542619365020742341 2539442539241130941389189)
                  ·
                    refine ⟨476145476107712051510473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2539442539241130941389189 476145476107712051510473)
                    ·
                      rfl

theorem cell23_2781870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2781870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781870 prefixEnd_2781870 := by exact prefixLift 2781870
  have htrace : WordTrace (prefixWord ++ tailWord_2781870) baseStart_2781870 baseEnd_2781870 := by
    simpa [prefixWord, tailWord_2781870, baseEnd_2781870] using wordTrace_append hprefix tailTrace_2781870
  have hstable : (prefixWord ++ tailWord_2781870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781870).length < 2 ^ (prefixWord ++ tailWord_2781870).sum := by decide
  have hdescent : baseEnd_2781870 < baseStart_2781870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781877 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 3, 2, 2]
def baseStart_2781877 : Nat := 118140960795 + 2781877 * 2 ^ 59
def prefixEnd_2781877 : Nat := 4983230072969 + 3 ^ 40 * 2781877 * 2
def baseEnd_2781877 : Nat := 1428440022687717627143887

theorem tailTrace_2781877 : CollatzResearch.WordTrace tailWord_2781877 prefixEnd_2781877 1428440022687717627143887 := by
  unfold tailWord_2781877
  simp only [CollatzResearch.WordTrace]
  refine ⟨101463389742742210611527885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67642259828494807074351923 101463389742742210611527885)
  ·
    refine ⟨38048771153528328979322957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101463389742742210611527885 38048771153528328979322957)
    ·
      refine ⟨14268289182573123367246109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38048771153528328979322957 14268289182573123367246109)
      ·
        refine ⟨5350608443464921262717291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14268289182573123367246109 5350608443464921262717291)
        ·
          refine ⟨8025912665197381894075937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5350608443464921262717291 8025912665197381894075937)
          ·
            refine ⟨6019434498898036420556953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8025912665197381894075937 6019434498898036420556953)
            ·
              refine ⟨4514575874173527315417715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6019434498898036420556953 4514575874173527315417715)
              ·
                refine ⟨6771863811260290973126573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4514575874173527315417715 6771863811260290973126573)
                ·
                  refine ⟨2539448929222609114922465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6771863811260290973126573 2539448929222609114922465)
                  ·
                    refine ⟨1904586696916956836191849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2539448929222609114922465 1904586696916956836191849)
                    ·
                      refine ⟨1428440022687717627143887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1904586696916956836191849 1428440022687717627143887)
                      ·
                        rfl

theorem cell23_2781877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_2781877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781877 prefixEnd_2781877 := by exact prefixLift 2781877
  have htrace : WordTrace (prefixWord ++ tailWord_2781877) baseStart_2781877 baseEnd_2781877 := by
    simpa [prefixWord, tailWord_2781877, baseEnd_2781877] using wordTrace_append hprefix tailTrace_2781877
  have hstable : (prefixWord ++ tailWord_2781877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781877).length < 2 ^ (prefixWord ++ tailWord_2781877).sum := by decide
  have hdescent : baseEnd_2781877 < baseStart_2781877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781894 : List Nat := [6, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_2781894 : Nat := 118140960795 + 2781894 * 2 ^ 59
def prefixEnd_2781894 : Nat := 4983230072969 + 3 ^ 40 * 2781894 * 2
def baseEnd_2781894 : Nat := 1428448751858844060631309

theorem tailTrace_2781894 : CollatzResearch.WordTrace tailWord_2781894 prefixEnd_2781894 1428448751858844060631309 := by
  unfold tailWord_2781894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3170750305740019453590523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67642673189120415009931157 3170750305740019453590523)
  ·
    refine ⟨4756125458610029180385785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3170750305740019453590523 4756125458610029180385785)
    ·
      refine ⟨3567094093957521885289339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4756125458610029180385785 3567094093957521885289339)
      ·
        refine ⟨5350641140936282827934009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3567094093957521885289339 5350641140936282827934009)
        ·
          refine ⟨4012980855702212120950507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5350641140936282827934009 4012980855702212120950507)
          ·
            refine ⟨6019471283553318181425761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4012980855702212120950507 6019471283553318181425761)
            ·
              refine ⟨4514603462664988636069321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6019471283553318181425761 4514603462664988636069321)
              ·
                refine ⟨3385952596998741477051991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4514603462664988636069321 3385952596998741477051991)
                ·
                  refine ⟨5078928895498112215577987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3385952596998741477051991 5078928895498112215577987)
                  ·
                    refine ⟨7618393343247168323366981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5078928895498112215577987 7618393343247168323366981)
                    ·
                      refine ⟨1428448751858844060631309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7618393343247168323366981 1428448751858844060631309)
                      ·
                        rfl

theorem cell23_2781894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_2781894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781894 prefixEnd_2781894 := by exact prefixLift 2781894
  have htrace : WordTrace (prefixWord ++ tailWord_2781894) baseStart_2781894 baseEnd_2781894 := by
    simpa [prefixWord, tailWord_2781894, baseEnd_2781894] using wordTrace_append hprefix tailTrace_2781894
  have hstable : (prefixWord ++ tailWord_2781894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781894).length < 2 ^ (prefixWord ++ tailWord_2781894).sum := by decide
  have hdescent : baseEnd_2781894 < baseStart_2781894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781936 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 3]
def baseStart_2781936 : Nat := 118140960795 + 2781936 * 2 ^ 59
def prefixEnd_2781936 : Nat := 4983230072969 + 3 ^ 40 * 2781936 * 2
def baseEnd_2781936 : Nat := 1428470318046332896306115

theorem tailTrace_2781936 : CollatzResearch.WordTrace tailWord_2781936 prefixEnd_2781936 1428470318046332896306115 := by
  unfold tailWord_2781936
  simp only [CollatzResearch.WordTrace]
  refine ⟨50732770824764231843962831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67643694433018975791950441 50732770824764231843962831)
  ·
    refine ⟨76099156237146347765944247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50732770824764231843962831 76099156237146347765944247)
    ·
      refine ⟨114148734355719521648916371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76099156237146347765944247 114148734355719521648916371)
      ·
        refine ⟨171223101533579282473374557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114148734355719521648916371 171223101533579282473374557)
        ·
          refine ⟨64208663075092230927515459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171223101533579282473374557 64208663075092230927515459)
          ·
            refine ⟨96312994612638346391273189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64208663075092230927515459 96312994612638346391273189)
            ·
              refine ⟨18058686489869689948363723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96312994612638346391273189 18058686489869689948363723)
              ·
                refine ⟨27088029734804534922545585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18058686489869689948363723 27088029734804534922545585)
                ·
                  refine ⟨20316022301103401191909189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27088029734804534922545585 20316022301103401191909189)
                  ·
                    refine ⟨3809254181456887723482973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20316022301103401191909189 3809254181456887723482973)
                    ·
                      refine ⟨1428470318046332896306115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3809254181456887723482973 1428470318046332896306115)
                      ·
                        rfl

theorem cell23_2781936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 3].length) (baseStart_2781936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781936 prefixEnd_2781936 := by exact prefixLift 2781936
  have htrace : WordTrace (prefixWord ++ tailWord_2781936) baseStart_2781936 baseEnd_2781936 := by
    simpa [prefixWord, tailWord_2781936, baseEnd_2781936] using wordTrace_append hprefix tailTrace_2781936
  have hstable : (prefixWord ++ tailWord_2781936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781936).length < 2 ^ (prefixWord ++ tailWord_2781936).sum := by decide
  have hdescent : baseEnd_2781936 < baseStart_2781936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781946 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4]
def baseStart_2781946 : Nat := 118140960795 + 2781946 * 2 ^ 59
def prefixEnd_2781946 : Nat := 4983230072969 + 3 ^ 40 * 2781946 * 2
def baseEnd_2781946 : Nat := 1428475452852877857181069

theorem tailTrace_2781946 : CollatzResearch.WordTrace tailWord_2781946 prefixEnd_2781946 1428475452852877857181069 := by
  unfold tailWord_2781946
  simp only [CollatzResearch.WordTrace]
  refine ⟨25366476594873058848947423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67643937586328156930526461 25366476594873058848947423)
  ·
    refine ⟨38049714892309588273421135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25366476594873058848947423 38049714892309588273421135)
    ·
      refine ⟨57074572338464382410131703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38049714892309588273421135 57074572338464382410131703)
      ·
        refine ⟨85611858507696573615197555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57074572338464382410131703 85611858507696573615197555)
        ·
          refine ⟨128417787761544860422796333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85611858507696573615197555 128417787761544860422796333)
          ·
            refine ⟨48156670410579322658548625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128417787761544860422796333 48156670410579322658548625)
            ·
              refine ⟨36117502807934491993911469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48156670410579322658548625 36117502807934491993911469)
              ·
                refine ⟨13544063552975434497716801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36117502807934491993911469 13544063552975434497716801)
                ·
                  refine ⟨10158047664731575873287601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13544063552975434497716801 10158047664731575873287601)
                  ·
                    refine ⟨7618535748548681904965701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10158047664731575873287601 7618535748548681904965701)
                    ·
                      refine ⟨1428475452852877857181069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7618535748548681904965701 1428475452852877857181069)
                      ·
                        rfl

theorem cell23_2781946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_2781946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781946 prefixEnd_2781946 := by exact prefixLift 2781946
  have htrace : WordTrace (prefixWord ++ tailWord_2781946) baseStart_2781946 baseEnd_2781946 := by
    simpa [prefixWord, tailWord_2781946, baseEnd_2781946] using wordTrace_append hprefix tailTrace_2781946
  have hstable : (prefixWord ++ tailWord_2781946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781946).length < 2 ^ (prefixWord ++ tailWord_2781946).sum := by decide
  have hdescent : baseEnd_2781946 < baseStart_2781946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781954 : List Nat := [3, 4, 1, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_2781954 : Nat := 118140960795 + 2781954 * 2 ^ 59
def prefixEnd_2781954 : Nat := 4983230072969 + 3 ^ 40 * 2781954 * 2
def baseEnd_2781954 : Nat := 1428479560698113825881033

theorem tailTrace_2781954 : CollatzResearch.WordTrace tailWord_2781954 prefixEnd_2781954 1428479560698113825881033 := by
  unfold tailWord_2781954
  simp only [CollatzResearch.WordTrace]
  refine ⟨25366549540865813190520229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67644132108975501841387277 25366549540865813190520229)
  ·
    refine ⟨4756228038912339973222543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25366549540865813190520229 4756228038912339973222543)
    ·
      refine ⟨7134342058368509959833815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4756228038912339973222543 7134342058368509959833815)
      ·
        refine ⟨10701513087552764939750723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7134342058368509959833815 10701513087552764939750723)
        ·
          refine ⟨16052269631329147409626085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10701513087552764939750723 16052269631329147409626085)
          ·
            refine ⟨3009800555874215139304891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16052269631329147409626085 3009800555874215139304891)
            ·
              refine ⟨4514700833811322708957337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3009800555874215139304891 4514700833811322708957337)
              ·
                refine ⟨3386025625358492031718003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4514700833811322708957337 3386025625358492031718003)
                ·
                  refine ⟨5079038438037738047577005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3386025625358492031718003 5079038438037738047577005)
                  ·
                    refine ⟨1904639414264151767841377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5079038438037738047577005 1904639414264151767841377)
                    ·
                      refine ⟨1428479560698113825881033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1904639414264151767841377 1428479560698113825881033)
                      ·
                        rfl

theorem cell23_2781954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_2781954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781954 prefixEnd_2781954 := by exact prefixLift 2781954
  have htrace : WordTrace (prefixWord ++ tailWord_2781954) baseStart_2781954 baseEnd_2781954 := by
    simpa [prefixWord, tailWord_2781954, baseEnd_2781954] using wordTrace_append hprefix tailTrace_2781954
  have hstable : (prefixWord ++ tailWord_2781954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781954).length < 2 ^ (prefixWord ++ tailWord_2781954).sum := by decide
  have hdescent : baseEnd_2781954 < baseStart_2781954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781956 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 9]
def baseStart_2781956 : Nat := 118140960795 + 2781956 * 2 ^ 59
def prefixEnd_2781956 : Nat := 4983230072969 + 3 ^ 40 * 2781956 * 2
def baseEnd_2781956 : Nat := 158720065295491424228447

theorem tailTrace_2781956 : CollatzResearch.WordTrace tailWord_2781956 prefixEnd_2781956 158720065295491424228447 := by
  unfold tailWord_2781956
  simp only [CollatzResearch.WordTrace]
  refine ⟨50733135554728003551826861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67644180739637338069102481 50733135554728003551826861)
  ·
    refine ⟨19024925833023001331935073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50733135554728003551826861 19024925833023001331935073)
    ·
      refine ⟨14268694374767250998951305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19024925833023001331935073 14268694374767250998951305)
      ·
        refine ⟨10701520781075438249213479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14268694374767250998951305 10701520781075438249213479)
        ·
          refine ⟨16052281171613157373820219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10701520781075438249213479 16052281171613157373820219)
          ·
            refine ⟨24078421757419736060730329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16052281171613157373820219 24078421757419736060730329)
            ·
              refine ⟨18058816318064802045547747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24078421757419736060730329 18058816318064802045547747)
              ·
                refine ⟨27088224477097203068321621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18058816318064802045547747 27088224477097203068321621)
                ·
                  refine ⟨158720065295491424228447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27088224477097203068321621 158720065295491424228447)
                  ·
                    rfl

theorem cell23_2781956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_2781956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781956 prefixEnd_2781956 := by exact prefixLift 2781956
  have htrace : WordTrace (prefixWord ++ tailWord_2781956) baseStart_2781956 baseEnd_2781956 := by
    simpa [prefixWord, tailWord_2781956, baseEnd_2781956] using wordTrace_append hprefix tailTrace_2781956
  have hstable : (prefixWord ++ tailWord_2781956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781956).length < 2 ^ (prefixWord ++ tailWord_2781956).sum := by decide
  have hdescent : baseEnd_2781956 < baseStart_2781956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781973 : List Nat := [1, 3, 2, 1, 2, 2, 2, 5, 5]
def baseStart_2781973 : Nat := 118140960795 + 2781973 * 2 ^ 59
def prefixEnd_2781973 : Nat := 4983230072969 + 3 ^ 40 * 2781973 * 2
def baseEnd_2781973 : Nat := 158721035203394361282605

theorem tailTrace_2781973 : CollatzResearch.WordTrace tailWord_2781973 prefixEnd_2781973 158721035203394361282605 := by
  unfold tailWord_2781973
  simp only [CollatzResearch.WordTrace]
  refine ⟨101466891150394419007022573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67644594100262946004681715 101466891150394419007022573)
  ·
    refine ⟨38050084181397907127633465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101466891150394419007022573 38050084181397907127633465)
    ·
      refine ⟨28537563136048430345725099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38050084181397907127633465 28537563136048430345725099)
      ·
        refine ⟨42806344704072645518587649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28537563136048430345725099 42806344704072645518587649)
        ·
          refine ⟨32104758528054484138940737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42806344704072645518587649 32104758528054484138940737)
          ·
            refine ⟨24078568896040863104205553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32104758528054484138940737 24078568896040863104205553)
            ·
              refine ⟨18058926672030647328154165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24078568896040863104205553 18058926672030647328154165)
              ·
                refine ⟨1693024375502873187014453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18058926672030647328154165 1693024375502873187014453)
                ·
                  refine ⟨158721035203394361282605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1693024375502873187014453 158721035203394361282605)
                  ·
                    rfl

theorem cell23_2781973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 5].length) (baseStart_2781973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781973 prefixEnd_2781973 := by exact prefixLift 2781973
  have htrace : WordTrace (prefixWord ++ tailWord_2781973) baseStart_2781973 baseEnd_2781973 := by
    simpa [prefixWord, tailWord_2781973, baseEnd_2781973] using wordTrace_append hprefix tailTrace_2781973
  have hstable : (prefixWord ++ tailWord_2781973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781973).length < 2 ^ (prefixWord ++ tailWord_2781973).sum := by decide
  have hdescent : baseEnd_2781973 < baseStart_2781973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781996 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 5]
def baseStart_2781996 : Nat := 118140960795 + 2781996 * 2 ^ 59
def prefixEnd_2781996 : Nat := 4983230072969 + 3 ^ 40 * 2781996 * 2
def baseEnd_2781996 : Nat := 1428501126885602661555839

theorem tailTrace_2781996 : CollatzResearch.WordTrace tailWord_2781996 prefixEnd_2781996 1428501126885602661555839 := by
  unfold tailWord_2781996
  simp only [CollatzResearch.WordTrace]
  refine ⟨50733865014655546967554921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67645153352874062623406561 50733865014655546967554921)
  ·
    refine ⟨38050398760991660225666191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50733865014655546967554921 38050398760991660225666191)
    ·
      refine ⟨57075598141487490338499287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38050398760991660225666191 57075598141487490338499287)
      ·
        refine ⟨85613397212231235507748931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57075598141487490338499287 85613397212231235507748931)
        ·
          refine ⟨128420095818346853261623397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85613397212231235507748931 128420095818346853261623397)
          ·
            refine ⟨24078767965940034986554387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128420095818346853261623397 24078767965940034986554387)
            ·
              refine ⟨36118151948910052479831581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24078767965940034986554387 36118151948910052479831581)
              ·
                refine ⟨13544306980841269679936843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36118151948910052479831581 13544306980841269679936843)
                ·
                  refine ⟨20316460471261904519905265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13544306980841269679936843 20316460471261904519905265)
                  ·
                    refine ⟨15237345353446428389928949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20316460471261904519905265 15237345353446428389928949)
                    ·
                      refine ⟨1428501126885602661555839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15237345353446428389928949 1428501126885602661555839)
                      ·
                        rfl

theorem cell23_2781996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_2781996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781996 prefixEnd_2781996 := by exact prefixLift 2781996
  have htrace : WordTrace (prefixWord ++ tailWord_2781996) baseStart_2781996 baseEnd_2781996 := by
    simpa [prefixWord, tailWord_2781996, baseEnd_2781996] using wordTrace_append hprefix tailTrace_2781996
  have hstable : (prefixWord ++ tailWord_2781996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781996).length < 2 ^ (prefixWord ++ tailWord_2781996).sum := by decide
  have hdescent : baseEnd_2781996 < baseStart_2781996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781997 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_2781997 : Nat := 118140960795 + 2781997 * 2 ^ 59
def prefixEnd_2781997 : Nat := 4983230072969 + 3 ^ 40 * 2781997 * 2
def baseEnd_2781997 : Nat := 1428501640366257157643335

theorem tailTrace_2781997 : CollatzResearch.WordTrace tailWord_2781997 prefixEnd_2781997 1428501640366257157643335 := by
  unfold tailWord_2781997
  simp only [CollatzResearch.WordTrace]
  refine ⟨101467766502307471105896245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67645177668204980737264163 101467766502307471105896245)
  ·
    refine ⟨9512603109591325416177773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101467766502307471105896245 9512603109591325416177773)
    ·
      refine ⟨3567226166096747031066665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9512603109591325416177773 3567226166096747031066665)
      ·
        refine ⟨2675419624572560273299999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3567226166096747031066665 2675419624572560273299999)
        ·
          refine ⟨4013129436858840409949999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2675419624572560273299999 4013129436858840409949999)
          ·
            refine ⟨6019694155288260614924999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4013129436858840409949999 6019694155288260614924999)
            ·
              refine ⟨9029541232932390922387499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6019694155288260614924999 9029541232932390922387499)
              ·
                refine ⟨13544311849398586383581249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9029541232932390922387499 13544311849398586383581249)
                ·
                  refine ⟨10158233887048939787685937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13544311849398586383581249 10158233887048939787685937)
                  ·
                    refine ⟨7618675415286704840764453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10158233887048939787685937 7618675415286704840764453)
                    ·
                      refine ⟨1428501640366257157643335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7618675415286704840764453 1428501640366257157643335)
                      ·
                        rfl

theorem cell23_2781997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_2781997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2781997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2781997 prefixEnd_2781997 := by exact prefixLift 2781997
  have htrace : WordTrace (prefixWord ++ tailWord_2781997) baseStart_2781997 baseEnd_2781997 := by
    simpa [prefixWord, tailWord_2781997, baseEnd_2781997] using wordTrace_append hprefix tailTrace_2781997
  have hstable : (prefixWord ++ tailWord_2781997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781997).length < 2 ^ (prefixWord ++ tailWord_2781997).sum := by decide
  have hdescent : baseEnd_2781997 < baseStart_2781997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782023 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 3, 6, 2]
def baseStart_2782023 : Nat := 118140960795 + 2782023 * 2 ^ 59
def prefixEnd_2782023 : Nat := 4983230072969 + 3 ^ 40 * 2782023 * 2
def baseEnd_2782023 : Nat := 1428514990863274055918215

theorem tailTrace_2782023 : CollatzResearch.WordTrace tailWord_2782023 prefixEnd_2782023 1428514990863274055918215 := by
  unfold tailWord_2782023
  simp only [CollatzResearch.WordTrace]
  refine ⟨101468714800213277546342723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67645809866808851697561815 101468714800213277546342723)
  ·
    refine ⟨152203072200319916319514085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101468714800213277546342723 152203072200319916319514085)
    ·
      refine ⟨28538076037559984309908891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152203072200319916319514085 28538076037559984309908891)
      ·
        refine ⟨42807114056339976464863337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28538076037559984309908891 42807114056339976464863337)
        ·
          refine ⟨32105335542254982348647503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42807114056339976464863337 32105335542254982348647503)
          ·
            refine ⟨48158003313382473522971255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32105335542254982348647503 48158003313382473522971255)
            ·
              refine ⟨72237004970073710284456883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48158003313382473522971255 72237004970073710284456883)
              ·
                refine ⟨108355507455110565426685325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72237004970073710284456883 108355507455110565426685325)
                ·
                  refine ⟨40633315295666462035006997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108355507455110565426685325 40633315295666462035006997)
                  ·
                    refine ⟨1904686654484365407890953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40633315295666462035006997 1904686654484365407890953)
                    ·
                      refine ⟨1428514990863274055918215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1904686654484365407890953 1428514990863274055918215)
                      ·
                        rfl

theorem cell23_2782023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_2782023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782023 prefixEnd_2782023 := by exact prefixLift 2782023
  have htrace : WordTrace (prefixWord ++ tailWord_2782023) baseStart_2782023 baseEnd_2782023 := by
    simpa [prefixWord, tailWord_2782023, baseEnd_2782023] using wordTrace_append hprefix tailTrace_2782023
  have hstable : (prefixWord ++ tailWord_2782023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782023).length < 2 ^ (prefixWord ++ tailWord_2782023).sum := by decide
  have hdescent : baseEnd_2782023 < baseStart_2782023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782026 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_2782026 : Nat := 118140960795 + 2782026 * 2 ^ 59
def prefixEnd_2782026 : Nat := 4983230072969 + 3 ^ 40 * 2782026 * 2
def baseEnd_2782026 : Nat := 1428516531305237544180701

theorem tailTrace_2782026 : CollatzResearch.WordTrace tailWord_2782026 prefixEnd_2782026 1428516531305237544180701 := by
  unfold tailWord_2782026
  simp only [CollatzResearch.WordTrace]
  refine ⟨25367206054800602264675483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67645882812801606039134621 25367206054800602264675483)
  ·
    refine ⟨38050809082200903397013225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25367206054800602264675483 38050809082200903397013225)
    ·
      refine ⟨28538106811650677547759919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38050809082200903397013225 28538106811650677547759919)
      ·
        refine ⟨42807160217476016321639879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28538106811650677547759919 42807160217476016321639879)
        ·
          refine ⟨64210740326214024482459819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42807160217476016321639879 64210740326214024482459819)
          ·
            refine ⟨96316110489321036723689729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64210740326214024482459819 96316110489321036723689729)
            ·
              refine ⟨72237082866990777542767297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96316110489321036723689729 72237082866990777542767297)
              ·
                refine ⟨54177812150243083157075473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72237082866990777542767297 54177812150243083157075473)
                ·
                  refine ⟨40633359112682312367806605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54177812150243083157075473 40633359112682312367806605)
                  ·
                    refine ⟨15237509667255867137927477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40633359112682312367806605 15237509667255867137927477)
                    ·
                      refine ⟨1428516531305237544180701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15237509667255867137927477 1428516531305237544180701)
                      ·
                        rfl

theorem cell23_2782026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_2782026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782026 prefixEnd_2782026 := by exact prefixLift 2782026
  have htrace : WordTrace (prefixWord ++ tailWord_2782026) baseStart_2782026 baseEnd_2782026 := by
    simpa [prefixWord, tailWord_2782026, baseEnd_2782026] using wordTrace_append hprefix tailTrace_2782026
  have hstable : (prefixWord ++ tailWord_2782026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782026).length < 2 ^ (prefixWord ++ tailWord_2782026).sum := by decide
  have hdescent : baseEnd_2782026 < baseStart_2782026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782076 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 2, 9]
def baseStart_2782076 : Nat := 118140960795 + 2782076 * 2 ^ 59
def prefixEnd_2782076 : Nat := 4983230072969 + 3 ^ 40 * 2782076 * 2
def baseEnd_2782076 : Nat := 476180735112654116185157

theorem tailTrace_2782076 : CollatzResearch.WordTrace tailWord_2782076 prefixEnd_2782076 476180735112654116185157 := by
  unfold tailWord_2782076
  simp only [CollatzResearch.WordTrace]
  refine ⟨50735323934510633799011041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67647098579347511732014721 50735323934510633799011041)
  ·
    refine ⟨38051492950882975349258281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50735323934510633799011041 38051492950882975349258281)
    ·
      refine ⟨28538619713162231511943711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38051492950882975349258281 28538619713162231511943711)
      ·
        refine ⟨42807929569743347267915567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28538619713162231511943711 42807929569743347267915567)
        ·
          refine ⟨64211894354615020901873351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42807929569743347267915567 64211894354615020901873351)
          ·
            refine ⟨96317841531922531352810027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64211894354615020901873351 96317841531922531352810027)
            ·
              refine ⟨144476762297883797029215041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96317841531922531352810027 144476762297883797029215041)
              ·
                refine ⟨108357571723412847771911281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144476762297883797029215041 108357571723412847771911281)
                ·
                  refine ⟨81268178792559635828933461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108357571723412847771911281 81268178792559635828933461)
                  ·
                    refine ⟨476180735112654116185157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 81268178792559635828933461 476180735112654116185157)
                    ·
                      rfl

theorem cell23_2782076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_2782076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782076 prefixEnd_2782076 := by exact prefixLift 2782076
  have htrace : WordTrace (prefixWord ++ tailWord_2782076) baseStart_2782076 baseEnd_2782076 := by
    simpa [prefixWord, tailWord_2782076, baseEnd_2782076] using wordTrace_append hprefix tailTrace_2782076
  have hstable : (prefixWord ++ tailWord_2782076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782076).length < 2 ^ (prefixWord ++ tailWord_2782076).sum := by decide
  have hdescent : baseEnd_2782076 < baseStart_2782076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782170 : List Nat := [3, 1, 1, 2, 4, 3, 1, 8]
def baseStart_2782170 : Nat := 118140960795 + 2782170 * 2 ^ 59
def prefixEnd_2782170 : Nat := 4983230072969 + 3 ^ 40 * 2782170 * 2
def baseEnd_2782170 : Nat := 52910758241462406695557

theorem tailTrace_2782170 : CollatzResearch.WordTrace tailWord_2782170 prefixEnd_2782170 52910758241462406695557 := by
  unfold tailWord_2782170
  simp only [CollatzResearch.WordTrace]
  refine ⟨25368519082670180412985991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67649384220453814434629309 25368519082670180412985991)
  ·
    refine ⟨38052778624005270619478987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25368519082670180412985991 38052778624005270619478987)
    ·
      refine ⟨57079167936007905929218481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38052778624005270619478987 57079167936007905929218481)
      ·
        refine ⟨42809375952005929446913861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57079167936007905929218481 42809375952005929446913861)
        ·
          refine ⟨8026757991001111771296349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42809375952005929446913861 8026757991001111771296349)
          ·
            refine ⟨3010034246625416914236131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8026757991001111771296349 3010034246625416914236131)
            ·
              refine ⟨4515051369938125371354197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3010034246625416914236131 4515051369938125371354197)
              ·
                refine ⟨52910758241462406695557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4515051369938125371354197 52910758241462406695557)
                ·
                  rfl

theorem cell23_2782170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 8].length) (baseStart_2782170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782170 prefixEnd_2782170 := by exact prefixLift 2782170
  have htrace : WordTrace (prefixWord ++ tailWord_2782170) baseStart_2782170 baseEnd_2782170 := by
    simpa [prefixWord, tailWord_2782170, baseEnd_2782170] using wordTrace_append hprefix tailTrace_2782170
  have hstable : (prefixWord ++ tailWord_2782170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782170).length < 2 ^ (prefixWord ++ tailWord_2782170).sum := by decide
  have hdescent : baseEnd_2782170 < baseStart_2782170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782181 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 3, 2, 2]
def baseStart_2782181 : Nat := 118140960795 + 2782181 * 2 ^ 59
def prefixEnd_2782181 : Nat := 4983230072969 + 3 ^ 40 * 2782181 * 2
def baseEnd_2782181 : Nat := 1428596120806684437742489

theorem tailTrace_2782181 : CollatzResearch.WordTrace tailWord_2782181 prefixEnd_2782181 1428596120806684437742489 := by
  unfold tailWord_2782181
  simp only [CollatzResearch.WordTrace]
  refine ⟨101474477533640870530594397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67649651689093913687062931 101474477533640870530594397)
  ·
    refine ⟨38052929075115326448972899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101474477533640870530594397 38052929075115326448972899)
    ·
      refine ⟨57079393612672989673459349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38052929075115326448972899 57079393612672989673459349)
      ·
        refine ⟨2675596575594046390943407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57079393612672989673459349 2675596575594046390943407)
        ·
          refine ⟨4013394863391069586415111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2675596575594046390943407 4013394863391069586415111)
          ·
            refine ⟨6020092295086604379622667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4013394863391069586415111 6020092295086604379622667)
            ·
              refine ⟨9030138442629906569434001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6020092295086604379622667 9030138442629906569434001)
              ·
                refine ⟨6772603831972429927075501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9030138442629906569434001 6772603831972429927075501)
                ·
                  refine ⟨2539726436989661222653313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6772603831972429927075501 2539726436989661222653313)
                  ·
                    refine ⟨1904794827742245916989985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2539726436989661222653313 1904794827742245916989985)
                    ·
                      refine ⟨1428596120806684437742489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1904794827742245916989985 1428596120806684437742489)
                      ·
                        rfl

theorem cell23_2782181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_2782181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782181 prefixEnd_2782181 := by exact prefixLift 2782181
  have htrace : WordTrace (prefixWord ++ tailWord_2782181) baseStart_2782181 baseEnd_2782181 := by
    simpa [prefixWord, tailWord_2782181, baseEnd_2782181] using wordTrace_append hprefix tailTrace_2782181
  have hstable : (prefixWord ++ tailWord_2782181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782181).length < 2 ^ (prefixWord ++ tailWord_2782181).sum := by decide
  have hdescent : baseEnd_2782181 < baseStart_2782181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782198 : List Nat := [5, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2]
def baseStart_2782198 : Nat := 118140960795 + 2782198 * 2 ^ 59
def prefixEnd_2782198 : Nat := 4983230072969 + 3 ^ 40 * 2782198 * 2
def baseEnd_2782198 : Nat := 1428604849977810871229911

theorem tailTrace_2782198 : CollatzResearch.WordTrace tailWord_2782198 prefixEnd_2782198 1428604849977810871229911 := by
  unfold tailWord_2782198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6342193598411205152122703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67650065049719521622642165 6342193598411205152122703)
  ·
    refine ⟨9513290397616807728184055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6342193598411205152122703 9513290397616807728184055)
    ·
      refine ⟨14269935596425211592276083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9513290397616807728184055 14269935596425211592276083)
      ·
        refine ⟨21404903394637817388414125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14269935596425211592276083 21404903394637817388414125)
        ·
          refine ⟨8026838772989181520655297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21404903394637817388414125 8026838772989181520655297)
          ·
            refine ⟨6020129079741886140491473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8026838772989181520655297 6020129079741886140491473)
            ·
              refine ⟨4515096809806414605368605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6020129079741886140491473 4515096809806414605368605)
              ·
                refine ⟨1693161303677405477013227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4515096809806414605368605 1693161303677405477013227)
                ·
                  refine ⟨2539741955516108215519841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693161303677405477013227 2539741955516108215519841)
                  ·
                    refine ⟨1904806466637081161639881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2539741955516108215519841 1904806466637081161639881)
                    ·
                      refine ⟨1428604849977810871229911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1904806466637081161639881 1428604849977810871229911)
                      ·
                        rfl

theorem cell23_2782198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_2782198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782198 prefixEnd_2782198 := by exact prefixLift 2782198
  have htrace : WordTrace (prefixWord ++ tailWord_2782198) baseStart_2782198 baseEnd_2782198 := by
    simpa [prefixWord, tailWord_2782198, baseEnd_2782198] using wordTrace_append hprefix tailTrace_2782198
  have hstable : (prefixWord ++ tailWord_2782198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782198).length < 2 ^ (prefixWord ++ tailWord_2782198).sum := by decide
  have hdescent : baseEnd_2782198 < baseStart_2782198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782213 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 4, 6]
def baseStart_2782213 : Nat := 118140960795 + 2782213 * 2 ^ 59
def prefixEnd_2782213 : Nat := 4983230072969 + 3 ^ 40 * 2782213 * 2
def baseEnd_2782213 : Nat := 476204184062542770847447

theorem tailTrace_2782213 : CollatzResearch.WordTrace tailWord_2782213 prefixEnd_2782213 476204184062542770847447 := by
  unfold tailWord_2782213
  simp only [CollatzResearch.WordTrace]
  refine ⟨101475644669524939995759293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67650429779683293330506195 101475644669524939995759293)
  ·
    refine ⟨38053366751071852498409735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101475644669524939995759293 38053366751071852498409735)
    ·
      refine ⟨57080050126607778747614603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38053366751071852498409735 57080050126607778747614603)
      ·
        refine ⟨85620075189911668121421905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57080050126607778747614603 85620075189911668121421905)
        ·
          refine ⟨64215056392433751091066429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85620075189911668121421905 64215056392433751091066429)
          ·
            refine ⟨24080646147162656659149911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64215056392433751091066429 24080646147162656659149911)
            ·
              refine ⟨36120969220743984988724867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24080646147162656659149911 36120969220743984988724867)
              ·
                refine ⟨54181453831115977483087301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36120969220743984988724867 54181453831115977483087301)
                ·
                  refine ⟨10159022593334245778078869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54181453831115977483087301 10159022593334245778078869)
                  ·
                    refine ⟨476204184062542770847447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10159022593334245778078869 476204184062542770847447)
                    ·
                      rfl

theorem cell23_2782213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_2782213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782213 prefixEnd_2782213 := by exact prefixLift 2782213
  have htrace : WordTrace (prefixWord ++ tailWord_2782213) baseStart_2782213 baseEnd_2782213 := by
    simpa [prefixWord, tailWord_2782213, baseEnd_2782213] using wordTrace_append hprefix tailTrace_2782213
  have hstable : (prefixWord ++ tailWord_2782213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782213).length < 2 ^ (prefixWord ++ tailWord_2782213).sum := by decide
  have hdescent : baseEnd_2782213 < baseStart_2782213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782231 : List Nat := [1, 1, 3, 5, 1, 2, 3, 1, 2, 1, 3]
def baseStart_2782231 : Nat := 118140960795 + 2782231 * 2 ^ 59
def prefixEnd_2782231 : Nat := 4983230072969 + 3 ^ 40 * 2782231 * 2
def baseEnd_2782231 : Nat := 1428621794839409242117259

theorem tailTrace_2782231 : CollatzResearch.WordTrace tailWord_2782231 prefixEnd_2782231 1428621794839409242117259 := by
  unfold tailWord_2782231
  simp only [CollatzResearch.WordTrace]
  refine ⟨101476301183459729069914547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67650867455639819379943031 101476301183459729069914547)
  ·
    refine ⟨152214451775189593604871821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101476301183459729069914547 152214451775189593604871821)
    ·
      refine ⟨57080419415696097601826933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152214451775189593604871821 57080419415696097601826933)
      ·
        refine ⟨5351289320221509150171275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57080419415696097601826933 5351289320221509150171275)
        ·
          refine ⟨8026933980332263725256913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5351289320221509150171275 8026933980332263725256913)
          ·
            refine ⟨6020200485249197793942685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8026933980332263725256913 6020200485249197793942685)
            ·
              refine ⟨2257575181968449172728507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6020200485249197793942685 2257575181968449172728507)
              ·
                refine ⟨3386362772952673759092761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2257575181968449172728507 3386362772952673759092761)
                ·
                  refine ⟨2539772079714505319319571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3386362772952673759092761 2539772079714505319319571)
                  ·
                    refine ⟨3809658119571757978979357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2539772079714505319319571 3809658119571757978979357)
                    ·
                      refine ⟨1428621794839409242117259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3809658119571757978979357 1428621794839409242117259)
                      ·
                        rfl

theorem cell23_2782231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_2782231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782231 prefixEnd_2782231 := by exact prefixLift 2782231
  have htrace : WordTrace (prefixWord ++ tailWord_2782231) baseStart_2782231 baseEnd_2782231 := by
    simpa [prefixWord, tailWord_2782231, baseEnd_2782231] using wordTrace_append hprefix tailTrace_2782231
  have hstable : (prefixWord ++ tailWord_2782231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782231).length < 2 ^ (prefixWord ++ tailWord_2782231).sum := by decide
  have hdescent : baseEnd_2782231 < baseStart_2782231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782254 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_2782254 : Nat := 118140960795 + 2782254 * 2 ^ 59
def prefixEnd_2782254 : Nat := 4983230072969 + 3 ^ 40 * 2782254 * 2
def baseEnd_2782254 : Nat := 1428633604894462652129653

theorem tailTrace_2782254 : CollatzResearch.WordTrace tailWord_2782254 prefixEnd_2782254 1428633604894462652129653 := by
  unfold tailWord_2782254
  simp only [CollatzResearch.WordTrace]
  refine ⟨12684642507797050499750227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67651426708250935998667877 12684642507797050499750227)
  ·
    refine ⟨19026963761695575749625341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12684642507797050499750227 19026963761695575749625341)
    ·
      refine ⟨7135111410635840906109503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19026963761695575749625341 7135111410635840906109503)
      ·
        refine ⟨10702667115953761359164255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7135111410635840906109503 10702667115953761359164255)
        ·
          refine ⟨16054000673930642038746383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10702667115953761359164255 16054000673930642038746383)
          ·
            refine ⟨24081001010895963058119575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16054000673930642038746383 24081001010895963058119575)
            ·
              refine ⟨36121501516343944587179363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24081001010895963058119575 36121501516343944587179363)
              ·
                refine ⟨54182252274515916880769045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36121501516343944587179363 54182252274515916880769045)
                ·
                  refine ⟨2539793075367933603786049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54182252274515916880769045 2539793075367933603786049)
                  ·
                    refine ⟨1904844806525950202839537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2539793075367933603786049 1904844806525950202839537)
                    ·
                      refine ⟨1428633604894462652129653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1904844806525950202839537 1428633604894462652129653)
                      ·
                        rfl

theorem cell23_2782254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_2782254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782254 prefixEnd_2782254 := by exact prefixLift 2782254
  have htrace : WordTrace (prefixWord ++ tailWord_2782254) baseStart_2782254 baseEnd_2782254 := by
    simpa [prefixWord, tailWord_2782254, baseEnd_2782254] using wordTrace_append hprefix tailTrace_2782254
  have hstable : (prefixWord ++ tailWord_2782254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782254).length < 2 ^ (prefixWord ++ tailWord_2782254).sum := by decide
  have hdescent : baseEnd_2782254 < baseStart_2782254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782300 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_2782300 : Nat := 118140960795 + 2782300 * 2 ^ 59
def prefixEnd_2782300 : Nat := 4983230072969 + 3 ^ 40 * 2782300 * 2
def baseEnd_2782300 : Nat := 1428657225004569472154441

theorem tailTrace_2782300 : CollatzResearch.WordTrace tailWord_2782300 prefixEnd_2782300 1428657225004569472154441 := by
  unfold tailWord_2782300
  simp only [CollatzResearch.WordTrace]
  refine ⟨50739408910104876927088177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67652545213473169236117569 50739408910104876927088177)
  ·
    refine ⟨38054556682578657695316133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50739408910104876927088177 38054556682578657695316133)
    ·
      refine ⟨7135229377983498317871775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38054556682578657695316133 7135229377983498317871775)
      ·
        refine ⟨10702844066975247476807663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7135229377983498317871775 10702844066975247476807663)
        ·
          refine ⟨16054266100462871215211495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10702844066975247476807663 16054266100462871215211495)
          ·
            refine ⟨24081399150694306822817243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16054266100462871215211495 24081399150694306822817243)
            ·
              refine ⟨36122098726041460234225865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24081399150694306822817243 36122098726041460234225865)
              ·
                refine ⟨27091574044531095175669399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36122098726041460234225865 27091574044531095175669399)
                ·
                  refine ⟨40637361066796642763504099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27091574044531095175669399 40637361066796642763504099)
                  ·
                    refine ⟨60956041600194964145256149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40637361066796642763504099 60956041600194964145256149)
                    ·
                      refine ⟨1428657225004569472154441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60956041600194964145256149 1428657225004569472154441)
                      ·
                        rfl

theorem cell23_2782300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_2782300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782300 prefixEnd_2782300 := by exact prefixLift 2782300
  have htrace : WordTrace (prefixWord ++ tailWord_2782300) baseStart_2782300 baseEnd_2782300 := by
    simpa [prefixWord, tailWord_2782300, baseEnd_2782300] using wordTrace_append hprefix tailTrace_2782300
  have hstable : (prefixWord ++ tailWord_2782300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782300).length < 2 ^ (prefixWord ++ tailWord_2782300).sum := by decide
  have hdescent : baseEnd_2782300 < baseStart_2782300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782327 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 2, 4, 2]
def baseStart_2782327 : Nat := 118140960795 + 2782327 * 2 ^ 59
def prefixEnd_2782327 : Nat := 4983230072969 + 3 ^ 40 * 2782327 * 2
def baseEnd_2782327 : Nat := 1428671088982240866516817

theorem tailTrace_2782327 : CollatzResearch.WordTrace tailWord_2782327 prefixEnd_2782327 1428671088982240866516817 := by
  unfold tailWord_2782327
  simp only [CollatzResearch.WordTrace]
  refine ⟨101479802591111937465409235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67653201727407958310272823 101479802591111937465409235)
  ·
    refine ⟨152219703886667906198113853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101479802591111937465409235 152219703886667906198113853)
    ·
      refine ⟨57082388957500464824292695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152219703886667906198113853 57082388957500464824292695)
      ·
        refine ⟨85623583436250697236439043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57082388957500464824292695 85623583436250697236439043)
        ·
          refine ⟨128435375154376045854658565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85623583436250697236439043 128435375154376045854658565)
          ·
            refine ⟨24081632841445508597748481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128435375154376045854658565 24081632841445508597748481)
            ·
              refine ⟨18061224631084131448311361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24081632841445508597748481 18061224631084131448311361)
              ·
                refine ⟨13545918473313098586233521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18061224631084131448311361 13545918473313098586233521)
                ·
                  refine ⟨10159438854984823939675141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13545918473313098586233521 10159438854984823939675141)
                  ·
                    refine ⟨1904894785309654488689089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10159438854984823939675141 1904894785309654488689089)
                    ·
                      refine ⟨1428671088982240866516817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1904894785309654488689089 1428671088982240866516817)
                      ·
                        rfl

theorem cell23_2782327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 4, 2].length) (baseStart_2782327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782327 prefixEnd_2782327 := by exact prefixLift 2782327
  have htrace : WordTrace (prefixWord ++ tailWord_2782327) baseStart_2782327 baseEnd_2782327 := by
    simpa [prefixWord, tailWord_2782327, baseEnd_2782327] using wordTrace_append hprefix tailTrace_2782327
  have hstable : (prefixWord ++ tailWord_2782327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782327).length < 2 ^ (prefixWord ++ tailWord_2782327).sum := by decide
  have hdescent : baseEnd_2782327 < baseStart_2782327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782354 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 3, 4]
def baseStart_2782354 : Nat := 118140960795 + 2782354 * 2 ^ 59
def prefixEnd_2782354 : Nat := 4983230072969 + 3 ^ 40 * 2782354 * 2
def baseEnd_2782354 : Nat := 476228317653304086959731

theorem tailTrace_2782354 : CollatzResearch.WordTrace tailWord_2782354 prefixEnd_2782354 476228317653304086959731 := by
  unfold tailWord_2782354
  simp only [CollatzResearch.WordTrace]
  refine ⟨25370196840503530269160529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67653858241342747384428077 25370196840503530269160529)
  ·
    refine ⟨19027647630377647701870397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25370196840503530269160529 19027647630377647701870397)
    ·
      refine ⟨7135367861391617888201399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19027647630377647701870397 7135367861391617888201399)
      ·
        refine ⟨10703051792087426832302099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7135367861391617888201399 10703051792087426832302099)
        ·
          refine ⟨16054577688131140248453149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10703051792087426832302099 16054577688131140248453149)
          ·
            refine ⟨6020466633049177593169931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16054577688131140248453149 6020466633049177593169931)
            ·
              refine ⟨9030699949573766389754897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6020466633049177593169931 9030699949573766389754897)
              ·
                refine ⟨6773024962180324792316173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9030699949573766389754897 6773024962180324792316173)
                ·
                  refine ⟨2539884360817621797118565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6773024962180324792316173 2539884360817621797118565)
                  ·
                    refine ⟨476228317653304086959731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2539884360817621797118565 476228317653304086959731)
                    ·
                      rfl

theorem cell23_2782354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_2782354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782354 prefixEnd_2782354 := by exact prefixLift 2782354
  have htrace : WordTrace (prefixWord ++ tailWord_2782354) baseStart_2782354 baseEnd_2782354 := by
    simpa [prefixWord, tailWord_2782354, baseEnd_2782354] using wordTrace_append hprefix tailTrace_2782354
  have hstable : (prefixWord ++ tailWord_2782354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782354).length < 2 ^ (prefixWord ++ tailWord_2782354).sum := by decide
  have hdescent : baseEnd_2782354 < baseStart_2782354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782364 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_2782364 : Nat := 118140960795 + 2782364 * 2 ^ 59
def prefixEnd_2782364 : Nat := 4983230072969 + 3 ^ 40 * 2782364 * 2
def baseEnd_2782364 : Nat := 1428690087766457221754147

theorem tailTrace_2782364 : CollatzResearch.WordTrace tailWord_2782364 prefixEnd_2782364 1428690087766457221754147 := by
  unfold tailWord_2782364
  simp only [CollatzResearch.WordTrace]
  refine ⟨50740576045988946392253073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67654101394651928523004097 50740576045988946392253073)
  ·
    refine ⟨38055432034491709794189805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50740576045988946392253073 38055432034491709794189805)
    ·
      refine ⟨14270787012934391172821177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38055432034491709794189805 14270787012934391172821177)
      ·
        refine ⟨10703090259700793379615883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14270787012934391172821177 10703090259700793379615883)
        ·
          refine ⟨16054635389551190069423825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10703090259700793379615883 16054635389551190069423825)
          ·
            refine ⟨12040976542163392552067869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16054635389551190069423825 12040976542163392552067869)
            ·
              refine ⟨4515366203311272207025451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12040976542163392552067869 4515366203311272207025451)
              ·
                refine ⟨6773049304966908310538177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4515366203311272207025451 6773049304966908310538177)
                ·
                  refine ⟨5079786978725181232903633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6773049304966908310538177 5079786978725181232903633)
                  ·
                    refine ⟨3809840234043885924677725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5079786978725181232903633 3809840234043885924677725)
                    ·
                      refine ⟨1428690087766457221754147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3809840234043885924677725 1428690087766457221754147)
                      ·
                        rfl

theorem cell23_2782364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_2782364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782364 prefixEnd_2782364 := by exact prefixLift 2782364
  have htrace : WordTrace (prefixWord ++ tailWord_2782364) baseStart_2782364 baseEnd_2782364 := by
    simpa [prefixWord, tailWord_2782364, baseEnd_2782364] using wordTrace_append hprefix tailTrace_2782364
  have hstable : (prefixWord ++ tailWord_2782364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782364).length < 2 ^ (prefixWord ++ tailWord_2782364).sum := by decide
  have hdescent : baseEnd_2782364 < baseStart_2782364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782380 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 5, 5]
def baseStart_2782380 : Nat := 118140960795 + 2782380 * 2 ^ 59
def prefixEnd_2782380 : Nat := 4983230072969 + 3 ^ 40 * 2782380 * 2
def baseEnd_2782380 : Nat := 476232767818976386384691

theorem tailTrace_2782380 : CollatzResearch.WordTrace tailWord_2782380 prefixEnd_2782380 476232767818976386384691 := by
  unfold tailWord_2782380
  simp only [CollatzResearch.WordTrace]
  refine ⟨50740867829959963758544297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67654490439946618344725729 50740867829959963758544297)
  ·
    refine ⟨38055650872469972818908223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50740867829959963758544297 38055650872469972818908223)
    ·
      refine ⟨57083476308704959228362335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38055650872469972818908223 57083476308704959228362335)
      ·
        refine ⟨85625214463057438842543503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57083476308704959228362335 85625214463057438842543503)
        ·
          refine ⟨128437821694586158263815255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85625214463057438842543503 128437821694586158263815255)
          ·
            refine ⟨192656732541879237395722883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128437821694586158263815255 192656732541879237395722883)
            ·
              refine ⟨288985098812818856093584325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192656732541879237395722883 288985098812818856093584325)
              ·
                refine ⟨54184706027403535517547061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 288985098812818856093584325 54184706027403535517547061)
                ·
                  refine ⟨5079816190069081454770037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54184706027403535517547061 5079816190069081454770037)
                  ·
                    refine ⟨476232767818976386384691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5079816190069081454770037 476232767818976386384691)
                    ·
                      rfl

theorem cell23_2782380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_2782380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782380 prefixEnd_2782380 := by exact prefixLift 2782380
  have htrace : WordTrace (prefixWord ++ tailWord_2782380) baseStart_2782380 baseEnd_2782380 := by
    simpa [prefixWord, tailWord_2782380, baseEnd_2782380] using wordTrace_append hprefix tailTrace_2782380
  have hstable : (prefixWord ++ tailWord_2782380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782380).length < 2 ^ (prefixWord ++ tailWord_2782380).sum := by decide
  have hdescent : baseEnd_2782380 < baseStart_2782380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782401 : List Nat := [1, 2, 6, 1, 1, 2, 3, 1, 6]
def baseStart_2782401 : Nat := 118140960795 + 2782401 * 2 ^ 59
def prefixEnd_2782401 : Nat := 4983230072969 + 3 ^ 40 * 2782401 * 2
def baseEnd_2782401 : Nat := 158745454061185952999053

theorem tailTrace_2782401 : CollatzResearch.WordTrace tailWord_2782401 prefixEnd_2782401 158745454061185952999053 := by
  unfold tailWord_2782401
  simp only [CollatzResearch.WordTrace]
  refine ⟨101482501592843848103603057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67655001061895898735735371 101482501592843848103603057)
  ·
    refine ⟨76111876194632886077702293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101482501592843848103603057 76111876194632886077702293)
    ·
      refine ⟨3567744196623416534892295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76111876194632886077702293 3567744196623416534892295)
      ·
        refine ⟨5351616294935124802338443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3567744196623416534892295 5351616294935124802338443)
        ·
          refine ⟨8027424442402687203507665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5351616294935124802338443 8027424442402687203507665)
          ·
            refine ⟨6020568331802015402630749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8027424442402687203507665 6020568331802015402630749)
            ·
              refine ⟨2257713124425755775986531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6020568331802015402630749 2257713124425755775986531)
              ·
                refine ⟨3386569686638633663979797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2257713124425755775986531 3386569686638633663979797)
                ·
                  refine ⟨158745454061185952999053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3386569686638633663979797 158745454061185952999053)
                  ·
                    rfl

theorem cell23_2782401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 6].length) (baseStart_2782401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782401 prefixEnd_2782401 := by exact prefixLift 2782401
  have htrace : WordTrace (prefixWord ++ tailWord_2782401) baseStart_2782401 baseEnd_2782401 := by
    simpa [prefixWord, tailWord_2782401, baseEnd_2782401] using wordTrace_append hprefix tailTrace_2782401
  have hstable : (prefixWord ++ tailWord_2782401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782401).length < 2 ^ (prefixWord ++ tailWord_2782401).sum := by decide
  have hdescent : baseEnd_2782401 < baseStart_2782401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782417 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 1, 8, 2]
def baseStart_2782417 : Nat := 118140960795 + 2782417 * 2 ^ 59
def prefixEnd_2782417 : Nat := 4983230072969 + 3 ^ 40 * 2782417 * 2
def baseEnd_2782417 : Nat := 1428717302241145514391403

theorem tailTrace_2782417 : CollatzResearch.WordTrace tailWord_2782417 prefixEnd_2782417 1428717302241145514391403 := by
  unfold tailWord_2782417
  simp only [CollatzResearch.WordTrace]
  refine ⟨101483085160785882836185505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67655390107190588557457003 101483085160785882836185505)
  ·
    refine ⟨76112313870589412127139129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101483085160785882836185505 76112313870589412127139129)
    ·
      refine ⟨57084235402942059095354347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76112313870589412127139129 57084235402942059095354347)
      ·
        refine ⟨85626353104413088643031521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57084235402942059095354347 85626353104413088643031521)
        ·
          refine ⟨64219764828309816482273641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85626353104413088643031521 64219764828309816482273641)
          ·
            refine ⟨48164823621232362361705231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64219764828309816482273641 48164823621232362361705231)
            ·
              refine ⟨72247235431848543542557847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48164823621232362361705231 72247235431848543542557847)
              ·
                refine ⟨108370853147772815313836771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72247235431848543542557847 108370853147772815313836771)
                ·
                  refine ⟨162556279721659222970755157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108370853147772815313836771 162556279721659222970755157)
                  ·
                    refine ⟨1904956402988194019188537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 162556279721659222970755157 1904956402988194019188537)
                    ·
                      refine ⟨1428717302241145514391403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1904956402988194019188537 1428717302241145514391403)
                      ·
                        rfl

theorem cell23_2782417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 8, 2].length) (baseStart_2782417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782417 prefixEnd_2782417 := by exact prefixLift 2782417
  have htrace : WordTrace (prefixWord ++ tailWord_2782417) baseStart_2782417 baseEnd_2782417 := by
    simpa [prefixWord, tailWord_2782417, baseEnd_2782417] using wordTrace_append hprefix tailTrace_2782417
  have hstable : (prefixWord ++ tailWord_2782417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782417).length < 2 ^ (prefixWord ++ tailWord_2782417).sum := by decide
  have hdescent : baseEnd_2782417 < baseStart_2782417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782422 : List Nat := [5, 2, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_2782422 : Nat := 118140960795 + 2782422 * 2 ^ 59
def prefixEnd_2782422 : Nat := 4983230072969 + 3 ^ 40 * 2782422 * 2
def baseEnd_2782422 : Nat := 476239956548139331609627

theorem tailTrace_2782422 : CollatzResearch.WordTrace tailWord_2782422 prefixEnd_2782422 476239956548139331609627 := by
  unfold tailWord_2782422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6342704220360485543132345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67655511683845179126745013 6342704220360485543132345)
  ·
    refine ⟨4757028165270364157349259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6342704220360485543132345 4757028165270364157349259)
    ·
      refine ⟨7135542247905546236023889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4757028165270364157349259 7135542247905546236023889)
      ·
        refine ⟨5351656685929159677017917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7135542247905546236023889 5351656685929159677017917)
        ·
          refine ⟨2006871257223434878881719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5351656685929159677017917 2006871257223434878881719)
          ·
            refine ⟨3010306885835152318322579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006871257223434878881719 3010306885835152318322579)
            ·
              refine ⟨4515460328752728477483869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3010306885835152318322579 4515460328752728477483869)
              ·
                refine ⟨1693297623282273179056451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4515460328752728477483869 1693297623282273179056451)
                ·
                  refine ⟨2539946434923409768584677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693297623282273179056451 2539946434923409768584677)
                  ·
                    refine ⟨476239956548139331609627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2539946434923409768584677 476239956548139331609627)
                    ·
                      rfl

theorem cell23_2782422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_2782422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782422 prefixEnd_2782422 := by exact prefixLift 2782422
  have htrace : WordTrace (prefixWord ++ tailWord_2782422) baseStart_2782422 baseEnd_2782422 := by
    simpa [prefixWord, tailWord_2782422, baseEnd_2782422] using wordTrace_append hprefix tailTrace_2782422
  have hstable : (prefixWord ++ tailWord_2782422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782422).length < 2 ^ (prefixWord ++ tailWord_2782422).sum := by decide
  have hdescent : baseEnd_2782422 < baseStart_2782422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782445 : List Nat := [1, 5, 1, 2, 2, 2, 3, 2, 1, 1, 3]
def baseStart_2782445 : Nat := 118140960795 + 2782445 * 2 ^ 59
def prefixEnd_2782445 : Nat := 4983230072969 + 3 ^ 40 * 2782445 * 2
def baseEnd_2782445 : Nat := 1428731679699471404841275

theorem tailTrace_2782445 : CollatzResearch.WordTrace tailWord_2782445 prefixEnd_2782445 1428731679699471404841275 := by
  unfold tailWord_2782445
  simp only [CollatzResearch.WordTrace]
  refine ⟨101484106404684443618204789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67656070936456295745469859 101484106404684443618204789)
  ·
    refine ⟨9514134975439166589206699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101484106404684443618204789 9514134975439166589206699)
    ·
      refine ⟨14271202463158749883810049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9514134975439166589206699 14271202463158749883810049)
      ·
        refine ⟨10703401847369062412857537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14271202463158749883810049 10703401847369062412857537)
        ·
          refine ⟨8027551385526796809643153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10703401847369062412857537 8027551385526796809643153)
          ·
            refine ⟨6020663539145097607232365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8027551385526796809643153 6020663539145097607232365)
            ·
              refine ⟨2257748827179411602712137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6020663539145097607232365 2257748827179411602712137)
              ·
                refine ⟨1693311620384558702034103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2257748827179411602712137 1693311620384558702034103)
                ·
                  refine ⟨2539967430576838053051155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693311620384558702034103 2539967430576838053051155)
                  ·
                    refine ⟨3809951145865257079576733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2539967430576838053051155 3809951145865257079576733)
                    ·
                      refine ⟨1428731679699471404841275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3809951145865257079576733 1428731679699471404841275)
                      ·
                        rfl

theorem cell23_2782445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_2782445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782445 prefixEnd_2782445 := by exact prefixLift 2782445
  have htrace : WordTrace (prefixWord ++ tailWord_2782445) baseStart_2782445 baseEnd_2782445 := by
    simpa [prefixWord, tailWord_2782445, baseEnd_2782445] using wordTrace_append hprefix tailTrace_2782445
  have hstable : (prefixWord ++ tailWord_2782445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782445).length < 2 ^ (prefixWord ++ tailWord_2782445).sum := by decide
  have hdescent : baseEnd_2782445 < baseStart_2782445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782451 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 3, 2, 2]
def baseStart_2782451 : Nat := 118140960795 + 2782451 * 2 ^ 59
def prefixEnd_2782451 : Nat := 4983230072969 + 3 ^ 40 * 2782451 * 2
def baseEnd_2782451 : Nat := 1428734760583398381366247

theorem tailTrace_2782451 : CollatzResearch.WordTrace tailWord_2782451 prefixEnd_2782451 1428734760583398381366247 := by
  unfold tailWord_2782451
  simp only [CollatzResearch.WordTrace]
  refine ⟨101484325242662706642923207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67656216828441804428615471 101484325242662706642923207)
  ·
    refine ⟨152226487863994059964384811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101484325242662706642923207 152226487863994059964384811)
    ·
      refine ⟨228339731795991089946577217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152226487863994059964384811 228339731795991089946577217)
      ·
        refine ⟨171254798846993317459932913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228339731795991089946577217 171254798846993317459932913)
        ·
          refine ⟨128441099135244988094949685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171254798846993317459932913 128441099135244988094949685)
          ·
            refine ⟨12041353043929217633901533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128441099135244988094949685 12041353043929217633901533)
            ·
              refine ⟨4515507391473456612713075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12041353043929217633901533 4515507391473456612713075)
              ·
                refine ⟨6773261087210184919069613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4515507391473456612713075 6773261087210184919069613)
                ·
                  refine ⟨2539972907703819344651105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6773261087210184919069613 2539972907703819344651105)
                  ·
                    refine ⟨1904979680777864508488329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2539972907703819344651105 1904979680777864508488329)
                    ·
                      refine ⟨1428734760583398381366247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1904979680777864508488329 1428734760583398381366247)
                      ·
                        rfl

theorem cell23_2782451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 2, 2].length) (baseStart_2782451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782451 prefixEnd_2782451 := by exact prefixLift 2782451
  have htrace : WordTrace (prefixWord ++ tailWord_2782451) baseStart_2782451 baseEnd_2782451 := by
    simpa [prefixWord, tailWord_2782451, baseEnd_2782451] using wordTrace_append hprefix tailTrace_2782451
  have hstable : (prefixWord ++ tailWord_2782451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782451).length < 2 ^ (prefixWord ++ tailWord_2782451).sum := by decide
  have hdescent : baseEnd_2782451 < baseStart_2782451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782452 : List Nat := [2, 6, 1, 2, 2, 1, 2, 1, 6]
def baseStart_2782452 : Nat := 118140960795 + 2782452 * 2 ^ 59
def prefixEnd_2782452 : Nat := 4983230072969 + 3 ^ 40 * 2782452 * 2
def baseEnd_2782452 : Nat := 158748363784894764161527

theorem tailTrace_2782452 : CollatzResearch.WordTrace tailWord_2782452 prefixEnd_2782452 158748363784894764161527 := by
  unfold tailWord_2782452
  simp only [CollatzResearch.WordTrace]
  refine ⟨50742180857829541906854805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67656241143772722542473073 50742180857829541906854805)
  ·
    refine ⟨2378539727710759776883819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50742180857829541906854805 2378539727710759776883819)
    ·
      refine ⟨3567809591566139665325729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2378539727710759776883819 3567809591566139665325729)
      ·
        refine ⟨2675857193674604748994297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3567809591566139665325729 2675857193674604748994297)
        ·
          refine ⟨2006892895255953561745723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2675857193674604748994297 2006892895255953561745723)
          ·
            refine ⟨3010339342883930342618585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006892895255953561745723 3010339342883930342618585)
            ·
              refine ⟨2257754507162947756963939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3010339342883930342618585 2257754507162947756963939)
              ·
                refine ⟨3386631760744421635445909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2257754507162947756963939 3386631760744421635445909)
                ·
                  refine ⟨158748363784894764161527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3386631760744421635445909 158748363784894764161527)
                  ·
                    rfl

theorem cell23_2782452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_2782452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782452 prefixEnd_2782452 := by exact prefixLift 2782452
  have htrace : WordTrace (prefixWord ++ tailWord_2782452) baseStart_2782452 baseEnd_2782452 := by
    simpa [prefixWord, tailWord_2782452, baseEnd_2782452] using wordTrace_append hprefix tailTrace_2782452
  have hstable : (prefixWord ++ tailWord_2782452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782452).length < 2 ^ (prefixWord ++ tailWord_2782452).sum := by decide
  have hdescent : baseEnd_2782452 < baseStart_2782452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782454 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_2782454 : Nat := 118140960795 + 2782454 * 2 ^ 59
def prefixEnd_2782454 : Nat := 4983230072969 + 3 ^ 40 * 2782454 * 2
def baseEnd_2782454 : Nat := 1428736301025361869628733

theorem tailTrace_2782454 : CollatzResearch.WordTrace tailWord_2782454 prefixEnd_2782454 1428736301025361869628733 := by
  unfold tailWord_2782454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6342777166353239884705151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67656289774434558770188277 6342777166353239884705151)
  ·
    refine ⟨9514165749529859827057727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6342777166353239884705151 9514165749529859827057727)
    ·
      refine ⟨14271248624294789740586591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9514165749529859827057727 14271248624294789740586591)
      ·
        refine ⟨21406872936442184610879887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14271248624294789740586591 21406872936442184610879887)
        ·
          refine ⟨32110309404663276916319831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21406872936442184610879887 32110309404663276916319831)
          ·
            refine ⟨48165464106994915374479747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32110309404663276916319831 48165464106994915374479747)
            ·
              refine ⟨72248196160492373061719621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48165464106994915374479747 72248196160492373061719621)
              ·
                refine ⟨13546536780092319949072429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72248196160492373061719621 13546536780092319949072429)
                ·
                  refine ⟨5079951292534619980902161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13546536780092319949072429 5079951292534619980902161)
                  ·
                    refine ⟨3809963469400964985676621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5079951292534619980902161 3809963469400964985676621)
                    ·
                      refine ⟨1428736301025361869628733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3809963469400964985676621 1428736301025361869628733)
                      ·
                        rfl

theorem cell23_2782454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_2782454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782454 prefixEnd_2782454 := by exact prefixLift 2782454
  have htrace : WordTrace (prefixWord ++ tailWord_2782454) baseStart_2782454 baseEnd_2782454 := by
    simpa [prefixWord, tailWord_2782454, baseEnd_2782454] using wordTrace_append hprefix tailTrace_2782454
  have hstable : (prefixWord ++ tailWord_2782454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782454).length < 2 ^ (prefixWord ++ tailWord_2782454).sum := by decide
  have hdescent : baseEnd_2782454 < baseStart_2782454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782480 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 7]
def baseStart_2782480 : Nat := 118140960795 + 2782480 * 2 ^ 59
def prefixEnd_2782480 : Nat := 4983230072969 + 3 ^ 40 * 2782480 * 2
def baseEnd_2782480 : Nat := 1428749651522378767903613

theorem tailTrace_2782480 : CollatzResearch.WordTrace tailWord_2782480 prefixEnd_2782480 1428749651522378767903613 := by
  unfold tailWord_2782480
  simp only [CollatzResearch.WordTrace]
  refine ⟨50742691479778822297864447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67656921973038429730485929 50742691479778822297864447)
  ·
    refine ⟨76114037219668233446796671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50742691479778822297864447 76114037219668233446796671)
    ·
      refine ⟨114171055829502350170195007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76114037219668233446796671 114171055829502350170195007)
      ·
        refine ⟨171256583744253525255292511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114171055829502350170195007 171256583744253525255292511)
        ·
          refine ⟨256884875616380287882938767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171256583744253525255292511 256884875616380287882938767)
          ·
            refine ⟨385327313424570431824408151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256884875616380287882938767 385327313424570431824408151)
            ·
              refine ⟨577990970136855647736612227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385327313424570431824408151 577990970136855647736612227)
              ·
                refine ⟨866986455205283471604918341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577990970136855647736612227 866986455205283471604918341)
                ·
                  refine ⟨162559960350990650925922189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 866986455205283471604918341 162559960350990650925922189)
                  ·
                    refine ⟨60959985131621494097220821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 162559960350990650925922189 60959985131621494097220821)
                    ·
                      refine ⟨1428749651522378767903613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60959985131621494097220821 1428749651522378767903613)
                      ·
                        rfl

theorem cell23_2782480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_2782480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782480 prefixEnd_2782480 := by exact prefixLift 2782480
  have htrace : WordTrace (prefixWord ++ tailWord_2782480) baseStart_2782480 baseEnd_2782480 := by
    simpa [prefixWord, tailWord_2782480, baseEnd_2782480] using wordTrace_append hprefix tailTrace_2782480
  have hstable : (prefixWord ++ tailWord_2782480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782480).length < 2 ^ (prefixWord ++ tailWord_2782480).sum := by decide
  have hdescent : baseEnd_2782480 < baseStart_2782480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782501 : List Nat := [1, 3, 1, 2, 4, 1, 1, 4, 2, 1, 3]
def baseStart_2782501 : Nat := 118140960795 + 2782501 * 2 ^ 59
def prefixEnd_2782501 : Nat := 4983230072969 + 3 ^ 40 * 2782501 * 2
def baseEnd_2782501 : Nat := 1428760434616123185741017

theorem tailTrace_2782501 : CollatzResearch.WordTrace tailWord_2782501 prefixEnd_2782501 1428760434616123185741017 := by
  unfold tailWord_2782501
  simp only [CollatzResearch.WordTrace]
  refine ⟨101486148892481565182243357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67657432594987710121495571 101486148892481565182243357)
  ·
    refine ⟨38057305834680586943341259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101486148892481565182243357 38057305834680586943341259)
    ·
      refine ⟨57085958752020880415011889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38057305834680586943341259 57085958752020880415011889)
      ·
        refine ⟨42814469064015660311258917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57085958752020880415011889 42814469064015660311258917)
        ·
          refine ⟨8027712949502936308361047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42814469064015660311258917 8027712949502936308361047)
          ·
            refine ⟨12041569424254404462541571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8027712949502936308361047 12041569424254404462541571)
            ·
              refine ⟨18062354136381606693812357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12041569424254404462541571 18062354136381606693812357)
              ·
                refine ⟨3386691400571551255089817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18062354136381606693812357 3386691400571551255089817)
                ·
                  refine ⟨2540018550428663441317363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3386691400571551255089817 2540018550428663441317363)
                  ·
                    refine ⟨3810027825642995161976045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2540018550428663441317363 3810027825642995161976045)
                    ·
                      refine ⟨1428760434616123185741017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3810027825642995161976045 1428760434616123185741017)
                      ·
                        rfl

theorem cell23_2782501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_2782501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782501 prefixEnd_2782501 := by exact prefixLift 2782501
  have htrace : WordTrace (prefixWord ++ tailWord_2782501) baseStart_2782501 baseEnd_2782501 := by
    simpa [prefixWord, tailWord_2782501, baseEnd_2782501] using wordTrace_append hprefix tailTrace_2782501
  have hstable : (prefixWord ++ tailWord_2782501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782501).length < 2 ^ (prefixWord ++ tailWord_2782501).sum := by decide
  have hdescent : baseEnd_2782501 < baseStart_2782501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782517 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 1, 8]
def baseStart_2782517 : Nat := 118140960795 + 2782517 * 2 ^ 59
def prefixEnd_2782517 : Nat := 4983230072969 + 3 ^ 40 * 2782517 * 2
def baseEnd_2782517 : Nat := 476256216768865041046981

theorem tailTrace_2782517 : CollatzResearch.WordTrace tailWord_2782517 prefixEnd_2782517 476256216768865041046981 := by
  unfold tailWord_2782517
  simp only [CollatzResearch.WordTrace]
  refine ⟨101486732460423599914825805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67657821640282399943217203 101486732460423599914825805)
  ·
    refine ⟨38057524672658849968059677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101486732460423599914825805 38057524672658849968059677)
    ·
      refine ⟨14271571752247068738022379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38057524672658849968059677 14271571752247068738022379)
      ·
        refine ⟨21407357628370603107033569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14271571752247068738022379 21407357628370603107033569)
        ·
          refine ⟨16055518221277952330275177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21407357628370603107033569 16055518221277952330275177)
          ·
            refine ⟨12041638665958464247706383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16055518221277952330275177 12041638665958464247706383)
            ·
              refine ⟨18062457998937696371559575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12041638665958464247706383 18062457998937696371559575)
              ·
                refine ⟨27093686998406544557339363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18062457998937696371559575 27093686998406544557339363)
                ·
                  refine ⟨40640530497609816836009045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27093686998406544557339363 40640530497609816836009045)
                  ·
                    refine ⟨476256216768865041046981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40640530497609816836009045 476256216768865041046981)
                    ·
                      rfl

theorem cell23_2782517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_2782517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782517 prefixEnd_2782517 := by exact prefixLift 2782517
  have htrace : WordTrace (prefixWord ++ tailWord_2782517) baseStart_2782517 baseEnd_2782517 := by
    simpa [prefixWord, tailWord_2782517, baseEnd_2782517] using wordTrace_append hprefix tailTrace_2782517
  have hstable : (prefixWord ++ tailWord_2782517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782517).length < 2 ^ (prefixWord ++ tailWord_2782517).sum := by decide
  have hdescent : baseEnd_2782517 < baseStart_2782517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782564 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 7]
def baseStart_2782564 : Nat := 118140960795 + 2782564 * 2 ^ 59
def prefixEnd_2782564 : Nat := 4983230072969 + 3 ^ 40 * 2782564 * 2
def baseEnd_2782564 : Nat := 158754753766372937694803

theorem tailTrace_2782564 : CollatzResearch.WordTrace tailWord_2782564 prefixEnd_2782564 158754753766372937694803 := by
  unfold tailWord_2782564
  simp only [CollatzResearch.WordTrace]
  refine ⟨50744223345626663470893373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67658964460835551294524497 50744223345626663470893373)
  ·
    refine ⟨19029083754609998801585015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50744223345626663470893373 19029083754609998801585015)
    ·
      refine ⟨28543625631914998202377523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19029083754609998801585015 28543625631914998202377523)
      ·
        refine ⟨42815438447872497303566285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28543625631914998202377523 42815438447872497303566285)
        ·
          refine ⟨16055789417952186488837357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42815438447872497303566285 16055789417952186488837357)
          ·
            refine ⟨6020921031732069933314009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16055789417952186488837357 6020921031732069933314009)
            ·
              refine ⟨4515690773799052449985507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6020921031732069933314009 4515690773799052449985507)
              ·
                refine ⟨6773536160698578674978261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4515690773799052449985507 6773536160698578674978261)
                ·
                  refine ⟨158754753766372937694803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6773536160698578674978261 158754753766372937694803)
                  ·
                    rfl

theorem cell23_2782564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_2782564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782564 prefixEnd_2782564 := by exact prefixLift 2782564
  have htrace : WordTrace (prefixWord ++ tailWord_2782564) baseStart_2782564 baseEnd_2782564 := by
    simpa [prefixWord, tailWord_2782564, baseEnd_2782564] using wordTrace_append hprefix tailTrace_2782564
  have hstable : (prefixWord ++ tailWord_2782564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782564).length < 2 ^ (prefixWord ++ tailWord_2782564).sum := by decide
  have hdescent : baseEnd_2782564 < baseStart_2782564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782577 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 1, 7]
def baseStart_2782577 : Nat := 118140960795 + 2782577 * 2 ^ 59
def prefixEnd_2782577 : Nat := 4983230072969 + 3 ^ 40 * 2782577 * 2
def baseEnd_2782577 : Nat := 476266486381954962796889

theorem tailTrace_2782577 : CollatzResearch.WordTrace tailWord_2782577 prefixEnd_2782577 476266486381954962796889 := by
  unfold tailWord_2782577
  simp only [CollatzResearch.WordTrace]
  refine ⟨101488920840206230162009985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67659280560137486774673323 101488920840206230162009985)
  ·
    refine ⟨76116690630154672621507489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101488920840206230162009985 76116690630154672621507489)
    ·
      refine ⟨57087517972616004466130617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76116690630154672621507489 57087517972616004466130617)
      ·
        refine ⟨42815638479462003349597963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57087517972616004466130617 42815638479462003349597963)
        ·
          refine ⟨64223457719193005024396945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42815638479462003349597963 64223457719193005024396945)
          ·
            refine ⟨48167593289394753768297709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64223457719193005024396945 48167593289394753768297709)
            ·
              refine ⟨18062847483523032663111641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48167593289394753768297709 18062847483523032663111641)
              ·
                refine ⟨13547135612642274497333731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18062847483523032663111641 13547135612642274497333731)
                ·
                  refine ⟨20320703418963411746000597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13547135612642274497333731 20320703418963411746000597)
                  ·
                    refine ⟨476266486381954962796889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20320703418963411746000597 476266486381954962796889)
                    ·
                      rfl

theorem cell23_2782577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_2782577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782577 prefixEnd_2782577 := by exact prefixLift 2782577
  have htrace : WordTrace (prefixWord ++ tailWord_2782577) baseStart_2782577 baseEnd_2782577 := by
    simpa [prefixWord, tailWord_2782577, baseEnd_2782577] using wordTrace_append hprefix tailTrace_2782577
  have hstable : (prefixWord ++ tailWord_2782577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782577).length < 2 ^ (prefixWord ++ tailWord_2782577).sum := by decide
  have hdescent : baseEnd_2782577 < baseStart_2782577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782631 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_2782631 : Nat := 118140960795 + 2782631 * 2 ^ 59
def prefixEnd_2782631 : Nat := 4983230072969 + 3 ^ 40 * 2782631 * 2
def baseEnd_2782631 : Nat := 1428827187101207677115419

theorem tailTrace_2782631 : CollatzResearch.WordTrace tailWord_2782631 prefixEnd_2782631 1428827187101207677115419 := by
  unfold tailWord_2782631
  simp only [CollatzResearch.WordTrace]
  refine ⟨101490890382010597384475747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67660593588007064922983831 101490890382010597384475747)
  ·
    refine ⟨152236335573015896076713621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101490890382010597384475747 152236335573015896076713621)
    ·
      refine ⟨7136078229985120128595951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 152236335573015896076713621 7136078229985120128595951)
      ·
        refine ⟨10704117344977680192893927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7136078229985120128595951 10704117344977680192893927)
        ·
          refine ⟨16056176017466520289340891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10704117344977680192893927 16056176017466520289340891)
          ·
            refine ⟨24084264026199780434011337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16056176017466520289340891 24084264026199780434011337)
            ·
              refine ⟨18063198019649835325508503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24084264026199780434011337 18063198019649835325508503)
              ·
                refine ⟨27094797029474752988262755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18063198019649835325508503 27094797029474752988262755)
                ·
                  refine ⟨40642195544212129482394133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27094797029474752988262755 40642195544212129482394133)
                  ·
                    refine ⟨1905102916134943569487225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40642195544212129482394133 1905102916134943569487225)
                    ·
                      refine ⟨1428827187101207677115419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1905102916134943569487225 1428827187101207677115419)
                      ·
                        rfl

theorem cell23_2782631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_2782631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782631 prefixEnd_2782631 := by exact prefixLift 2782631
  have htrace : WordTrace (prefixWord ++ tailWord_2782631) baseStart_2782631 baseEnd_2782631 := by
    simpa [prefixWord, tailWord_2782631, baseEnd_2782631] using wordTrace_append hprefix tailTrace_2782631
  have hstable : (prefixWord ++ tailWord_2782631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782631).length < 2 ^ (prefixWord ++ tailWord_2782631).sum := by decide
  have hdescent : baseEnd_2782631 < baseStart_2782631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782714 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 1, 6]
def baseStart_2782714 : Nat := 118140960795 + 2782714 * 2 ^ 59
def prefixEnd_2782714 : Nat := 4983230072969 + 3 ^ 40 * 2782714 * 2
def baseEnd_2782714 : Nat := 476289935331843617459179

theorem tailTrace_2782714 : CollatzResearch.WordTrace tailWord_2782714 prefixEnd_2782714 476289935331843617459179 := by
  unfold tailWord_2782714
  simp only [CollatzResearch.WordTrace]
  refine ⟨25373479410177475639936799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67662611760473268373164797 25373479410177475639936799)
  ·
    refine ⟨38060219115266213459905199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25373479410177475639936799 38060219115266213459905199)
    ·
      refine ⟨57090328672899320189857799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38060219115266213459905199 57090328672899320189857799)
      ·
        refine ⟨85635493009348980284786699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57090328672899320189857799 85635493009348980284786699)
        ·
          refine ⟨128453239514023470427180049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85635493009348980284786699 128453239514023470427180049)
          ·
            refine ⟨96339929635517602820385037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128453239514023470427180049 96339929635517602820385037)
            ·
              refine ⟨36127473613319101057644389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96339929635517602820385037 36127473613319101057644389)
              ·
                refine ⟨6773901302497331448308323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36127473613319101057644389 6773901302497331448308323)
                ·
                  refine ⟨10160851953745997172462485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6773901302497331448308323 10160851953745997172462485)
                  ·
                    refine ⟨476289935331843617459179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10160851953745997172462485 476289935331843617459179)
                    ·
                      rfl

theorem cell23_2782714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_2782714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782714 prefixEnd_2782714 := by exact prefixLift 2782714
  have htrace : WordTrace (prefixWord ++ tailWord_2782714) baseStart_2782714 baseEnd_2782714 := by
    simpa [prefixWord, tailWord_2782714, baseEnd_2782714] using wordTrace_append hprefix tailTrace_2782714
  have hstable : (prefixWord ++ tailWord_2782714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782714).length < 2 ^ (prefixWord ++ tailWord_2782714).sum := by decide
  have hdescent : baseEnd_2782714 < baseStart_2782714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782741 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_2782741 : Nat := 118140960795 + 2782741 * 2 ^ 59
def prefixEnd_2782741 : Nat := 4983230072969 + 3 ^ 40 * 2782741 * 2
def baseEnd_2782741 : Nat := 1428883669973202246739913

theorem tailTrace_2782741 : CollatzResearch.WordTrace tailWord_2782741 prefixEnd_2782741 1428883669973202246739913 := by
  unfold tailWord_2782741
  simp only [CollatzResearch.WordTrace]
  refine ⟨101494902411612086170980077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67663268274408057447320051 101494902411612086170980077)
  ·
    refine ⟨38060588404354532314117529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101494902411612086170980077 38060588404354532314117529)
    ·
      refine ⟨28545441303265899235588147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38060588404354532314117529 28545441303265899235588147)
      ·
        refine ⟨42818161954898848853382221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28545441303265899235588147 42818161954898848853382221)
        ·
          refine ⟨16056810733087068320018333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42818161954898848853382221 16056810733087068320018333)
          ·
            refine ⟨6021304024907650620006875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16056810733087068320018333 6021304024907650620006875)
            ·
              refine ⟨9031956037361475930010313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6021304024907650620006875 9031956037361475930010313)
              ·
                refine ⟨6773967028021106947507735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9031956037361475930010313 6773967028021106947507735)
                ·
                  refine ⟨10160950542031660421261603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6773967028021106947507735 10160950542031660421261603)
                  ·
                    refine ⟨15241425813047490631892405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10160950542031660421261603 15241425813047490631892405)
                    ·
                      refine ⟨1428883669973202246739913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15241425813047490631892405 1428883669973202246739913)
                      ·
                        rfl

theorem cell23_2782741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_2782741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782741 prefixEnd_2782741 := by exact prefixLift 2782741
  have htrace : WordTrace (prefixWord ++ tailWord_2782741) baseStart_2782741 baseEnd_2782741 := by
    simpa [prefixWord, tailWord_2782741, baseEnd_2782741] using wordTrace_append hprefix tailTrace_2782741
  have hstable : (prefixWord ++ tailWord_2782741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782741).length < 2 ^ (prefixWord ++ tailWord_2782741).sum := by decide
  have hdescent : baseEnd_2782741 < baseStart_2782741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782751 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 4]
def baseStart_2782751 : Nat := 118140960795 + 2782751 * 2 ^ 59
def prefixEnd_2782751 : Nat := 4983230072969 + 3 ^ 40 * 2782751 * 2
def baseEnd_2782751 : Nat := 1428888804779747207614867

theorem tailTrace_2782751 : CollatzResearch.WordTrace tailWord_2782751 prefixEnd_2782751 1428888804779747207614867 := by
  unfold tailWord_2782751
  simp only [CollatzResearch.WordTrace]
  refine ⟨101495267141575857878844107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67663511427717238585896071 101495267141575857878844107)
  ·
    refine ⟨152242900712363786818266161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101495267141575857878844107 152242900712363786818266161)
    ·
      refine ⟨114182175534272840113699621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152242900712363786818266161 114182175534272840113699621)
      ·
        refine ⟨21409157912676157521318679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114182175534272840113699621 21409157912676157521318679)
        ·
          refine ⟨32113736869014236281978019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21409157912676157521318679 32113736869014236281978019)
          ·
            refine ⟨48170605303521354422967029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32113736869014236281978019 48170605303521354422967029)
            ·
              refine ⟨4515994247205126977153159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48170605303521354422967029 4515994247205126977153159)
              ·
                refine ⟨6773991370807690465729739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4515994247205126977153159 6773991370807690465729739)
                ·
                  refine ⟨10160987056211535698594609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6773991370807690465729739 10160987056211535698594609)
                  ·
                    refine ⟨7620740292158651773945957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10160987056211535698594609 7620740292158651773945957)
                    ·
                      refine ⟨1428888804779747207614867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7620740292158651773945957 1428888804779747207614867)
                      ·
                        rfl

theorem cell23_2782751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_2782751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782751 prefixEnd_2782751 := by exact prefixLift 2782751
  have htrace : WordTrace (prefixWord ++ tailWord_2782751) baseStart_2782751 baseEnd_2782751 := by
    simpa [prefixWord, tailWord_2782751, baseEnd_2782751] using wordTrace_append hprefix tailTrace_2782751
  have hstable : (prefixWord ++ tailWord_2782751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782751).length < 2 ^ (prefixWord ++ tailWord_2782751).sum := by decide
  have hdescent : baseEnd_2782751 < baseStart_2782751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782784 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 5]
def baseStart_2782784 : Nat := 118140960795 + 2782784 * 2 ^ 59
def prefixEnd_2782784 : Nat := 4983230072969 + 3 ^ 40 * 2782784 * 2
def baseEnd_2782784 : Nat := 1428905749641345578502215

theorem tailTrace_2782784 : CollatzResearch.WordTrace tailWord_2782784 prefixEnd_2782784 1428905749641345578502215 := by
  unfold tailWord_2782784
  simp only [CollatzResearch.WordTrace]
  refine ⟨50748235375228152257397703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67664313833637536343196937 50748235375228152257397703)
  ·
    refine ⟨76122353062842228386096555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50748235375228152257397703 76122353062842228386096555)
    ·
      refine ⟨114183529594263342579144833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76122353062842228386096555 114183529594263342579144833)
      ·
        refine ⟨85637647195697506934358625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114183529594263342579144833 85637647195697506934358625)
        ·
          refine ⟨64228235396773130200768969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85637647195697506934358625 64228235396773130200768969)
          ·
            refine ⟨48171176547579847650576727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64228235396773130200768969 48171176547579847650576727)
            ·
              refine ⟨72256764821369771475865091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48171176547579847650576727 72256764821369771475865091)
              ·
                refine ⟨108385147232054657213797637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72256764821369771475865091 108385147232054657213797637)
                ·
                  refine ⟨20322215106010248227587057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108385147232054657213797637 20322215106010248227587057)
                  ·
                    refine ⟨15241661329507686170690293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20322215106010248227587057 15241661329507686170690293)
                    ·
                      refine ⟨1428905749641345578502215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15241661329507686170690293 1428905749641345578502215)
                      ·
                        rfl

theorem cell23_2782784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_2782784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782784 prefixEnd_2782784 := by exact prefixLift 2782784
  have htrace : WordTrace (prefixWord ++ tailWord_2782784) baseStart_2782784 baseEnd_2782784 := by
    simpa [prefixWord, tailWord_2782784, baseEnd_2782784] using wordTrace_append hprefix tailTrace_2782784
  have hstable : (prefixWord ++ tailWord_2782784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782784).length < 2 ^ (prefixWord ++ tailWord_2782784).sum := by decide
  have hdescent : baseEnd_2782784 < baseStart_2782784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782798 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2]
def baseStart_2782798 : Nat := 118140960795 + 2782798 * 2 ^ 59
def prefixEnd_2782798 : Nat := 4983230072969 + 3 ^ 40 * 2782798 * 2
def baseEnd_2782798 : Nat := 1428912938370508523727151

theorem tailTrace_2782798 : CollatzResearch.WordTrace tailWord_2782798 prefixEnd_2782798 1428912938370508523727151 := by
  unfold tailWord_2782798
  simp only [CollatzResearch.WordTrace]
  refine ⟨12687122671550698113225631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67664654248270389937203365 12687122671550698113225631)
  ·
    refine ⟨19030684007326047169838447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12687122671550698113225631 19030684007326047169838447)
    ·
      refine ⟨28546026010989070754757671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19030684007326047169838447 28546026010989070754757671)
      ·
        refine ⟨42819039016483606132136507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28546026010989070754757671 42819039016483606132136507)
        ·
          refine ⟨64228558524725409198204761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42819039016483606132136507 64228558524725409198204761)
          ·
            refine ⟨48171418893544056898653571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64228558524725409198204761 48171418893544056898653571)
            ·
              refine ⟨72257128340316085347980357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48171418893544056898653571 72257128340316085347980357)
              ·
                refine ⟨13548211563809266002746317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72257128340316085347980357 13548211563809266002746317)
                ·
                  refine ⟨5080579336428474751029869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13548211563809266002746317 5080579336428474751029869)
                  ·
                    refine ⟨1905217251160678031636201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5080579336428474751029869 1905217251160678031636201)
                    ·
                      refine ⟨1428912938370508523727151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1905217251160678031636201 1428912938370508523727151)
                      ·
                        rfl

theorem cell23_2782798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_2782798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782798 prefixEnd_2782798 := by exact prefixLift 2782798
  have htrace : WordTrace (prefixWord ++ tailWord_2782798) baseStart_2782798 baseEnd_2782798 := by
    simpa [prefixWord, tailWord_2782798, baseEnd_2782798] using wordTrace_append hprefix tailTrace_2782798
  have hstable : (prefixWord ++ tailWord_2782798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782798).length < 2 ^ (prefixWord ++ tailWord_2782798).sum := by decide
  have hdescent : baseEnd_2782798 < baseStart_2782798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782806 : List Nat := [5, 2, 2, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_2782806 : Nat := 118140960795 + 2782806 * 2 ^ 59
def prefixEnd_2782806 : Nat := 4983230072969 + 3 ^ 40 * 2782806 * 2
def baseEnd_2782806 : Nat := 1428917046215744492427115

theorem tailTrace_2782806 : CollatzResearch.WordTrace tailWord_2782806 prefixEnd_2782806 1428917046215744492427115 := by
  unfold tailWord_2782806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6343579572273537642006017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67664848770917734848064181 6343579572273537642006017)
  ·
    refine ⟨4757684679205153231504513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6343579572273537642006017 4757684679205153231504513)
    ·
      refine ⟨3568263509403864923628385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4757684679205153231504513 3568263509403864923628385)
      ·
        refine ⟨2676197632052898692721289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3568263509403864923628385 2676197632052898692721289)
        ·
          refine ⟨2007148224039674019540967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2676197632052898692721289 2007148224039674019540967)
          ·
            refine ⟨3010722336059511029311451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2007148224039674019540967 3010722336059511029311451)
            ·
              refine ⟨4516083504089266543967177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3010722336059511029311451 4516083504089266543967177)
              ·
                refine ⟨3387062628066949907975383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4516083504089266543967177 3387062628066949907975383)
                ·
                  refine ⟨5080593942100424861963075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3387062628066949907975383 5080593942100424861963075)
                  ·
                    refine ⟨7620890913150637292944613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5080593942100424861963075 7620890913150637292944613)
                    ·
                      refine ⟨1428917046215744492427115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7620890913150637292944613 1428917046215744492427115)
                      ·
                        rfl

theorem cell23_2782806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_2782806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782806 prefixEnd_2782806 := by exact prefixLift 2782806
  have htrace : WordTrace (prefixWord ++ tailWord_2782806) baseStart_2782806 baseEnd_2782806 := by
    simpa [prefixWord, tailWord_2782806, baseEnd_2782806] using wordTrace_append hprefix tailTrace_2782806
  have hstable : (prefixWord ++ tailWord_2782806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782806).length < 2 ^ (prefixWord ++ tailWord_2782806).sum := by decide
  have hdescent : baseEnd_2782806 < baseStart_2782806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782832 : List Nat := [2, 1, 1, 1, 6, 2, 3, 1, 1, 3, 2]
def baseStart_2782832 : Nat := 118140960795 + 2782832 * 2 ^ 59
def prefixEnd_2782832 : Nat := 4983230072969 + 3 ^ 40 * 2782832 * 2
def baseEnd_2782832 : Nat := 1428930396712761390701995

theorem tailTrace_2782832 : CollatzResearch.WordTrace tailWord_2782832 prefixEnd_2782832 1428930396712761390701995 := by
  unfold tailWord_2782832
  simp only [CollatzResearch.WordTrace]
  refine ⟨50749110727141204356271375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67665480969521605808361833 50749110727141204356271375)
  ·
    refine ⟨76123666090711806534407063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50749110727141204356271375 76123666090711806534407063)
    ·
      refine ⟨114185499136067709801610595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76123666090711806534407063 114185499136067709801610595)
      ·
        refine ⟨171278248704101564702415893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114185499136067709801610595 171278248704101564702415893)
        ·
          refine ⟨8028667908004760845425745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 171278248704101564702415893 8028667908004760845425745)
          ·
            refine ⟨6021500931003570634069309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8028667908004760845425745 6021500931003570634069309)
            ·
              refine ⟨2258062849126338987775991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6021500931003570634069309 2258062849126338987775991)
              ·
                refine ⟨3387094273689508481663987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2258062849126338987775991 3387094273689508481663987)
                ·
                  refine ⟨5080641410534262722495981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3387094273689508481663987 5080641410534262722495981)
                  ·
                    refine ⟨1905240528950348520935993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5080641410534262722495981 1905240528950348520935993)
                    ·
                      refine ⟨1428930396712761390701995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1905240528950348520935993 1428930396712761390701995)
                      ·
                        rfl

theorem cell23_2782832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 1, 3, 2].length) (baseStart_2782832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782832 prefixEnd_2782832 := by exact prefixLift 2782832
  have htrace : WordTrace (prefixWord ++ tailWord_2782832) baseStart_2782832 baseEnd_2782832 := by
    simpa [prefixWord, tailWord_2782832, baseEnd_2782832] using wordTrace_append hprefix tailTrace_2782832
  have hstable : (prefixWord ++ tailWord_2782832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782832).length < 2 ^ (prefixWord ++ tailWord_2782832).sum := by decide
  have hdescent : baseEnd_2782832 < baseStart_2782832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782841 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 2, 2, 4]
def baseStart_2782841 : Nat := 118140960795 + 2782841 * 2 ^ 59
def prefixEnd_2782841 : Nat := 4983230072969 + 3 ^ 40 * 2782841 * 2
def baseEnd_2782841 : Nat := 1428935018038651855489453

theorem tailTrace_2782841 : CollatzResearch.WordTrace tailWord_2782841 prefixEnd_2782841 1428935018038651855489453 := by
  unfold tailWord_2782841
  simp only [CollatzResearch.WordTrace]
  refine ⟨101498549711249803249620377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67665699807499868833080251 101498549711249803249620377)
  ·
    refine ⟨76123912283437352437215283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101498549711249803249620377 76123912283437352437215283)
    ·
      refine ⟨114185868425156028655822925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76123912283437352437215283 114185868425156028655822925)
      ·
        refine ⟨42819700659433510745933597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114185868425156028655822925 42819700659433510745933597)
        ·
          refine ⟨16057387747287566529725099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42819700659433510745933597 16057387747287566529725099)
          ·
            refine ⟨24086081620931349794587649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16057387747287566529725099 24086081620931349794587649)
            ·
              refine ⟨18064561215698512345940737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24086081620931349794587649 18064561215698512345940737)
              ·
                refine ⟨13548420911773884259455553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18064561215698512345940737 13548420911773884259455553)
                ·
                  refine ⟨10161315683830413194591665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13548420911773884259455553 10161315683830413194591665)
                  ·
                    refine ⟨7620986762872809895943749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10161315683830413194591665 7620986762872809895943749)
                    ·
                      refine ⟨1428935018038651855489453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7620986762872809895943749 1428935018038651855489453)
                      ·
                        rfl

theorem cell23_2782841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_2782841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782841 prefixEnd_2782841 := by exact prefixLift 2782841
  have htrace : WordTrace (prefixWord ++ tailWord_2782841) baseStart_2782841 baseEnd_2782841 := by
    simpa [prefixWord, tailWord_2782841, baseEnd_2782841] using wordTrace_append hprefix tailTrace_2782841
  have hstable : (prefixWord ++ tailWord_2782841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782841).length < 2 ^ (prefixWord ++ tailWord_2782841).sum := by decide
  have hdescent : baseEnd_2782841 < baseStart_2782841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782858 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_2782858 : Nat := 118140960795 + 2782858 * 2 ^ 59
def prefixEnd_2782858 : Nat := 4983230072969 + 3 ^ 40 * 2782858 * 2
def baseEnd_2782858 : Nat := 1428943747209778288976875

theorem tailTrace_2782858 : CollatzResearch.WordTrace tailWord_2782858 prefixEnd_2782858 1428943747209778288976875 := by
  unfold tailWord_2782858
  simp only [CollatzResearch.WordTrace]
  refine ⟨25374792438047053788247307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67666113168125476768659485 25374792438047053788247307)
  ·
    refine ⟨38062188657070580682370961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25374792438047053788247307 38062188657070580682370961)
    ·
      refine ⟨28546641492802935511778221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38062188657070580682370961 28546641492802935511778221)
      ·
        refine ⟨10704990559801100816916833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28546641492802935511778221 10704990559801100816916833)
        ·
          refine ⟨8028742919850825612687625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10704990559801100816916833 8028742919850825612687625)
          ·
            refine ⟨6021557189888119209515719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8028742919850825612687625 6021557189888119209515719)
            ·
              refine ⟨9032335784832178814273579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6021557189888119209515719 9032335784832178814273579)
              ·
                refine ⟨13548503677248268221410369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9032335784832178814273579 13548503677248268221410369)
                ·
                  refine ⟨10161377757936201166057777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13548503677248268221410369 10161377757936201166057777)
                  ·
                    refine ⟨7621033318452150874543333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10161377757936201166057777 7621033318452150874543333)
                    ·
                      refine ⟨1428943747209778288976875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7621033318452150874543333 1428943747209778288976875)
                      ·
                        rfl

theorem cell23_2782858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_2782858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782858 prefixEnd_2782858 := by exact prefixLift 2782858
  have htrace : WordTrace (prefixWord ++ tailWord_2782858) baseStart_2782858 baseEnd_2782858 := by
    simpa [prefixWord, tailWord_2782858, baseEnd_2782858] using wordTrace_append hprefix tailTrace_2782858
  have hstable : (prefixWord ++ tailWord_2782858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782858).length < 2 ^ (prefixWord ++ tailWord_2782858).sum := by decide
  have hdescent : baseEnd_2782858 < baseStart_2782858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782862 : List Nat := [4, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2]
def baseStart_2782862 : Nat := 118140960795 + 2782862 * 2 ^ 59
def prefixEnd_2782862 : Nat := 4983230072969 + 3 ^ 40 * 2782862 * 2
def baseEnd_2782862 : Nat := 1428945801132396273326857

theorem tailTrace_2782862 : CollatzResearch.WordTrace tailWord_2782862 prefixEnd_2782862 1428945801132396273326857 := by
  unfold tailWord_2782862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12687414455521715479516855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67666210429449149224089893 12687414455521715479516855)
  ·
    refine ⟨19031121683282573219275283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12687414455521715479516855 19031121683282573219275283)
    ·
      refine ⟨28546682524923859828912925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19031121683282573219275283 28546682524923859828912925)
      ·
        refine ⟨10705005946846447435842347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28546682524923859828912925 10705005946846447435842347)
        ·
          refine ⟨16057508920269671153763521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10705005946846447435842347 16057508920269671153763521)
          ·
            refine ⟨12043131690202253365322641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16057508920269671153763521 12043131690202253365322641)
            ·
              refine ⟨9032348767651690023991981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12043131690202253365322641 9032348767651690023991981)
              ·
                refine ⟨3387130787869383758996993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9032348767651690023991981 3387130787869383758996993)
                ·
                  refine ⟨2540348090902037819247745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3387130787869383758996993 2540348090902037819247745)
                  ·
                    refine ⟨1905261068176528364435809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2540348090902037819247745 1905261068176528364435809)
                    ·
                      refine ⟨1428945801132396273326857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1905261068176528364435809 1428945801132396273326857)
                      ·
                        rfl

theorem cell23_2782862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_2782862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782862 prefixEnd_2782862 := by exact prefixLift 2782862
  have htrace : WordTrace (prefixWord ++ tailWord_2782862) baseStart_2782862 baseEnd_2782862 := by
    simpa [prefixWord, tailWord_2782862, baseEnd_2782862] using wordTrace_append hprefix tailTrace_2782862
  have hstable : (prefixWord ++ tailWord_2782862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782862).length < 2 ^ (prefixWord ++ tailWord_2782862).sum := by decide
  have hdescent : baseEnd_2782862 < baseStart_2782862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782902 : List Nat := [5, 1, 3, 1, 1, 1, 2, 4, 5]
def baseStart_2782902 : Nat := 118140960795 + 2782902 * 2 ^ 59
def prefixEnd_2782902 : Nat := 4983230072969 + 3 ^ 40 * 2782902 * 2
def baseEnd_2782902 : Nat := 158774037817619568536297

theorem tailTrace_2782902 : CollatzResearch.WordTrace tailWord_2782902 prefixEnd_2782902 158774037817619568536297 := by
  unfold tailWord_2782902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6343798410251800666724435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67667183042685873778393973 6343798410251800666724435)
  ·
    refine ⟨9515697615377701000086653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6343798410251800666724435 9515697615377701000086653)
    ·
      refine ⟨3568386605766637875032495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9515697615377701000086653 3568386605766637875032495)
      ·
        refine ⟨5352579908649956812548743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3568386605766637875032495 5352579908649956812548743)
        ·
          refine ⟨8028869862974935218823115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5352579908649956812548743 8028869862974935218823115)
          ·
            refine ⟨12043304794462402828234673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8028869862974935218823115 12043304794462402828234673)
            ·
              refine ⟨9032478595846802121176005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12043304794462402828234673 9032478595846802121176005)
              ·
                refine ⟨1693589736721275397720501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9032478595846802121176005 1693589736721275397720501)
                ·
                  refine ⟨158774037817619568536297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1693589736721275397720501 158774037817619568536297)
                  ·
                    rfl

theorem cell23_2782902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_2782902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782902 prefixEnd_2782902 := by exact prefixLift 2782902
  have htrace : WordTrace (prefixWord ++ tailWord_2782902) baseStart_2782902 baseEnd_2782902 := by
    simpa [prefixWord, tailWord_2782902, baseEnd_2782902] using wordTrace_append hprefix tailTrace_2782902
  have hstable : (prefixWord ++ tailWord_2782902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782902).length < 2 ^ (prefixWord ++ tailWord_2782902).sum := by decide
  have hdescent : baseEnd_2782902 < baseStart_2782902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782938 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3]
def baseStart_2782938 : Nat := 118140960795 + 2782938 * 2 ^ 59
def prefixEnd_2782938 : Nat := 4983230072969 + 3 ^ 40 * 2782938 * 2
def baseEnd_2782938 : Nat := 1428984825662137975976507

theorem tailTrace_2782938 : CollatzResearch.WordTrace tailWord_2782938 prefixEnd_2782938 1428984825662137975976507 := by
  unfold tailWord_2782938
  simp only [CollatzResearch.WordTrace]
  refine ⟨25375521897974597203975367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67668058394598925877267645 25375521897974597203975367)
  ·
    refine ⟨38063282846961895805963051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25375521897974597203975367 38063282846961895805963051)
    ·
      refine ⟨57094924270442843708944577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38063282846961895805963051 57094924270442843708944577)
      ·
        refine ⟨42821193202832132781708433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57094924270442843708944577 42821193202832132781708433)
        ·
          refine ⟨32115894902124099586281325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42821193202832132781708433 32115894902124099586281325)
          ·
            refine ⟨12043460588296537344855497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32115894902124099586281325 12043460588296537344855497)
            ·
              refine ⟨9032595441222403008641623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12043460588296537344855497 9032595441222403008641623)
              ·
                refine ⟨13548893161833604512962435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9032595441222403008641623 13548893161833604512962435)
                ·
                  refine ⟨20323339742750406769443653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13548893161833604512962435 20323339742750406769443653)
                  ·
                    refine ⟨3810626201765701269270685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20323339742750406769443653 3810626201765701269270685)
                    ·
                      refine ⟨1428984825662137975976507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3810626201765701269270685 1428984825662137975976507)
                      ·
                        rfl

theorem cell23_2782938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_2782938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782938 prefixEnd_2782938 := by exact prefixLift 2782938
  have htrace : WordTrace (prefixWord ++ tailWord_2782938) baseStart_2782938 baseEnd_2782938 := by
    simpa [prefixWord, tailWord_2782938, baseEnd_2782938] using wordTrace_append hprefix tailTrace_2782938
  have hstable : (prefixWord ++ tailWord_2782938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782938).length < 2 ^ (prefixWord ++ tailWord_2782938).sum := by decide
  have hdescent : baseEnd_2782938 < baseStart_2782938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782958 : List Nat := [4, 1, 2, 1, 1, 2, 2, 4, 6]
def baseStart_2782958 : Nat := 118140960795 + 2782958 * 2 ^ 59
def prefixEnd_2782958 : Nat := 4983230072969 + 3 ^ 40 * 2782958 * 2
def baseEnd_2782958 : Nat := 158777232808358655302935

theorem tailTrace_2782958 : CollatzResearch.WordTrace tailWord_2782958 prefixEnd_2782958 158777232808358655302935 := by
  unfold tailWord_2782958
  simp only [CollatzResearch.WordTrace]
  refine ⟨12687852131478241528953691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67668544701217288154419685 12687852131478241528953691)
  ·
    refine ⟨19031778197217362293430537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12687852131478241528953691 19031778197217362293430537)
    ·
      refine ⟨14273833647913021720072903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19031778197217362293430537 14273833647913021720072903)
      ·
        refine ⟨21410750471869532580109355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14273833647913021720072903 21410750471869532580109355)
        ·
          refine ⟨32116125707804298870164033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21410750471869532580109355 32116125707804298870164033)
          ·
            refine ⟨24087094280853224152623025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32116125707804298870164033 24087094280853224152623025)
            ·
              refine ⟨18065320710639918114467269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24087094280853224152623025 18065320710639918114467269)
              ·
                refine ⟨3387247633244984646462613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18065320710639918114467269 3387247633244984646462613)
                ·
                  refine ⟨158777232808358655302935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3387247633244984646462613 158777232808358655302935)
                  ·
                    rfl

theorem cell23_2782958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_2782958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2782958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2782958 prefixEnd_2782958 := by exact prefixLift 2782958
  have htrace : WordTrace (prefixWord ++ tailWord_2782958) baseStart_2782958 baseEnd_2782958 := by
    simpa [prefixWord, tailWord_2782958, baseEnd_2782958] using wordTrace_append hprefix tailTrace_2782958
  have hstable : (prefixWord ++ tailWord_2782958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782958).length < 2 ^ (prefixWord ++ tailWord_2782958).sum := by decide
  have hdescent : baseEnd_2782958 < baseStart_2782958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783012 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 2, 3, 2]
def baseStart_2783012 : Nat := 118140960795 + 2783012 * 2 ^ 59
def prefixEnd_2783012 : Nat := 4983230072969 + 3 ^ 40 * 2783012 * 2
def baseEnd_2783012 : Nat := 1429022823230570686451167

theorem tailTrace_2783012 : CollatzResearch.WordTrace tailWord_2783012 prefixEnd_2783012 1429022823230570686451167 := by
  unfold tailWord_2783012
  simp only [CollatzResearch.WordTrace]
  refine ⟨50752393296815149727047645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67669857729086866302730193 50752393296815149727047645)
  ·
    refine ⟨19032147486305681147642867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50752393296815149727047645 19032147486305681147642867)
    ·
      refine ⟨28548221229458521721464301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19032147486305681147642867 28548221229458521721464301)
      ·
        refine ⟨10705582961046945645549113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28548221229458521721464301 10705582961046945645549113)
        ·
          refine ⟨8029187220785209234161835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10705582961046945645549113 8029187220785209234161835)
          ·
            refine ⟨12043780831177813851242753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8029187220785209234161835 12043780831177813851242753)
            ·
              refine ⟨9032835623383360388432065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12043780831177813851242753 9032835623383360388432065)
              ·
                refine ⟨6774626717537520291324049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9032835623383360388432065 6774626717537520291324049)
                ·
                  refine ⟨5080970038153140218493037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6774626717537520291324049 5080970038153140218493037)
                  ·
                    refine ⟨1905363764307427581934889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5080970038153140218493037 1905363764307427581934889)
                    ·
                      refine ⟨1429022823230570686451167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1905363764307427581934889 1429022823230570686451167)
                      ·
                        rfl

theorem cell23_2783012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_2783012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783012 prefixEnd_2783012 := by exact prefixLift 2783012
  have htrace : WordTrace (prefixWord ++ tailWord_2783012) baseStart_2783012 baseEnd_2783012 := by
    simpa [prefixWord, tailWord_2783012, baseEnd_2783012] using wordTrace_append hprefix tailTrace_2783012
  have hstable : (prefixWord ++ tailWord_2783012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783012).length < 2 ^ (prefixWord ++ tailWord_2783012).sum := by decide
  have hdescent : baseEnd_2783012 < baseStart_2783012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783031 : List Nat := [1, 1, 3, 1, 2, 1, 2, 12]
def baseStart_2783031 : Nat := 118140960795 + 2783031 * 2 ^ 59
def prefixEnd_2783031 : Nat := 4983230072969 + 3 ^ 40 * 2783031 * 2
def baseEnd_2783031 : Nat := 52927132569000226374577

theorem tailTrace_2783031 : CollatzResearch.WordTrace tailWord_2783031 prefixEnd_2783031 52927132569000226374577 := by
  unfold tailWord_2783031
  simp only [CollatzResearch.WordTrace]
  refine ⟨101505479580561465699036947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67670319720374310466024631 101505479580561465699036947)
  ·
    refine ⟨152258219370842198548555421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101505479580561465699036947 152258219370842198548555421)
    ·
      refine ⟨57096832264065824455708283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152258219370842198548555421 57096832264065824455708283)
      ·
        refine ⟨85645248396098736683562425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57096832264065824455708283 85645248396098736683562425)
        ·
          refine ⟨64233936297074052512671819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85645248396098736683562425 64233936297074052512671819)
          ·
            refine ⟨96350904445611078769007729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64233936297074052512671819 96350904445611078769007729)
            ·
              refine ⟨72263178334208309076755797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96350904445611078769007729 72263178334208309076755797)
              ·
                refine ⟨52927132569000226374577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 72263178334208309076755797 52927132569000226374577)
                ·
                  rfl

theorem cell23_2783031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 12].length) (baseStart_2783031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783031 prefixEnd_2783031 := by exact prefixLift 2783031
  have htrace : WordTrace (prefixWord ++ tailWord_2783031) baseStart_2783031 baseEnd_2783031 := by
    simpa [prefixWord, tailWord_2783031, baseEnd_2783031] using wordTrace_append hprefix tailTrace_2783031
  have hstable : (prefixWord ++ tailWord_2783031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783031).length < 2 ^ (prefixWord ++ tailWord_2783031).sum := by decide
  have hdescent : baseEnd_2783031 < baseStart_2783031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783045 : List Nat := [1, 3, 1, 1, 1, 2, 4, 4, 1, 2, 3]
def baseStart_2783045 : Nat := 118140960795 + 2783045 * 2 ^ 59
def prefixEnd_2783045 : Nat := 4983230072969 + 3 ^ 40 * 2783045 * 2
def baseEnd_2783045 : Nat := 1429039768092169057338515

theorem tailTrace_2783045 : CollatzResearch.WordTrace tailWord_2783045 prefixEnd_2783045 1429039768092169057338515 := by
  unfold tailWord_2783045
  simp only [CollatzResearch.WordTrace]
  refine ⟨101505990202510746090046589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67670660135007164060031059 101505990202510746090046589)
  ·
    refine ⟨38064746325941529783767471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101505990202510746090046589 38064746325941529783767471)
    ·
      refine ⟨57097119488912294675651207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38064746325941529783767471 57097119488912294675651207)
      ·
        refine ⟨85645679233368442013476811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57097119488912294675651207 85645679233368442013476811)
        ·
          refine ⟨128468518850052663020215217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85645679233368442013476811 128468518850052663020215217)
          ·
            refine ⟨96351389137539497265161413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128468518850052663020215217 96351389137539497265161413)
            ·
              refine ⟨18065885463288655737217765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96351389137539497265161413 18065885463288655737217765)
              ·
                refine ⟨3387353524366622950728331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18065885463288655737217765 3387353524366622950728331)
                ·
                  refine ⟨5081030286549934426092497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3387353524366622950728331 5081030286549934426092497)
                  ·
                    refine ⟨3810772714912450819569373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5081030286549934426092497 3810772714912450819569373)
                    ·
                      refine ⟨1429039768092169057338515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3810772714912450819569373 1429039768092169057338515)
                      ·
                        rfl

theorem cell23_2783045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_2783045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783045 prefixEnd_2783045 := by exact prefixLift 2783045
  have htrace : WordTrace (prefixWord ++ tailWord_2783045) baseStart_2783045 baseEnd_2783045 := by
    simpa [prefixWord, tailWord_2783045, baseEnd_2783045] using wordTrace_append hprefix tailTrace_2783045
  have hstable : (prefixWord ++ tailWord_2783045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783045).length < 2 ^ (prefixWord ++ tailWord_2783045).sum := by decide
  have hdescent : baseEnd_2783045 < baseStart_2783045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783046 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_2783046 : Nat := 118140960795 + 2783046 * 2 ^ 59
def prefixEnd_2783046 : Nat := 4983230072969 + 3 ^ 40 * 2783046 * 2
def baseEnd_2783046 : Nat := 1429040281572823553426011

theorem tailTrace_2783046 : CollatzResearch.WordTrace tailWord_2783046 prefixEnd_2783046 1429040281572823553426011 := by
  unfold tailWord_2783046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3172063333609597601901031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67670684450338082173888661 3172063333609597601901031)
  ·
    refine ⟨4758095000414396402851547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3172063333609597601901031 4758095000414396402851547)
    ·
      refine ⟨7137142500621594604277321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4758095000414396402851547 7137142500621594604277321)
      ·
        refine ⟨5352856875466195953207991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7137142500621594604277321 5352856875466195953207991)
        ·
          refine ⟨8029285313199293929811987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5352856875466195953207991 8029285313199293929811987)
          ·
            refine ⟨12043927969798940894717981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8029285313199293929811987 12043927969798940894717981)
            ·
              refine ⟨4516472988674602835519243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12043927969798940894717981 4516472988674602835519243)
              ·
                refine ⟨6774709483011904253278865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4516472988674602835519243 6774709483011904253278865)
                ·
                  refine ⟨5081032112258928189959149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6774709483011904253278865 5081032112258928189959149)
                  ·
                    refine ⟨1905387042097098071234681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5081032112258928189959149 1905387042097098071234681)
                    ·
                      refine ⟨1429040281572823553426011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1905387042097098071234681 1429040281572823553426011)
                      ·
                        rfl

theorem cell23_2783046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_2783046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783046 prefixEnd_2783046 := by exact prefixLift 2783046
  have htrace : WordTrace (prefixWord ++ tailWord_2783046) baseStart_2783046 baseEnd_2783046 := by
    simpa [prefixWord, tailWord_2783046, baseEnd_2783046] using wordTrace_append hprefix tailTrace_2783046
  have hstable : (prefixWord ++ tailWord_2783046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783046).length < 2 ^ (prefixWord ++ tailWord_2783046).sum := by decide
  have hdescent : baseEnd_2783046 < baseStart_2783046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783098 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4]
def baseStart_2783098 : Nat := 118140960795 + 2783098 * 2 ^ 59
def prefixEnd_2783098 : Nat := 4983230072969 + 3 ^ 40 * 2783098 * 2
def baseEnd_2783098 : Nat := 1429066982566857349975771

theorem tailTrace_2783098 : CollatzResearch.WordTrace tailWord_2783098 prefixEnd_2783098 1429066982566857349975771 := by
  unfold tailWord_2783098
  simp only [CollatzResearch.WordTrace]
  refine ⟨25376980817829684035431487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67671948847545824094483965 25376980817829684035431487)
  ·
    refine ⟨38065471226744526053147231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25376980817829684035431487 38065471226744526053147231)
    ·
      refine ⟨57098206840116789079720847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38065471226744526053147231 57098206840116789079720847)
      ·
        refine ⟨85647310260175183619581271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57098206840116789079720847 85647310260175183619581271)
        ·
          refine ⟨128470965390262775429371907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85647310260175183619581271 128470965390262775429371907)
          ·
            refine ⟨192706448085394163144057861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128470965390262775429371907 192706448085394163144057861)
            ·
              refine ⟨36132459016011405589510849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192706448085394163144057861 36132459016011405589510849)
              ·
                refine ⟨27099344262008554192133137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36132459016011405589510849 27099344262008554192133137)
                ·
                  refine ⟨20324508196506415644099853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27099344262008554192133137 20324508196506415644099853)
                  ·
                    refine ⟨7621690573689905866537445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20324508196506415644099853 7621690573689905866537445)
                    ·
                      refine ⟨1429066982566857349975771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7621690573689905866537445 1429066982566857349975771)
                      ·
                        rfl

theorem cell23_2783098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_2783098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783098 prefixEnd_2783098 := by exact prefixLift 2783098
  have htrace : WordTrace (prefixWord ++ tailWord_2783098) baseStart_2783098 baseEnd_2783098 := by
    simpa [prefixWord, tailWord_2783098, baseEnd_2783098] using wordTrace_append hprefix tailTrace_2783098
  have hstable : (prefixWord ++ tailWord_2783098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783098).length < 2 ^ (prefixWord ++ tailWord_2783098).sum := by decide
  have hdescent : baseEnd_2783098 < baseStart_2783098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783108 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 1, 8]
def baseStart_2783108 : Nat := 118140960795 + 2783108 * 2 ^ 59
def prefixEnd_2783108 : Nat := 4983230072969 + 3 ^ 40 * 2783108 * 2
def baseEnd_2783108 : Nat := 476357372457800770283575

theorem tailTrace_2783108 : CollatzResearch.WordTrace tailWord_2783108 prefixEnd_2783108 476357372457800770283575 := by
  unfold tailWord_2783108
  simp only [CollatzResearch.WordTrace]
  refine ⟨50754144000641253924794989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67672192000855005233059985 50754144000641253924794989)
  ·
    refine ⟨19032804000240470221798121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50754144000641253924794989 19032804000240470221798121)
    ·
      refine ⟨14274603000180352666348591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19032804000240470221798121 14274603000180352666348591)
      ·
        refine ⟨21411904500270528999522887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14274603000180352666348591 21411904500270528999522887)
        ·
          refine ⟨32117856750405793499284331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21411904500270528999522887 32117856750405793499284331)
          ·
            refine ⟨48176785125608690248926497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32117856750405793499284331 48176785125608690248926497)
            ·
              refine ⟨36132588844206517686694873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48176785125608690248926497 36132588844206517686694873)
              ·
                refine ⟨27099441633154888265021155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36132588844206517686694873 27099441633154888265021155)
                ·
                  refine ⟨40649162449732332397531733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27099441633154888265021155 40649162449732332397531733)
                  ·
                    refine ⟨476357372457800770283575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40649162449732332397531733 476357372457800770283575)
                    ·
                      rfl

theorem cell23_2783108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_2783108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783108 prefixEnd_2783108 := by exact prefixLift 2783108
  have htrace : WordTrace (prefixWord ++ tailWord_2783108) baseStart_2783108 baseEnd_2783108 := by
    simpa [prefixWord, tailWord_2783108, baseEnd_2783108] using wordTrace_append hprefix tailTrace_2783108
  have hstable : (prefixWord ++ tailWord_2783108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783108).length < 2 ^ (prefixWord ++ tailWord_2783108).sum := by decide
  have hdescent : baseEnd_2783108 < baseStart_2783108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783115 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 3, 4, 2]
def baseStart_2783115 : Nat := 118140960795 + 2783115 * 2 ^ 59
def prefixEnd_2783115 : Nat := 4983230072969 + 3 ^ 40 * 2783115 * 2
def baseEnd_2783115 : Nat := 1429075711737983783463193

theorem tailTrace_2783115 : CollatzResearch.WordTrace tailWord_2783115 prefixEnd_2783115 1429075711737983783463193 := by
  unfold tailWord_2783115
  simp only [CollatzResearch.WordTrace]
  refine ⟨101508543312257148045094799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67672362208171432030063199 101508543312257148045094799)
  ·
    refine ⟨152262814968385722067642199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101508543312257148045094799 152262814968385722067642199)
    ·
      refine ⟨228394222452578583101463299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152262814968385722067642199 228394222452578583101463299)
      ·
        refine ⟨342591333678867874652194949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228394222452578583101463299 342591333678867874652194949)
        ·
          refine ⟨64235875064787726497286553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 342591333678867874652194949 64235875064787726497286553)
          ·
            refine ⟨48176906298590794872964915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64235875064787726497286553 48176906298590794872964915)
            ·
              refine ⟨72265359447886192309447373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48176906298590794872964915 72265359447886192309447373)
              ·
                refine ⟨27099509792957322116042765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72265359447886192309447373 27099509792957322116042765)
                ·
                  refine ⟨10162316172358995793516037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27099509792957322116042765 10162316172358995793516037)
                  ·
                    refine ⟨1905434282317311711284257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10162316172358995793516037 1905434282317311711284257)
                    ·
                      refine ⟨1429075711737983783463193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1905434282317311711284257 1429075711737983783463193)
                      ·
                        rfl

theorem cell23_2783115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 4, 2].length) (baseStart_2783115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783115 prefixEnd_2783115 := by exact prefixLift 2783115
  have htrace : WordTrace (prefixWord ++ tailWord_2783115) baseStart_2783115 baseEnd_2783115 := by
    simpa [prefixWord, tailWord_2783115, baseEnd_2783115] using wordTrace_append hprefix tailTrace_2783115
  have hstable : (prefixWord ++ tailWord_2783115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783115).length < 2 ^ (prefixWord ++ tailWord_2783115).sum := by decide
  have hdescent : baseEnd_2783115 < baseStart_2783115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783189 : List Nat := [1, 3, 2, 3, 2, 1, 4, 2, 5]
def baseStart_2783189 : Nat := 118140960795 + 2783189 * 2 ^ 59
def prefixEnd_2783189 : Nat := 4983230072969 + 3 ^ 40 * 2783189 * 2
def baseEnd_2783189 : Nat := 158790412145157388215317

theorem tailTrace_2783189 : CollatzResearch.WordTrace tailWord_2783189 prefixEnd_2783189 158790412145157388215317 := by
  unfold tailWord_2783189
  simp only [CollatzResearch.WordTrace]
  refine ⟨101511242313989058683288621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67674161542659372455525747 101511242313989058683288621)
  ·
    refine ⟨38066715867745897006233233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101511242313989058683288621 38066715867745897006233233)
    ·
      refine ⟨28550036900809422754674925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38066715867745897006233233 28550036900809422754674925)
      ·
        refine ⟨10706263837803533533003097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28550036900809422754674925 10706263837803533533003097)
        ·
          refine ⟨8029697878352650149752323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10706263837803533533003097 8029697878352650149752323)
          ·
            refine ⟨12044546817528975224628485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8029697878352650149752323 12044546817528975224628485)
            ·
              refine ⟨2258352528286682854617841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12044546817528975224628485 2258352528286682854617841)
              ·
                refine ⟨1693764396215012140963381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2258352528286682854617841 1693764396215012140963381)
                ·
                  refine ⟨158790412145157388215317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1693764396215012140963381 158790412145157388215317)
                  ·
                    rfl

theorem cell23_2783189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 5].length) (baseStart_2783189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783189 prefixEnd_2783189 := by exact prefixLift 2783189
  have htrace : WordTrace (prefixWord ++ tailWord_2783189) baseStart_2783189 baseEnd_2783189 := by
    simpa [prefixWord, tailWord_2783189, baseEnd_2783189] using wordTrace_append hprefix tailTrace_2783189
  have hstable : (prefixWord ++ tailWord_2783189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783189).length < 2 ^ (prefixWord ++ tailWord_2783189).sum := by decide
  have hdescent : baseEnd_2783189 < baseStart_2783189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783196 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_2783196 : Nat := 118140960795 + 2783196 * 2 ^ 59
def prefixEnd_2783196 : Nat := 4983230072969 + 3 ^ 40 * 2783196 * 2
def baseEnd_2783196 : Nat := 1429117303670997966550321

theorem tailTrace_2783196 : CollatzResearch.WordTrace tailWord_2783196 prefixEnd_2783196 1429117303670997966550321 := by
  unfold tailWord_2783196
  simp only [CollatzResearch.WordTrace]
  refine ⟨50755748812481849439396721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67674331749975799252528961 50755748812481849439396721)
  ·
    refine ⟨38066811609361387079547541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50755748812481849439396721 38066811609361387079547541)
    ·
      refine ⟨1784381794188815019353791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38066811609361387079547541 1784381794188815019353791)
      ·
        refine ⟨2676572691283222529030687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1784381794188815019353791 2676572691283222529030687)
        ·
          refine ⟨4014859036924833793546031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676572691283222529030687 4014859036924833793546031)
          ·
            refine ⟨6022288555387250690319047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4014859036924833793546031 6022288555387250690319047)
            ·
              refine ⟨9033432833080876035478571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6022288555387250690319047 9033432833080876035478571)
              ·
                refine ⟨13550149249621314053217857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9033432833080876035478571 13550149249621314053217857)
                ·
                  refine ⟨10162611937215985539913393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13550149249621314053217857 10162611937215985539913393)
                  ·
                    refine ⟨7621958952911989154935045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10162611937215985539913393 7621958952911989154935045)
                    ·
                      refine ⟨1429117303670997966550321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7621958952911989154935045 1429117303670997966550321)
                      ·
                        rfl

theorem cell23_2783196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_2783196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783196 prefixEnd_2783196 := by exact prefixLift 2783196
  have htrace : WordTrace (prefixWord ++ tailWord_2783196) baseStart_2783196 baseEnd_2783196 := by
    simpa [prefixWord, tailWord_2783196, baseEnd_2783196] using wordTrace_append hprefix tailTrace_2783196
  have hstable : (prefixWord ++ tailWord_2783196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783196).length < 2 ^ (prefixWord ++ tailWord_2783196).sum := by decide
  have hdescent : baseEnd_2783196 < baseStart_2783196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783292 : List Nat := [2, 2, 2, 2, 2, 1, 1, 5, 1, 5]
def baseStart_2783292 : Nat := 118140960795 + 2783292 * 2 ^ 59
def prefixEnd_2783292 : Nat := 4983230072969 + 3 ^ 40 * 2783292 * 2
def baseEnd_2783292 : Nat := 476388865937943196983293

theorem tailTrace_2783292 : CollatzResearch.WordTrace tailWord_2783292 prefixEnd_2783292 476388865937943196983293 := by
  unfold tailWord_2783292
  simp only [CollatzResearch.WordTrace]
  refine ⟨50757499516307953637144065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67676666021743938182858753 50757499516307953637144065)
  ·
    refine ⟨38068124637230965227858049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50757499516307953637144065 38068124637230965227858049)
    ·
      refine ⟨28551093477923223920893537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38068124637230965227858049 28551093477923223920893537)
      ·
        refine ⟨21413320108442417940670153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28551093477923223920893537 21413320108442417940670153)
        ·
          refine ⟨16059990081331813455502615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21413320108442417940670153 16059990081331813455502615)
          ·
            refine ⟨24089985121997720183253923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16059990081331813455502615 24089985121997720183253923)
            ·
              refine ⟨36134977682996580274880885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24089985121997720183253923 36134977682996580274880885)
              ·
                refine ⟨3387654157780929400770083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36134977682996580274880885 3387654157780929400770083)
                ·
                  refine ⟨5081481236671394101155125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3387654157780929400770083 5081481236671394101155125)
                  ·
                    refine ⟨476388865937943196983293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5081481236671394101155125 476388865937943196983293)
                    ·
                      rfl

theorem cell23_2783292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_2783292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783292 prefixEnd_2783292 := by exact prefixLift 2783292
  have htrace : WordTrace (prefixWord ++ tailWord_2783292) baseStart_2783292 baseEnd_2783292 := by
    simpa [prefixWord, tailWord_2783292, baseEnd_2783292] using wordTrace_append hprefix tailTrace_2783292
  have hstable : (prefixWord ++ tailWord_2783292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783292).length < 2 ^ (prefixWord ++ tailWord_2783292).sum := by decide
  have hdescent : baseEnd_2783292 < baseStart_2783292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783329 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 5, 2, 2]
def baseStart_2783329 : Nat := 118140960795 + 2783329 * 2 ^ 59
def prefixEnd_2783329 : Nat := 4983230072969 + 3 ^ 40 * 2783329 * 2
def baseEnd_2783329 : Nat := 1429185596598045946187209

theorem tailTrace_2783329 : CollatzResearch.WordTrace tailWord_2783329 prefixEnd_2783329 1429185596598045946187209 := by
  unfold tailWord_2783329
  simp only [CollatzResearch.WordTrace]
  refine ⟨101516348533481862593385041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67677565688987908395590027 101516348533481862593385041)
  ·
    refine ⟨76137261400111396945038781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101516348533481862593385041 76137261400111396945038781)
    ·
      refine ⟨28551473025041773854389543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76137261400111396945038781 28551473025041773854389543)
      ·
        refine ⟨42827209537562660781584315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28551473025041773854389543 42827209537562660781584315)
        ·
          refine ⟨64240814306343991172376473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42827209537562660781584315 64240814306343991172376473)
          ·
            refine ⟨48180610729757993379282355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64240814306343991172376473 48180610729757993379282355)
            ·
              refine ⟨72270916094636990068923533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48180610729757993379282355 72270916094636990068923533)
              ·
                refine ⟨27101593535488871275846325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72270916094636990068923533 27101593535488871275846325)
                ·
                  refine ⟨2540774393952081682110593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27101593535488871275846325 2540774393952081682110593)
                  ·
                    refine ⟨1905580795464061261582945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2540774393952081682110593 1905580795464061261582945)
                    ·
                      refine ⟨1429185596598045946187209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1905580795464061261582945 1429185596598045946187209)
                      ·
                        rfl

theorem cell23_2783329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_2783329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783329 prefixEnd_2783329 := by exact prefixLift 2783329
  have htrace : WordTrace (prefixWord ++ tailWord_2783329) baseStart_2783329 baseEnd_2783329 := by
    simpa [prefixWord, tailWord_2783329, baseEnd_2783329] using wordTrace_append hprefix tailTrace_2783329
  have hstable : (prefixWord ++ tailWord_2783329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783329).length < 2 ^ (prefixWord ++ tailWord_2783329).sum := by decide
  have hdescent : baseEnd_2783329 < baseStart_2783329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783335 : List Nat := [1, 1, 5, 1, 1, 2, 1, 11]
def baseStart_2783335 : Nat := 118140960795 + 2783335 * 2 ^ 59
def prefixEnd_2783335 : Nat := 4983230072969 + 3 ^ 40 * 2783335 * 2
def baseEnd_2783335 : Nat := 52932913980813811952303

theorem tailTrace_2783335 : CollatzResearch.WordTrace tailWord_2783335 prefixEnd_2783335 52932913980813811952303 := by
  unfold tailWord_2783335
  simp only [CollatzResearch.WordTrace]
  refine ⟨101516567371460125618103459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67677711580973417078735639 101516567371460125618103459)
  ·
    refine ⟨152274851057190188427155189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101516567371460125618103459 152274851057190188427155189)
    ·
      refine ⟨14275767286611580165045799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152274851057190188427155189 14275767286611580165045799)
      ·
        refine ⟨21413650929917370247568699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14275767286611580165045799 21413650929917370247568699)
        ·
          refine ⟨32120476394876055371353049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21413650929917370247568699 32120476394876055371353049)
          ·
            refine ⟨24090357296157041528514787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32120476394876055371353049 24090357296157041528514787)
            ·
              refine ⟨36135535944235562292772181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24090357296157041528514787 36135535944235562292772181)
              ·
                refine ⟨52932913980813811952303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 36135535944235562292772181 52932913980813811952303)
                ·
                  rfl

theorem cell23_2783335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 11].length) (baseStart_2783335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783335 prefixEnd_2783335 := by exact prefixLift 2783335
  have htrace : WordTrace (prefixWord ++ tailWord_2783335) baseStart_2783335 baseEnd_2783335 := by
    simpa [prefixWord, tailWord_2783335, baseEnd_2783335] using wordTrace_append hprefix tailTrace_2783335
  have hstable : (prefixWord ++ tailWord_2783335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783335).length < 2 ^ (prefixWord ++ tailWord_2783335).sum := by decide
  have hdescent : baseEnd_2783335 < baseStart_2783335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783346 : List Nat := [3, 2, 1, 2, 2, 3, 3, 1, 1, 1, 4]
def baseStart_2783346 : Nat := 118140960795 + 2783346 * 2 ^ 59
def prefixEnd_2783346 : Nat := 4983230072969 + 3 ^ 40 * 2783346 * 2
def baseEnd_2783346 : Nat := 1429194325769172379674631

theorem tailTrace_2783346 : CollatzResearch.WordTrace tailWord_2783346 prefixEnd_2783346 1429194325769172379674631 := by
  unfold tailWord_2783346
  simp only [CollatzResearch.WordTrace]
  refine ⟨25379242143605068624188473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67677979049613516331169261 25379242143605068624188473)
  ·
    refine ⟨19034431607703801468141355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25379242143605068624188473 19034431607703801468141355)
    ·
      refine ⟨28551647411555702202212033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19034431607703801468141355 28551647411555702202212033)
      ·
        refine ⟨21413735558666776651659025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28551647411555702202212033 21413735558666776651659025)
        ·
          refine ⟨16060301669000082488744269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21413735558666776651659025 16060301669000082488744269)
          ·
            refine ⟨6022613125875030933279101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16060301669000082488744269 6022613125875030933279101)
            ·
              refine ⟨2258479922203136599979663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6022613125875030933279101 2258479922203136599979663)
              ·
                refine ⟨3387719883304704899969495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2258479922203136599979663 3387719883304704899969495)
                ·
                  refine ⟨5081579824957057349954243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3387719883304704899969495 5081579824957057349954243)
                  ·
                    refine ⟨7622369737435586024931365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5081579824957057349954243 7622369737435586024931365)
                    ·
                      refine ⟨1429194325769172379674631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7622369737435586024931365 1429194325769172379674631)
                      ·
                        rfl

theorem cell23_2783346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_2783346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783346 prefixEnd_2783346 := by exact prefixLift 2783346
  have htrace : WordTrace (prefixWord ++ tailWord_2783346) baseStart_2783346 baseEnd_2783346 := by
    simpa [prefixWord, tailWord_2783346, baseEnd_2783346] using wordTrace_append hprefix tailTrace_2783346
  have hstable : (prefixWord ++ tailWord_2783346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783346).length < 2 ^ (prefixWord ++ tailWord_2783346).sum := by decide
  have hdescent : baseEnd_2783346 < baseStart_2783346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783363 : List Nat := [1, 1, 1, 3, 3, 4, 1, 4, 1, 2, 2]
def baseStart_2783363 : Nat := 118140960795 + 2783363 * 2 ^ 59
def prefixEnd_2783363 : Nat := 4983230072969 + 3 ^ 40 * 2783363 * 2
def baseEnd_2783363 : Nat := 1429203054940298813162053

theorem tailTrace_2783363 : CollatzResearch.WordTrace tailWord_2783363 prefixEnd_2783363 1429203054940298813162053 := by
  unfold tailWord_2783363
  simp only [CollatzResearch.WordTrace]
  refine ⟨101517588615358686400122743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67678392410239124266748495 101517588615358686400122743)
  ·
    refine ⟨152276382923038029600184115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101517588615358686400122743 152276382923038029600184115)
    ·
      refine ⟨228414574384557044400276173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152276382923038029600184115 228414574384557044400276173)
      ·
        refine ⟨85655465394208891650103565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228414574384557044400276173 85655465394208891650103565)
        ·
          refine ⟨32120799522828334368788837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85655465394208891650103565 32120799522828334368788837)
          ·
            refine ⟨6022649910530312694147907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32120799522828334368788837 6022649910530312694147907)
            ·
              refine ⟨9033974865795469041221861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6022649910530312694147907 9033974865795469041221861)
              ·
                refine ⟨1693870287336650445229099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9033974865795469041221861 1693870287336650445229099)
                ·
                  refine ⟨2540805431004975667843649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693870287336650445229099 2540805431004975667843649)
                  ·
                    refine ⟨1905604073253731750882737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2540805431004975667843649 1905604073253731750882737)
                    ·
                      refine ⟨1429203054940298813162053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1905604073253731750882737 1429203054940298813162053)
                      ·
                        rfl

theorem cell23_2783363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 1, 2, 2].length) (baseStart_2783363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783363 prefixEnd_2783363 := by exact prefixLift 2783363
  have htrace : WordTrace (prefixWord ++ tailWord_2783363) baseStart_2783363 baseEnd_2783363 := by
    simpa [prefixWord, tailWord_2783363, baseEnd_2783363] using wordTrace_append hprefix tailTrace_2783363
  have hstable : (prefixWord ++ tailWord_2783363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783363).length < 2 ^ (prefixWord ++ tailWord_2783363).sum := by decide
  have hdescent : baseEnd_2783363 < baseStart_2783363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783380 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_2783380 : Nat := 118140960795 + 2783380 * 2 ^ 59
def prefixEnd_2783380 : Nat := 4983230072969 + 3 ^ 40 * 2783380 * 2
def baseEnd_2783380 : Nat := 1429211784111425246649475

theorem tailTrace_2783380 : CollatzResearch.WordTrace tailWord_2783380 prefixEnd_2783380 1429211784111425246649475 := by
  unfold tailWord_2783380
  simp only [CollatzResearch.WordTrace]
  refine ⟨50759104328148549151745797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67678805770864732202327729 50759104328148549151745797)
  ·
    refine ⟨9517332061527852965952337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50759104328148549151745797 9517332061527852965952337)
    ·
      refine ⟨7137999046145889724464253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9517332061527852965952337 7137999046145889724464253)
      ·
        refine ⟨2676749642304708646674095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7137999046145889724464253 2676749642304708646674095)
        ·
          refine ⟨4015124463457062970011143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676749642304708646674095 4015124463457062970011143)
          ·
            refine ⟨6022686695185594455016715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4015124463457062970011143 6022686695185594455016715)
            ·
              refine ⟨9034030042778391682525073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6022686695185594455016715 9034030042778391682525073)
              ·
                refine ⟨6775522532083793761893805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9034030042778391682525073 6775522532083793761893805)
                ·
                  refine ⟨2540820949531422660710177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6775522532083793761893805 2540820949531422660710177)
                  ·
                    refine ⟨1905615712148566995532633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2540820949531422660710177 1905615712148566995532633)
                    ·
                      refine ⟨1429211784111425246649475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1905615712148566995532633 1429211784111425246649475)
                      ·
                        rfl

theorem cell23_2783380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_2783380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783380 prefixEnd_2783380 := by exact prefixLift 2783380
  have htrace : WordTrace (prefixWord ++ tailWord_2783380) baseStart_2783380 baseEnd_2783380 := by
    simpa [prefixWord, tailWord_2783380, baseEnd_2783380] using wordTrace_append hprefix tailTrace_2783380
  have hstable : (prefixWord ++ tailWord_2783380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783380).length < 2 ^ (prefixWord ++ tailWord_2783380).sum := by decide
  have hdescent : baseEnd_2783380 < baseStart_2783380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783413 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_2783413 : Nat := 118140960795 + 2783413 * 2 ^ 59
def prefixEnd_2783413 : Nat := 4983230072969 + 3 ^ 40 * 2783413 * 2
def baseEnd_2783413 : Nat := 1429228728973023617536823

theorem tailTrace_2783413 : CollatzResearch.WordTrace tailWord_2783413 prefixEnd_2783413 1429228728973023617536823 := by
  unfold tailWord_2783413
  simp only [CollatzResearch.WordTrace]
  refine ⟨101519412265177544939442893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67679608176785029959628595 101519412265177544939442893)
  ·
    refine ⟨38069779599441579352291085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101519412265177544939442893 38069779599441579352291085)
    ·
      refine ⟨14276167349790592257109157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38069779599441579352291085 14276167349790592257109157)
      ·
        refine ⟨2676781378085736048207967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14276167349790592257109157 2676781378085736048207967)
        ·
          refine ⟨4015172067128604072311951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676781378085736048207967 4015172067128604072311951)
          ·
            refine ⟨6022758100692906108467927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4015172067128604072311951 6022758100692906108467927)
            ·
              refine ⟨9034137151039359162701891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6022758100692906108467927 9034137151039359162701891)
              ·
                refine ⟨13551205726559038744052837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9034137151039359162701891 13551205726559038744052837)
                ·
                  refine ⟨2540851073729819764509907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13551205726559038744052837 2540851073729819764509907)
                  ·
                    refine ⟨3811276610594729646764861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2540851073729819764509907 3811276610594729646764861)
                    ·
                      refine ⟨1429228728973023617536823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3811276610594729646764861 1429228728973023617536823)
                      ·
                        rfl

theorem cell23_2783413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_2783413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783413 prefixEnd_2783413 := by exact prefixLift 2783413
  have htrace : WordTrace (prefixWord ++ tailWord_2783413) baseStart_2783413 baseEnd_2783413 := by
    simpa [prefixWord, tailWord_2783413, baseEnd_2783413] using wordTrace_append hprefix tailTrace_2783413
  have hstable : (prefixWord ++ tailWord_2783413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783413).length < 2 ^ (prefixWord ++ tailWord_2783413).sum := by decide
  have hdescent : baseEnd_2783413 < baseStart_2783413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783453 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_2783453 : Nat := 118140960795 + 2783453 * 2 ^ 59
def prefixEnd_2783453 : Nat := 4983230072969 + 3 ^ 40 * 2783453 * 2
def baseEnd_2783453 : Nat := 1429249268199203461036639

theorem tailTrace_2783453 : CollatzResearch.WordTrace tailWord_2783453 prefixEnd_2783453 1429249268199203461036639 := by
  unfold tailWord_2783453
  simp only [CollatzResearch.WordTrace]
  refine ⟨101520871185032631770899013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67680580790021754513932675 101520871185032631770899013)
  ·
    refine ⟨19035163347193618457043565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101520871185032631770899013 19035163347193618457043565)
    ·
      refine ⟨7138186255197606921391337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19035163347193618457043565 7138186255197606921391337)
      ·
        refine ⟨5353639691398205191043503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7138186255197606921391337 5353639691398205191043503)
        ·
          refine ⟨8030459537097307786565255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5353639691398205191043503 8030459537097307786565255)
          ·
            refine ⟨12045689305645961679847883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8030459537097307786565255 12045689305645961679847883)
            ·
              refine ⟨18068533958468942519771825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12045689305645961679847883 18068533958468942519771825)
              ·
                refine ⟨13551400468851706889828869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18068533958468942519771825 13551400468851706889828869)
                ·
                  refine ⟨2540887587909695041842913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13551400468851706889828869 2540887587909695041842913)
                  ·
                    refine ⟨1905665690932271281382185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2540887587909695041842913 1905665690932271281382185)
                    ·
                      refine ⟨1429249268199203461036639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1905665690932271281382185 1429249268199203461036639)
                      ·
                        rfl

theorem cell23_2783453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_2783453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783453 prefixEnd_2783453 := by exact prefixLift 2783453
  have htrace : WordTrace (prefixWord ++ tailWord_2783453) baseStart_2783453 baseEnd_2783453 := by
    simpa [prefixWord, tailWord_2783453, baseEnd_2783453] using wordTrace_append hprefix tailTrace_2783453
  have hstable : (prefixWord ++ tailWord_2783453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783453).length < 2 ^ (prefixWord ++ tailWord_2783453).sum := by decide
  have hdescent : baseEnd_2783453 < baseStart_2783453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783482 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7]
def baseStart_2783482 : Nat := 118140960795 + 2783482 * 2 ^ 59
def prefixEnd_2783482 : Nat := 4983230072969 + 3 ^ 40 * 2783482 * 2
def baseEnd_2783482 : Nat := 1429264159138183847574005

theorem tailTrace_2783482 : CollatzResearch.WordTrace tailWord_2783482 prefixEnd_2783482 1429264159138183847574005 := by
  unfold tailWord_2783482
  simp only [CollatzResearch.WordTrace]
  refine ⟨25380482225481892430926175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67681285934618379815803133 25380482225481892430926175)
  ·
    refine ⟨38070723338222838646389263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25380482225481892430926175 38070723338222838646389263)
    ·
      refine ⟨57106085007334257969583895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38070723338222838646389263 57106085007334257969583895)
      ·
        refine ⟨85659127511001386954375843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57106085007334257969583895 85659127511001386954375843)
        ·
          refine ⟨128488691266502080431563765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85659127511001386954375843 128488691266502080431563765)
          ·
            refine ⟨12045814806234570040459103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128488691266502080431563765 12045814806234570040459103)
            ·
              refine ⟨18068722209351855060688655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12045814806234570040459103 18068722209351855060688655)
              ·
                refine ⟨27103083314027782591032983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18068722209351855060688655 27103083314027782591032983)
                ·
                  refine ⟨40654624971041673886549475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27103083314027782591032983 40654624971041673886549475)
                  ·
                    refine ⟨60981937456562510829824213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40654624971041673886549475 60981937456562510829824213)
                    ·
                      refine ⟨1429264159138183847574005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60981937456562510829824213 1429264159138183847574005)
                      ·
                        rfl

theorem cell23_2783482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_2783482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783482 prefixEnd_2783482 := by exact prefixLift 2783482
  have htrace : WordTrace (prefixWord ++ tailWord_2783482) baseStart_2783482 baseEnd_2783482 := by
    simpa [prefixWord, tailWord_2783482, baseEnd_2783482] using wordTrace_append hprefix tailTrace_2783482
  have hstable : (prefixWord ++ tailWord_2783482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783482).length < 2 ^ (prefixWord ++ tailWord_2783482).sum := by decide
  have hdescent : baseEnd_2783482 < baseStart_2783482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783509 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_2783509 : Nat := 118140960795 + 2783509 * 2 ^ 59
def prefixEnd_2783509 : Nat := 4983230072969 + 3 ^ 40 * 2783509 * 2
def baseEnd_2783509 : Nat := 1429278023115855241936381

theorem tailTrace_2783509 : CollatzResearch.WordTrace tailWord_2783509 prefixEnd_2783509 1429278023115855241936381 := by
  unfold tailWord_2783509
  simp only [CollatzResearch.WordTrace]
  refine ⟨101522913672829753334937581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67681942448553168889958387 101522913672829753334937581)
  ·
    refine ⟨38071092627311157500601593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101522913672829753334937581 38071092627311157500601593)
    ·
      refine ⟨28553319470483368125451195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38071092627311157500601593 28553319470483368125451195)
      ·
        refine ⟨42829979205725052188176793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28553319470483368125451195 42829979205725052188176793)
        ·
          refine ⟨32122484404293789141132595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42829979205725052188176793 32122484404293789141132595)
          ·
            refine ⟨48183726606440683711698893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32122484404293789141132595 48183726606440683711698893)
            ·
              refine ⟨18068897477415256391887085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48183726606440683711698893 18068897477415256391887085)
              ·
                refine ⟨6775836554030721146957657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18068897477415256391887085 6775836554030721146957657)
                ·
                  refine ⟨5081877415523040860218243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6775836554030721146957657 5081877415523040860218243)
                  ·
                    refine ⟨7622816123284561290327365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5081877415523040860218243 7622816123284561290327365)
                    ·
                      refine ⟨1429278023115855241936381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7622816123284561290327365 1429278023115855241936381)
                      ·
                        rfl

theorem cell23_2783509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_2783509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783509 prefixEnd_2783509 := by exact prefixLift 2783509
  have htrace : WordTrace (prefixWord ++ tailWord_2783509) baseStart_2783509 baseEnd_2783509 := by
    simpa [prefixWord, tailWord_2783509, baseEnd_2783509] using wordTrace_append hprefix tailTrace_2783509
  have hstable : (prefixWord ++ tailWord_2783509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783509).length < 2 ^ (prefixWord ++ tailWord_2783509).sum := by decide
  have hdescent : baseEnd_2783509 < baseStart_2783509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783532 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 8]
def baseStart_2783532 : Nat := 118140960795 + 2783532 * 2 ^ 59
def prefixEnd_2783532 : Nat := 4983230072969 + 3 ^ 40 * 2783532 * 2
def baseEnd_2783532 : Nat := 158809981463434294660975

theorem tailTrace_2783532 : CollatzResearch.WordTrace tailWord_2783532 prefixEnd_2783532 158809981463434294660975 := by
  unfold tailWord_2783532
  simp only [CollatzResearch.WordTrace]
  refine ⟨50761876275873214131512425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67682501701164285508683233 50761876275873214131512425)
  ·
    refine ⟨38071407206904910598634319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50761876275873214131512425 38071407206904910598634319)
    ·
      refine ⟨57107110810357365897951479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38071407206904910598634319 57107110810357365897951479)
      ·
        refine ⟨85660666215536048846927219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57107110810357365897951479 85660666215536048846927219)
        ·
          refine ⟨128490999323304073270390829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85660666215536048846927219 128490999323304073270390829)
          ·
            refine ⟨48184124746239027476396561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128490999323304073270390829 48184124746239027476396561)
            ·
              refine ⟨36138093559679270607297421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48184124746239027476396561 36138093559679270607297421)
              ·
                refine ⟨13551785084879726477736533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36138093559679270607297421 13551785084879726477736533)
                ·
                  refine ⟨158809981463434294660975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13551785084879726477736533 158809981463434294660975)
                  ·
                    rfl

theorem cell23_2783532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 8].length) (baseStart_2783532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783532 prefixEnd_2783532 := by exact prefixLift 2783532
  have htrace : WordTrace (prefixWord ++ tailWord_2783532) baseStart_2783532 baseEnd_2783532 := by
    simpa [prefixWord, tailWord_2783532, baseEnd_2783532] using wordTrace_append hprefix tailTrace_2783532
  have hstable : (prefixWord ++ tailWord_2783532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783532).length < 2 ^ (prefixWord ++ tailWord_2783532).sum := by decide
  have hdescent : baseEnd_2783532 < baseStart_2783532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783552 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 6]
def baseStart_2783552 : Nat := 118140960795 + 2783552 * 2 ^ 59
def prefixEnd_2783552 : Nat := 4983230072969 + 3 ^ 40 * 2783552 * 2
def baseEnd_2783552 : Nat := 1429300102783998573698683

theorem tailTrace_2783552 : CollatzResearch.WordTrace tailWord_2783552 prefixEnd_2783552 1429300102783998573698683 := by
  unfold tailWord_2783552
  simp only [CollatzResearch.WordTrace]
  refine ⟨50762241005836985839376455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67682988007782647785835273 50762241005836985839376455)
  ·
    refine ⟨76143361508755478759064683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50762241005836985839376455 76143361508755478759064683)
    ·
      refine ⟨114215042263133218138597025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76143361508755478759064683 114215042263133218138597025)
      ·
        refine ⟨85661281697349913603947769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114215042263133218138597025 85661281697349913603947769)
        ·
          refine ⟨64245961273012435202960827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85661281697349913603947769 64245961273012435202960827)
          ·
            refine ⟨96368941909518652804441241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64245961273012435202960827 96368941909518652804441241)
            ·
              refine ⟨72276706432138989603330931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96368941909518652804441241 72276706432138989603330931)
              ·
                refine ⟨108415059648208484404996397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72276706432138989603330931 108415059648208484404996397)
                ·
                  refine ⟨40655647368078181651873649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108415059648208484404996397 40655647368078181651873649)
                  ·
                    refine ⟨30491735526058636238905237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40655647368078181651873649 30491735526058636238905237)
                    ·
                      refine ⟨1429300102783998573698683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30491735526058636238905237 1429300102783998573698683)
                      ·
                        rfl

theorem cell23_2783552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_2783552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783552 prefixEnd_2783552 := by exact prefixLift 2783552
  have htrace : WordTrace (prefixWord ++ tailWord_2783552) baseStart_2783552 baseEnd_2783552 := by
    simpa [prefixWord, tailWord_2783552, baseEnd_2783552] using wordTrace_append hprefix tailTrace_2783552
  have hstable : (prefixWord ++ tailWord_2783552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783552).length < 2 ^ (prefixWord ++ tailWord_2783552).sum := by decide
  have hdescent : baseEnd_2783552 < baseStart_2783552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783553 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 3, 4]
def baseStart_2783553 : Nat := 118140960795 + 2783553 * 2 ^ 59
def prefixEnd_2783553 : Nat := 4983230072969 + 3 ^ 40 * 2783553 * 2
def baseEnd_2783553 : Nat := 476433538754884356595393

theorem tailTrace_2783553 : CollatzResearch.WordTrace tailWord_2783553 prefixEnd_2783553 476433538754884356595393 := by
  unfold tailWord_2783553
  simp only [CollatzResearch.WordTrace]
  refine ⟨101524518484670348849539313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67683012323113565899692875 101524518484670348849539313)
  ·
    refine ⟨76143388863502761637154485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101524518484670348849539313 76143388863502761637154485)
    ·
      refine ⟨7138442705953383903483233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76143388863502761637154485 7138442705953383903483233)
      ·
        refine ⟨5353832029465037927612425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7138442705953383903483233 5353832029465037927612425)
        ·
          refine ⟨4015374022098778445709319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5353832029465037927612425 4015374022098778445709319)
          ·
            refine ⟨6023061033148167668563979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4015374022098778445709319 6023061033148167668563979)
            ·
              refine ⟨9034591549722251502845969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6023061033148167668563979 9034591549722251502845969)
              ·
                refine ⟨6775943662291688627134477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9034591549722251502845969 6775943662291688627134477)
                ·
                  refine ⟨2540978873359383235175429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6775943662291688627134477 2540978873359383235175429)
                  ·
                    refine ⟨476433538754884356595393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2540978873359383235175429 476433538754884356595393)
                    ·
                      rfl

theorem cell23_2783553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_2783553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783553 prefixEnd_2783553 := by exact prefixLift 2783553
  have htrace : WordTrace (prefixWord ++ tailWord_2783553) baseStart_2783553 baseEnd_2783553 := by
    simpa [prefixWord, tailWord_2783553, baseEnd_2783553] using wordTrace_append hprefix tailTrace_2783553
  have hstable : (prefixWord ++ tailWord_2783553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783553).length < 2 ^ (prefixWord ++ tailWord_2783553).sum := by decide
  have hdescent : baseEnd_2783553 < baseStart_2783553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783593 : List Nat := [1, 2, 1, 1, 1, 3, 3, 6, 1, 1, 3]
def baseStart_2783593 : Nat := 118140960795 + 2783593 * 2 ^ 59
def prefixEnd_2783593 : Nat := 4983230072969 + 3 ^ 40 * 2783593 * 2
def baseEnd_2783593 : Nat := 1429321155490832913285995

theorem tailTrace_2783593 : CollatzResearch.WordTrace tailWord_2783593 prefixEnd_2783593 1429321155490832913285995 := by
  unfold tailWord_2783593
  simp only [CollatzResearch.WordTrace]
  refine ⟨101525977404525435680995433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67683984936350290453996955 101525977404525435680995433)
  ·
    refine ⟨76144483053394076760746575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101525977404525435680995433 76144483053394076760746575)
    ·
      refine ⟨114216724580091115141119863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76144483053394076760746575 114216724580091115141119863)
      ·
        refine ⟨171325086870136672711679795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114216724580091115141119863 171325086870136672711679795)
        ·
          refine ⟨256987630305205009067519693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171325086870136672711679795 256987630305205009067519693)
          ·
            refine ⟨96370361364451878400319885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256987630305205009067519693 96370361364451878400319885)
            ·
              refine ⟨36138885511669454400119957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96370361364451878400319885 36138885511669454400119957)
              ·
                refine ⟨1694010258359505675005623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36138885511669454400119957 1694010258359505675005623)
                ·
                  refine ⟨2541015387539258512508435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694010258359505675005623 2541015387539258512508435)
                  ·
                    refine ⟨3811523081308887768762653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2541015387539258512508435 3811523081308887768762653)
                    ·
                      refine ⟨1429321155490832913285995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3811523081308887768762653 1429321155490832913285995)
                      ·
                        rfl

theorem cell23_2783593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 1, 1, 3].length) (baseStart_2783593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783593 prefixEnd_2783593 := by exact prefixLift 2783593
  have htrace : WordTrace (prefixWord ++ tailWord_2783593) baseStart_2783593 baseEnd_2783593 := by
    simpa [prefixWord, tailWord_2783593, baseEnd_2783593] using wordTrace_append hprefix tailTrace_2783593
  have hstable : (prefixWord ++ tailWord_2783593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783593).length < 2 ^ (prefixWord ++ tailWord_2783593).sum := by decide
  have hdescent : baseEnd_2783593 < baseStart_2783593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783599 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 4]
def baseStart_2783599 : Nat := 118140960795 + 2783599 * 2 ^ 59
def prefixEnd_2783599 : Nat := 4983230072969 + 3 ^ 40 * 2783599 * 2
def baseEnd_2783599 : Nat := 1429324236374759889810967

theorem tailTrace_2783599 : CollatzResearch.WordTrace tailWord_2783599 prefixEnd_2783599 1429324236374759889810967 := by
  unfold tailWord_2783599
  simp only [CollatzResearch.WordTrace]
  refine ⟨101526196242503698705713851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67684130828335799137142567 101526196242503698705713851)
  ·
    refine ⟨152289294363755548058570777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101526196242503698705713851 152289294363755548058570777)
    ·
      refine ⟨114216970772816661043928083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152289294363755548058570777 114216970772816661043928083)
      ·
        refine ⟨171325456159224991565892125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114216970772816661043928083 171325456159224991565892125)
        ·
          refine ⟨64247046059709371837209547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171325456159224991565892125 64247046059709371837209547)
          ·
            refine ⟨96370569089564057755814321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64247046059709371837209547 96370569089564057755814321)
            ·
              refine ⟨72277926817173043316860741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96370569089564057755814321 72277926817173043316860741)
              ·
                refine ⟨13552111278219945621911389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72277926817173043316860741 13552111278219945621911389)
                ·
                  refine ⟨5082041729332479608216771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13552111278219945621911389 5082041729332479608216771)
                  ·
                    refine ⟨7623062593998719412325157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5082041729332479608216771 7623062593998719412325157)
                    ·
                      refine ⟨1429324236374759889810967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7623062593998719412325157 1429324236374759889810967)
                      ·
                        rfl

theorem cell23_2783599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 4].length) (baseStart_2783599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783599 prefixEnd_2783599 := by exact prefixLift 2783599
  have htrace : WordTrace (prefixWord ++ tailWord_2783599) baseStart_2783599 baseEnd_2783599 := by
    simpa [prefixWord, tailWord_2783599, baseEnd_2783599] using wordTrace_append hprefix tailTrace_2783599
  have hstable : (prefixWord ++ tailWord_2783599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783599).length < 2 ^ (prefixWord ++ tailWord_2783599).sum := by decide
  have hdescent : baseEnd_2783599 < baseStart_2783599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783656 : List Nat := [2, 1, 6, 1, 1, 1, 1, 10]
def baseStart_2783656 : Nat := 118140960795 + 2783656 * 2 ^ 59
def prefixEnd_2783656 : Nat := 4983230072969 + 3 ^ 40 * 2783656 * 2
def baseEnd_2783656 : Nat := 52939018695261709881415

theorem tailTrace_2783656 : CollatzResearch.WordTrace tailWord_2783656 prefixEnd_2783656 52939018695261709881415 := by
  unfold tailWord_2783656
  simp only [CollatzResearch.WordTrace]
  refine ⟨50764137601648598720269411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67685516802198131627025881 50764137601648598720269411)
  ·
    refine ⟨76146206402472898080404117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50764137601648598720269411 76146206402472898080404117)
    ·
      refine ⟨3569353425115917097518943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76146206402472898080404117 3569353425115917097518943)
      ·
        refine ⟨5354030137673875646278415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3569353425115917097518943 5354030137673875646278415)
        ·
          refine ⟨8031045206510813469417623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5354030137673875646278415 8031045206510813469417623)
          ·
            refine ⟨12046567809766220204126435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8031045206510813469417623 12046567809766220204126435)
            ·
              refine ⟨18069851714649330306189653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12046567809766220204126435 18069851714649330306189653)
              ·
                refine ⟨52939018695261709881415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18069851714649330306189653 52939018695261709881415)
                ·
                  rfl

theorem cell23_2783656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 10].length) (baseStart_2783656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783656 prefixEnd_2783656 := by exact prefixLift 2783656
  have htrace : WordTrace (prefixWord ++ tailWord_2783656) baseStart_2783656 baseEnd_2783656 := by
    simpa [prefixWord, tailWord_2783656, baseEnd_2783656] using wordTrace_append hprefix tailTrace_2783656
  have hstable : (prefixWord ++ tailWord_2783656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783656).length < 2 ^ (prefixWord ++ tailWord_2783656).sum := by decide
  have hdescent : baseEnd_2783656 < baseStart_2783656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783666 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3]
def baseStart_2783666 : Nat := 118140960795 + 2783666 * 2 ^ 59
def prefixEnd_2783666 : Nat := 4983230072969 + 3 ^ 40 * 2783666 * 2
def baseEnd_2783666 : Nat := 1429358639578611127673159

theorem tailTrace_2783666 : CollatzResearch.WordTrace tailWord_2783666 prefixEnd_2783666 1429358639578611127673159 := by
  unfold tailWord_2783666
  simp only [CollatzResearch.WordTrace]
  refine ⟨25382159983315242287100713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67685759955507312765601901 25382159983315242287100713)
  ·
    refine ⟨19036619987486431715325535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25382159983315242287100713 19036619987486431715325535)
    ·
      refine ⟨28554929981229647572988303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19036619987486431715325535 28554929981229647572988303)
      ·
        refine ⟨42832394971844471359482455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28554929981229647572988303 42832394971844471359482455)
        ·
          refine ⟨64248592457766707039223683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42832394971844471359482455 64248592457766707039223683)
          ·
            refine ⟨96372888686650060558835525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64248592457766707039223683 96372888686650060558835525)
            ·
              refine ⟨18069916628746886354781661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96372888686650060558835525 18069916628746886354781661)
              ·
                refine ⟨6776218735780082383043123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18069916628746886354781661 6776218735780082383043123)
                ·
                  refine ⟨10164328103670123574564685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6776218735780082383043123 10164328103670123574564685)
                  ·
                    refine ⟨3811623038876296340461757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10164328103670123574564685 3811623038876296340461757)
                    ·
                      refine ⟨1429358639578611127673159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3811623038876296340461757 1429358639578611127673159)
                      ·
                        rfl

theorem cell23_2783666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_2783666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783666 prefixEnd_2783666 := by exact prefixLift 2783666
  have htrace : WordTrace (prefixWord ++ tailWord_2783666) baseStart_2783666 baseEnd_2783666 := by
    simpa [prefixWord, tailWord_2783666, baseEnd_2783666] using wordTrace_append hprefix tailTrace_2783666
  have hstable : (prefixWord ++ tailWord_2783666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783666).length < 2 ^ (prefixWord ++ tailWord_2783666).sum := by decide
  have hdescent : baseEnd_2783666 < baseStart_2783666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783700 : List Nat := [2, 4, 1, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_2783700 : Nat := 118140960795 + 2783700 * 2 ^ 59
def prefixEnd_2783700 : Nat := 4983230072969 + 3 ^ 40 * 2783700 * 2
def baseEnd_2783700 : Nat := 1429376097920863994648003

theorem tailTrace_2783700 : CollatzResearch.WordTrace tailWord_2783700 prefixEnd_2783700 1429376097920863994648003 := by
  unfold tailWord_2783700
  simp only [CollatzResearch.WordTrace]
  refine ⟨50764940007568896477570277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67686586676758528636760369 50764940007568896477570277)
  ·
    refine ⟨9518426251419168089544427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50764940007568896477570277 9518426251419168089544427)
    ·
      refine ⟨14277639377128752134316641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9518426251419168089544427 14277639377128752134316641)
      ·
        refine ⟨10708229532846564100737481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14277639377128752134316641 10708229532846564100737481)
        ·
          refine ⟨8031172149634923075553111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10708229532846564100737481 8031172149634923075553111)
          ·
            refine ⟨12046758224452384613329667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8031172149634923075553111 12046758224452384613329667)
            ·
              refine ⟨18070137336678576919994501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12046758224452384613329667 18070137336678576919994501)
              ·
                refine ⟨3388150750627233172498969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18070137336678576919994501 3388150750627233172498969)
                ·
                  refine ⟨2541113062970424879374227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3388150750627233172498969 2541113062970424879374227)
                  ·
                    refine ⟨3811669594455637319061341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2541113062970424879374227 3811669594455637319061341)
                    ·
                      refine ⟨1429376097920863994648003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3811669594455637319061341 1429376097920863994648003)
                      ·
                        rfl

theorem cell23_2783700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_2783700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783700 prefixEnd_2783700 := by exact prefixLift 2783700
  have htrace : WordTrace (prefixWord ++ tailWord_2783700) baseStart_2783700 baseEnd_2783700 := by
    simpa [prefixWord, tailWord_2783700, baseEnd_2783700] using wordTrace_append hprefix tailTrace_2783700
  have hstable : (prefixWord ++ tailWord_2783700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783700).length < 2 ^ (prefixWord ++ tailWord_2783700).sum := by decide
  have hdescent : baseEnd_2783700 < baseStart_2783700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783723 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 1, 4, 2]
def baseStart_2783723 : Nat := 118140960795 + 2783723 * 2 ^ 59
def prefixEnd_2783723 : Nat := 4983230072969 + 3 ^ 40 * 2783723 * 2
def baseEnd_2783723 : Nat := 1429387907975917404660397

theorem tailTrace_2783723 : CollatzResearch.WordTrace tailWord_2783723 prefixEnd_2783723 1429387907975917404660397 := by
  unfold tailWord_2783723
  simp only [CollatzResearch.WordTrace]
  refine ⟨101530718894054467883227823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67687145929369645255485215 101530718894054467883227823)
  ·
    refine ⟨152296078341081701824841735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101530718894054467883227823 152296078341081701824841735)
    ·
      refine ⟨228444117511622552737262603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152296078341081701824841735 228444117511622552737262603)
      ·
        refine ⟨342666176267433829105893905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228444117511622552737262603 342666176267433829105893905)
        ·
          refine ⟨256999632200575371829420429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342666176267433829105893905 256999632200575371829420429)
          ·
            refine ⟨96374862075215764436032661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256999632200575371829420429 96374862075215764436032661)
            ·
              refine ⟨4517571659775738957939031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96374862075215764436032661 4517571659775738957939031)
              ·
                refine ⟨6776357489663608436908547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4517571659775738957939031 6776357489663608436908547)
                ·
                  refine ⟨10164536234495412655362821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6776357489663608436908547 10164536234495412655362821)
                  ·
                    refine ⟨1905850543967889872880529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10164536234495412655362821 1905850543967889872880529)
                    ·
                      refine ⟨1429387907975917404660397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1905850543967889872880529 1429387907975917404660397)
                      ·
                        rfl

theorem cell23_2783723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 4, 2].length) (baseStart_2783723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783723 prefixEnd_2783723 := by exact prefixLift 2783723
  have htrace : WordTrace (prefixWord ++ tailWord_2783723) baseStart_2783723 baseEnd_2783723 := by
    simpa [prefixWord, tailWord_2783723, baseEnd_2783723] using wordTrace_append hprefix tailTrace_2783723
  have hstable : (prefixWord ++ tailWord_2783723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783723).length < 2 ^ (prefixWord ++ tailWord_2783723).sum := by decide
  have hdescent : baseEnd_2783723 < baseStart_2783723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783759 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 3, 7]
def baseStart_2783759 : Nat := 118140960795 + 2783759 * 2 ^ 59
def prefixEnd_2783759 : Nat := 4983230072969 + 3 ^ 40 * 2783759 * 2
def baseEnd_2783759 : Nat := 476468797759826421270077

theorem tailTrace_2783759 : CollatzResearch.WordTrace tailWord_2783759 prefixEnd_2783759 476468797759826421270077 := by
  unfold tailWord_2783759
  simp only [CollatzResearch.WordTrace]
  refine ⟨101532031921924046031538331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67688021281282697354358887 101532031921924046031538331)
  ·
    refine ⟨152298047882886069047307497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101532031921924046031538331 152298047882886069047307497)
    ·
      refine ⟨114223535912164551785480623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152298047882886069047307497 114223535912164551785480623)
      ·
        refine ⟨171335303868246827678220935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114223535912164551785480623 171335303868246827678220935)
        ·
          refine ⟨257002955802370241517331403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171335303868246827678220935 257002955802370241517331403)
          ·
            refine ⟨385504433703555362275997105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257002955802370241517331403 385504433703555362275997105)
            ·
              refine ⟨289128325277666521706997829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385504433703555362275997105 289128325277666521706997829)
              ·
                refine ⟨54211560989562472820062093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 289128325277666521706997829 54211560989562472820062093)
                ·
                  refine ⟨20329335371085927307523285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54211560989562472820062093 20329335371085927307523285)
                  ·
                    refine ⟨476468797759826421270077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20329335371085927307523285 476468797759826421270077)
                    ·
                      rfl

theorem cell23_2783759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 7].length) (baseStart_2783759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783759 prefixEnd_2783759 := by exact prefixLift 2783759
  have htrace : WordTrace (prefixWord ++ tailWord_2783759) baseStart_2783759 baseEnd_2783759 := by
    simpa [prefixWord, tailWord_2783759, baseEnd_2783759] using wordTrace_append hprefix tailTrace_2783759
  have hstable : (prefixWord ++ tailWord_2783759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783759).length < 2 ^ (prefixWord ++ tailWord_2783759).sum := by decide
  have hdescent : baseEnd_2783759 < baseStart_2783759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783773 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_2783773 : Nat := 118140960795 + 2783773 * 2 ^ 59
def prefixEnd_2783773 : Nat := 4983230072969 + 3 ^ 40 * 2783773 * 2
def baseEnd_2783773 : Nat := 1429413582008642209035167

theorem tailTrace_2783773 : CollatzResearch.WordTrace tailWord_2783773 prefixEnd_2783773 1429413582008642209035167 := by
  unfold tailWord_2783773
  simp only [CollatzResearch.WordTrace]
  refine ⟨101532542543873326422547973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67688361695915550948365315 101532542543873326422547973)
  ·
    refine ⟨19037351726976248704227745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101532542543873326422547973 19037351726976248704227745)
    ·
      refine ⟨14278013795232186528170809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19037351726976248704227745 14278013795232186528170809)
      ·
        refine ⟨10708510346424139896128107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14278013795232186528170809 10708510346424139896128107)
        ·
          refine ⟨16062765519636209844192161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10708510346424139896128107 16062765519636209844192161)
          ·
            refine ⟨12047074139727157383144121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16062765519636209844192161 12047074139727157383144121)
            ·
              refine ⟨9035305604795368037358091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12047074139727157383144121 9035305604795368037358091)
              ·
                refine ⟨13552958407193052056037137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9035305604795368037358091 13552958407193052056037137)
                ·
                  refine ⟨10164718805394789042027853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13552958407193052056037137 10164718805394789042027853)
                  ·
                    refine ⟨3811769552023045890760445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10164718805394789042027853 3811769552023045890760445)
                    ·
                      refine ⟨1429413582008642209035167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3811769552023045890760445 1429413582008642209035167)
                      ·
                        rfl

theorem cell23_2783773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_2783773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783773 prefixEnd_2783773 := by exact prefixLift 2783773
  have htrace : WordTrace (prefixWord ++ tailWord_2783773) baseStart_2783773 baseEnd_2783773 := by
    simpa [prefixWord, tailWord_2783773, baseEnd_2783773] using wordTrace_append hprefix tailTrace_2783773
  have hstable : (prefixWord ++ tailWord_2783773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783773).length < 2 ^ (prefixWord ++ tailWord_2783773).sum := by decide
  have hdescent : baseEnd_2783773 < baseStart_2783773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783813 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 2, 1, 4]
def baseStart_2783813 : Nat := 118140960795 + 2783813 * 2 ^ 59
def prefixEnd_2783813 : Nat := 4983230072969 + 3 ^ 40 * 2783813 * 2
def baseEnd_2783813 : Nat := 1429434121234822052534983

theorem tailTrace_2783813 : CollatzResearch.WordTrace tailWord_2783813 prefixEnd_2783813 1429434121234822052534983 := by
  unfold tailWord_2783813
  simp only [CollatzResearch.WordTrace]
  refine ⟨101534001463728413254004093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67689334309152275502669395 101534001463728413254004093)
  ·
    refine ⟨38075250548898154970251535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101534001463728413254004093 38075250548898154970251535)
    ·
      refine ⟨57112875823347232455377303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38075250548898154970251535 57112875823347232455377303)
      ·
        refine ⟨85669313735020848683065955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57112875823347232455377303 85669313735020848683065955)
        ·
          refine ⟨128503970602531273024598933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85669313735020848683065955 128503970602531273024598933)
          ·
            refine ⟨6023623621993653423028075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 128503970602531273024598933 6023623621993653423028075)
            ·
              refine ⟨9035435432990480134542113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6023623621993653423028075 9035435432990480134542113)
              ·
                refine ⟨6776576574742860100906585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9035435432990480134542113 6776576574742860100906585)
                ·
                  refine ⟨5082432431057145075679939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6776576574742860100906585 5082432431057145075679939)
                  ·
                    refine ⟨7623648646585717613519909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5082432431057145075679939 7623648646585717613519909)
                    ·
                      refine ⟨1429434121234822052534983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7623648646585717613519909 1429434121234822052534983)
                      ·
                        rfl

theorem cell23_2783813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_2783813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783813 prefixEnd_2783813 := by exact prefixLift 2783813
  have htrace : WordTrace (prefixWord ++ tailWord_2783813) baseStart_2783813 baseEnd_2783813 := by
    simpa [prefixWord, tailWord_2783813, baseEnd_2783813] using wordTrace_append hprefix tailTrace_2783813
  have hstable : (prefixWord ++ tailWord_2783813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783813).length < 2 ^ (prefixWord ++ tailWord_2783813).sum := by decide
  have hdescent : baseEnd_2783813 < baseStart_2783813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783814 : List Nat := [6, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_2783814 : Nat := 118140960795 + 2783814 * 2 ^ 59
def prefixEnd_2783814 : Nat := 4983230072969 + 3 ^ 40 * 2783814 * 2
def baseEnd_2783814 : Nat := 158826070523941838735831

theorem tailTrace_2783814 : CollatzResearch.WordTrace tailWord_2783814 prefixEnd_2783814 158826070523941838735831 := by
  unfold tailWord_2783814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3172938685522649700774703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67689358624483193616526997 3172938685522649700774703)
  ·
    refine ⟨4759408028283974551162055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3172938685522649700774703 4759408028283974551162055)
    ·
      refine ⟨7139112042425961826743083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4759408028283974551162055 7139112042425961826743083)
      ·
        refine ⟨10708668063638942740114625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7139112042425961826743083 10708668063638942740114625)
        ·
          refine ⟨8031501047729207055085969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10708668063638942740114625 8031501047729207055085969)
          ·
            refine ⟨6023625785796905291314477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8031501047729207055085969 6023625785796905291314477)
            ·
              refine ⟨2258859669673839484242929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6023625785796905291314477 2258859669673839484242929)
              ·
                refine ⟨1694144752255379613182197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2258859669673839484242929 1694144752255379613182197)
                ·
                  refine ⟨158826070523941838735831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1694144752255379613182197 158826070523941838735831)
                  ·
                    rfl

theorem cell23_2783814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_2783814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783814 prefixEnd_2783814 := by exact prefixLift 2783814
  have htrace : WordTrace (prefixWord ++ tailWord_2783814) baseStart_2783814 baseEnd_2783814 := by
    simpa [prefixWord, tailWord_2783814, baseEnd_2783814] using wordTrace_append hprefix tailTrace_2783814
  have hstable : (prefixWord ++ tailWord_2783814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783814).length < 2 ^ (prefixWord ++ tailWord_2783814).sum := by decide
  have hdescent : baseEnd_2783814 < baseStart_2783814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783823 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 3, 4]
def baseStart_2783823 : Nat := 118140960795 + 2783823 * 2 ^ 59
def prefixEnd_2783823 : Nat := 4983230072969 + 3 ^ 40 * 2783823 * 2
def baseEnd_2783823 : Nat := 476479752013789004469979

theorem tailTrace_2783823 : CollatzResearch.WordTrace tailWord_2783823 prefixEnd_2783823 476479752013789004469979 := by
  unfold tailWord_2783823
  simp only [CollatzResearch.WordTrace]
  refine ⟨101534366193692184961868123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67689577462461456641245415 101534366193692184961868123)
  ·
    refine ⟨152301549290538277442802185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101534366193692184961868123 152301549290538277442802185)
    ·
      refine ⟨114226161967903708082101639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152301549290538277442802185 114226161967903708082101639)
      ·
        refine ⟨171339242951855562123152459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114226161967903708082101639 171339242951855562123152459)
        ·
          refine ⟨257008864427783343184728689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171339242951855562123152459 257008864427783343184728689)
          ·
            refine ⟨192756648320837507388546517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257008864427783343184728689 192756648320837507388546517)
            ·
              refine ⟨4517733945019629079419059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 192756648320837507388546517 4517733945019629079419059)
              ·
                refine ⟨6776600917529443619128589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4517733945019629079419059 6776600917529443619128589)
                ·
                  refine ⟨2541225344073541357173221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6776600917529443619128589 2541225344073541357173221)
                  ·
                    refine ⟨476479752013789004469979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2541225344073541357173221 476479752013789004469979)
                    ·
                      rfl

theorem cell23_2783823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 4].length) (baseStart_2783823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783823 prefixEnd_2783823 := by exact prefixLift 2783823
  have htrace : WordTrace (prefixWord ++ tailWord_2783823) baseStart_2783823 baseEnd_2783823 := by
    simpa [prefixWord, tailWord_2783823, baseEnd_2783823] using wordTrace_append hprefix tailTrace_2783823
  have hstable : (prefixWord ++ tailWord_2783823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783823).length < 2 ^ (prefixWord ++ tailWord_2783823).sum := by decide
  have hdescent : baseEnd_2783823 < baseStart_2783823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783850 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_2783850 : Nat := 118140960795 + 2783850 * 2 ^ 59
def prefixEnd_2783850 : Nat := 4983230072969 + 3 ^ 40 * 2783850 * 2
def baseEnd_2783850 : Nat := 1429453120019038407772313

theorem tailTrace_2783850 : CollatzResearch.WordTrace tailWord_2783850 prefixEnd_2783850 1429453120019038407772313 := by
  unfold tailWord_2783850
  simp only [CollatzResearch.WordTrace]
  refine ⟨25383837741148592143275251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67690233976396245715400669 25383837741148592143275251)
  ·
    refine ⟨38075756611722888214912877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25383837741148592143275251 38075756611722888214912877)
    ·
      refine ⟨14278408729396083080592329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38075756611722888214912877 14278408729396083080592329)
      ·
        refine ⟨10708806547047062310444247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14278408729396083080592329 10708806547047062310444247)
        ·
          refine ⟨16063209820570593465666371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10708806547047062310444247 16063209820570593465666371)
          ·
            refine ⟨24094814730855890198499557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16063209820570593465666371 24094814730855890198499557)
            ·
              refine ⟨4517777762035479412218667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24094814730855890198499557 4517777762035479412218667)
              ·
                refine ⟨6776666643053219118328001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4517777762035479412218667 6776666643053219118328001)
                ·
                  refine ⟨5082499982289914338746001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6776666643053219118328001 5082499982289914338746001)
                  ·
                    refine ⟨3811874986717435754059501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5082499982289914338746001 3811874986717435754059501)
                    ·
                      refine ⟨1429453120019038407772313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3811874986717435754059501 1429453120019038407772313)
                      ·
                        rfl

theorem cell23_2783850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_2783850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783850 prefixEnd_2783850 := by exact prefixLift 2783850
  have htrace : WordTrace (prefixWord ++ tailWord_2783850) baseStart_2783850 baseEnd_2783850 := by
    simpa [prefixWord, tailWord_2783850, baseEnd_2783850] using wordTrace_append hprefix tailTrace_2783850
  have hstable : (prefixWord ++ tailWord_2783850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783850).length < 2 ^ (prefixWord ++ tailWord_2783850).sum := by decide
  have hdescent : baseEnd_2783850 < baseStart_2783850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783917 : List Nat := [1, 5, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_2783917 : Nat := 118140960795 + 2783917 * 2 ^ 59
def prefixEnd_2783917 : Nat := 4983230072969 + 3 ^ 40 * 2783917 * 2
def baseEnd_2783917 : Nat := 476495841074296548544835

theorem tailTrace_2783917 : CollatzResearch.WordTrace tailWord_2783917 prefixEnd_2783917 476495841074296548544835 := by
  unfold tailWord_2783917
  simp only [CollatzResearch.WordTrace]
  refine ⟨101537794655351639015790005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67691863103567759343860003 101537794655351639015790005)
  ·
    refine ⟨9519168248939216157730313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101537794655351639015790005 9519168248939216157730313)
    ·
      refine ⟨7139376186704412118297735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9519168248939216157730313 7139376186704412118297735)
      ·
        refine ⟨10709064280056618177446603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7139376186704412118297735 10709064280056618177446603)
        ·
          refine ⟨16063596420084927266169905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10709064280056618177446603 16063596420084927266169905)
          ·
            refine ⟨12047697315063695449627429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16063596420084927266169905 12047697315063695449627429)
            ·
              refine ⟨2258943246574442896805143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12047697315063695449627429 2258943246574442896805143)
              ·
                refine ⟨3388414869861664345207715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2258943246574442896805143 3388414869861664345207715)
                ·
                  refine ⟨5082622304792496517811573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3388414869861664345207715 5082622304792496517811573)
                  ·
                    refine ⟨476495841074296548544835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5082622304792496517811573 476495841074296548544835)
                    ·
                      rfl

theorem cell23_2783917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_2783917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783917 prefixEnd_2783917 := by exact prefixLift 2783917
  have htrace : WordTrace (prefixWord ++ tailWord_2783917) baseStart_2783917 baseEnd_2783917 := by
    simpa [prefixWord, tailWord_2783917, baseEnd_2783917] using wordTrace_append hprefix tailTrace_2783917
  have hstable : (prefixWord ++ tailWord_2783917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783917).length < 2 ^ (prefixWord ++ tailWord_2783917).sum := by decide
  have hdescent : baseEnd_2783917 < baseStart_2783917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783920 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 7, 2, 2]
def baseStart_2783920 : Nat := 118140960795 + 2783920 * 2 ^ 59
def prefixEnd_2783920 : Nat := 4983230072969 + 3 ^ 40 * 2783920 * 2
def baseEnd_2783920 : Nat := 1429489063664853133896991

theorem tailTrace_2783920 : CollatzResearch.WordTrace tailWord_2783920 prefixEnd_2783920 1429489063664853133896991 := by
  unfold tailWord_2783920
  simp only [CollatzResearch.WordTrace]
  refine ⟨50768952037170385264074607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67691936049560513685432809 50768952037170385264074607)
  ·
    refine ⟨76153428055755577896111911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50768952037170385264074607 76153428055755577896111911)
    ·
      refine ⟨114230142083633366844167867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76153428055755577896111911 114230142083633366844167867)
      ·
        refine ⟨171345213125450050266251801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114230142083633366844167867 171345213125450050266251801)
        ·
          refine ⟨128508909844087537699688851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171345213125450050266251801 128508909844087537699688851)
          ·
            refine ⟨192763364766131306549533277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128508909844087537699688851 192763364766131306549533277)
            ·
              refine ⟨72286261787299239956074979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192763364766131306549533277 72286261787299239956074979)
              ·
                refine ⟨108429392680948859934112469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72286261787299239956074979 108429392680948859934112469)
                ·
                  refine ⟨2541313890959738904705761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 108429392680948859934112469 2541313890959738904705761)
                  ·
                    refine ⟨1905985418219804178529321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2541313890959738904705761 1905985418219804178529321)
                    ·
                      refine ⟨1429489063664853133896991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1905985418219804178529321 1429489063664853133896991)
                      ·
                        rfl

theorem cell23_2783920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 7, 2, 2].length) (baseStart_2783920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783920 prefixEnd_2783920 := by exact prefixLift 2783920
  have htrace : WordTrace (prefixWord ++ tailWord_2783920) baseStart_2783920 baseEnd_2783920 := by
    simpa [prefixWord, tailWord_2783920, baseEnd_2783920] using wordTrace_append hprefix tailTrace_2783920
  have hstable : (prefixWord ++ tailWord_2783920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783920).length < 2 ^ (prefixWord ++ tailWord_2783920).sum := by decide
  have hdescent : baseEnd_2783920 < baseStart_2783920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783940 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2783940 : Nat := 118140960795 + 2783940 * 2 ^ 59
def prefixEnd_2783940 : Nat := 4983230072969 + 3 ^ 40 * 2783940 * 2
def baseEnd_2783940 : Nat := 1429499333277943055646899

theorem tailTrace_2783940 : CollatzResearch.WordTrace tailWord_2783940 prefixEnd_2783940 1429499333277943055646899 := by
  unfold tailWord_2783940
  simp only [CollatzResearch.WordTrace]
  refine ⟨50769316767134156971938637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67692422356178875962584849 50769316767134156971938637)
  ·
    refine ⟨19038493787675308864476989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50769316767134156971938637 19038493787675308864476989)
    ·
      refine ⟨7139435170378240824178871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19038493787675308864476989 7139435170378240824178871)
      ·
        refine ⟨10709152755567361236268307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7139435170378240824178871 10709152755567361236268307)
        ·
          refine ⟨16063729133351041854402461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10709152755567361236268307 16063729133351041854402461)
          ·
            refine ⟨6023898425006640695400923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16063729133351041854402461 6023898425006640695400923)
            ·
              refine ⟨9035847637509961043101385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6023898425006640695400923 9035847637509961043101385)
              ·
                refine ⟨6776885728132470782326039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9035847637509961043101385 6776885728132470782326039)
                ·
                  refine ⟨10165328592198706173489059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6776885728132470782326039 10165328592198706173489059)
                  ·
                    refine ⟨15247992888298059260233589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10165328592198706173489059 15247992888298059260233589)
                    ·
                      refine ⟨1429499333277943055646899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15247992888298059260233589 1429499333277943055646899)
                      ·
                        rfl

theorem cell23_2783940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2783940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783940 prefixEnd_2783940 := by exact prefixLift 2783940
  have htrace : WordTrace (prefixWord ++ tailWord_2783940) baseStart_2783940 baseEnd_2783940 := by
    simpa [prefixWord, tailWord_2783940, baseEnd_2783940] using wordTrace_append hprefix tailTrace_2783940
  have hstable : (prefixWord ++ tailWord_2783940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783940).length < 2 ^ (prefixWord ++ tailWord_2783940).sum := by decide
  have hdescent : baseEnd_2783940 < baseStart_2783940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783950 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4]
def baseStart_2783950 : Nat := 118140960795 + 2783950 * 2 ^ 59
def prefixEnd_2783950 : Nat := 4983230072969 + 3 ^ 40 * 2783950 * 2
def baseEnd_2783950 : Nat := 1429504468084488016521853

theorem tailTrace_2783950 : CollatzResearch.WordTrace tailWord_2783950 prefixEnd_2783950 1429504468084488016521853 := by
  unfold tailWord_2783950
  simp only [CollatzResearch.WordTrace]
  refine ⟨12692374783029010706467663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67692665509488057101160869 12692374783029010706467663)
  ·
    refine ⟨19038562174543516059701495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12692374783029010706467663 19038562174543516059701495)
    ·
      refine ⟨28557843261815274089552243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19038562174543516059701495 28557843261815274089552243)
      ·
        refine ⟨42836764892722911134328365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28557843261815274089552243 42836764892722911134328365)
        ·
          refine ⟨16063786834771091675373137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42836764892722911134328365 16063786834771091675373137)
          ·
            refine ⟨12047840126078318756529853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16063786834771091675373137 12047840126078318756529853)
            ·
              refine ⟨4517940047279369533698695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12047840126078318756529853 4517940047279369533698695)
              ·
                refine ⟨6776910070919054300548043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4517940047279369533698695 6776910070919054300548043)
                ·
                  refine ⟨10165365106378581450822065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6776910070919054300548043 10165365106378581450822065)
                  ·
                    refine ⟨7624023829783936088116549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10165365106378581450822065 7624023829783936088116549)
                    ·
                      refine ⟨1429504468084488016521853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7624023829783936088116549 1429504468084488016521853)
                      ·
                        rfl

theorem cell23_2783950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_2783950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783950 prefixEnd_2783950 := by exact prefixLift 2783950
  have htrace : WordTrace (prefixWord ++ tailWord_2783950) baseStart_2783950 baseEnd_2783950 := by
    simpa [prefixWord, tailWord_2783950, baseEnd_2783950] using wordTrace_append hprefix tailTrace_2783950
  have hstable : (prefixWord ++ tailWord_2783950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783950).length < 2 ^ (prefixWord ++ tailWord_2783950).sum := by decide
  have hdescent : baseEnd_2783950 < baseStart_2783950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783960 : List Nat := [2, 1, 2, 2, 3, 4, 2, 7]
def baseStart_2783960 : Nat := 118140960795 + 2783960 * 2 ^ 59
def prefixEnd_2783960 : Nat := 4983230072969 + 3 ^ 40 * 2783960 * 2
def baseEnd_2783960 : Nat := 52944800107075295459141

theorem tailTrace_2783960 : CollatzResearch.WordTrace tailWord_2783960 prefixEnd_2783960 52944800107075295459141 := by
  unfold tailWord_2783960
  simp only [CollatzResearch.WordTrace]
  refine ⟨50769681497097928679802667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67692908662797238239736889 50769681497097928679802667)
  ·
    refine ⟨76154522245646893019704001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50769681497097928679802667 76154522245646893019704001)
    ·
      refine ⟨57115891684235169764778001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76154522245646893019704001 57115891684235169764778001)
      ·
        refine ⟨42836918763176377323583501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57115891684235169764778001 42836918763176377323583501)
        ·
          refine ⟨16063844536191141496343813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42836918763176377323583501 16063844536191141496343813)
          ·
            refine ⟨3011970850535839030564465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16063844536191141496343813 3011970850535839030564465)
            ·
              refine ⟨2258978137901879272923349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3011970850535839030564465 2258978137901879272923349)
              ·
                refine ⟨52944800107075295459141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2258978137901879272923349 52944800107075295459141)
                ·
                  rfl

theorem cell23_2783960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 7].length) (baseStart_2783960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783960 prefixEnd_2783960 := by exact prefixLift 2783960
  have htrace : WordTrace (prefixWord ++ tailWord_2783960) baseStart_2783960 baseEnd_2783960 := by
    simpa [prefixWord, tailWord_2783960, baseEnd_2783960] using wordTrace_append hprefix tailTrace_2783960
  have hstable : (prefixWord ++ tailWord_2783960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783960).length < 2 ^ (prefixWord ++ tailWord_2783960).sum := by decide
  have hdescent : baseEnd_2783960 < baseStart_2783960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783971 : List Nat := [1, 1, 1, 7, 1, 1, 3, 3, 1, 2, 2]
def baseStart_2783971 : Nat := 118140960795 + 2783971 * 2 ^ 59
def prefixEnd_2783971 : Nat := 4983230072969 + 3 ^ 40 * 2783971 * 2
def baseEnd_2783971 : Nat := 1429515251178232434359257

theorem tailTrace_2783971 : CollatzResearch.WordTrace tailWord_2783971 prefixEnd_2783971 1429515251178232434359257 := by
  unfold tailWord_2783971
  simp only [CollatzResearch.WordTrace]
  refine ⟨101539764197156006238255767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67693176131437337492170511 101539764197156006238255767)
  ·
    refine ⟨152309646295734009357383651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101539764197156006238255767 152309646295734009357383651)
    ·
      refine ⟨228464469443601014036075477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152309646295734009357383651 228464469443601014036075477)
      ·
        refine ⟨5354636002584398766470519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 228464469443601014036075477 5354636002584398766470519)
        ·
          refine ⟨8031954003876598149705779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5354636002584398766470519 8031954003876598149705779)
          ·
            refine ⟨12047931005814897224558669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8031954003876598149705779 12047931005814897224558669)
            ·
              refine ⟨4517974127180586459209501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12047931005814897224558669 4517974127180586459209501)
              ·
                refine ⟨1694240297692719922203563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4517974127180586459209501 1694240297692719922203563)
                ·
                  refine ⟨2541360446539079883305345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694240297692719922203563 2541360446539079883305345)
                  ·
                    refine ⟨1906020334904309912479009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2541360446539079883305345 1906020334904309912479009)
                    ·
                      refine ⟨1429515251178232434359257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906020334904309912479009 1429515251178232434359257)
                      ·
                        rfl

theorem cell23_2783971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_2783971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783971 prefixEnd_2783971 := by exact prefixLift 2783971
  have htrace : WordTrace (prefixWord ++ tailWord_2783971) baseStart_2783971 baseEnd_2783971 := by
    simpa [prefixWord, tailWord_2783971, baseEnd_2783971] using wordTrace_append hprefix tailTrace_2783971
  have hstable : (prefixWord ++ tailWord_2783971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783971).length < 2 ^ (prefixWord ++ tailWord_2783971).sum := by decide
  have hdescent : baseEnd_2783971 < baseStart_2783971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783980 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 5, 3, 2]
def baseStart_2783980 : Nat := 118140960795 + 2783980 * 2 ^ 59
def prefixEnd_2783980 : Nat := 4983230072969 + 3 ^ 40 * 2783980 * 2
def baseEnd_2783980 : Nat := 1429519872504122899146715

theorem tailTrace_2783980 : CollatzResearch.WordTrace tailWord_2783980 prefixEnd_2783980 1429519872504122899146715 := by
  unfold tailWord_2783980
  simp only [CollatzResearch.WordTrace]
  refine ⟨50770046227061700387666697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67693394969415600516888929 50770046227061700387666697)
  ·
    refine ⟨38077534670296275290750023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50770046227061700387666697 38077534670296275290750023)
    ·
      refine ⟨57116302005444412936125035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38077534670296275290750023 57116302005444412936125035)
      ·
        refine ⟨85674453008166619404187553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57116302005444412936125035 85674453008166619404187553)
        ·
          refine ⟨64255839756124964553140665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85674453008166619404187553 64255839756124964553140665)
          ·
            refine ⟨48191879817093723414855499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64255839756124964553140665 48191879817093723414855499)
            ·
              refine ⟨72287819725640585122283249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48191879817093723414855499 72287819725640585122283249)
              ·
                refine ⟨54215864794230438841712437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72287819725640585122283249 54215864794230438841712437)
                ·
                  refine ⟨5082737324459103641410541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54215864794230438841712437 5082737324459103641410541)
                  ·
                    refine ⟨1906026496672163865528953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5082737324459103641410541 1906026496672163865528953)
                    ·
                      refine ⟨1429519872504122899146715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906026496672163865528953 1429519872504122899146715)
                      ·
                        rfl

theorem cell23_2783980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 3, 2].length) (baseStart_2783980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2783980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2783980 prefixEnd_2783980 := by exact prefixLift 2783980
  have htrace : WordTrace (prefixWord ++ tailWord_2783980) baseStart_2783980 baseEnd_2783980 := by
    simpa [prefixWord, tailWord_2783980, baseEnd_2783980] using wordTrace_append hprefix tailTrace_2783980
  have hstable : (prefixWord ++ tailWord_2783980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783980).length < 2 ^ (prefixWord ++ tailWord_2783980).sum := by decide
  have hdescent : baseEnd_2783980 < baseStart_2783980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784040 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_2784040 : Nat := 118140960795 + 2784040 * 2 ^ 59
def prefixEnd_2784040 : Nat := 4983230072969 + 3 ^ 40 * 2784040 * 2
def baseEnd_2784040 : Nat := 1429550681343392664396439

theorem tailTrace_2784040 : CollatzResearch.WordTrace tailWord_2784040 prefixEnd_2784040 1429550681343392664396439 := by
  unfold tailWord_2784040
  simp only [CollatzResearch.WordTrace]
  refine ⟨50771140416953015511258787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67694853889270687348345049 50771140416953015511258787)
  ·
    refine ⟨76156710625429523266888181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50771140416953015511258787 76156710625429523266888181)
    ·
      refine ⟨7139691621134017806270767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76156710625429523266888181 7139691621134017806270767)
      ·
        refine ⟨10709537431701026709406151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7139691621134017806270767 10709537431701026709406151)
        ·
          refine ⟨16064306147551540064109227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10709537431701026709406151 16064306147551540064109227)
          ·
            refine ⟨24096459221327310096163841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16064306147551540064109227 24096459221327310096163841)
            ·
              refine ⟨18072344415995482572122881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24096459221327310096163841 18072344415995482572122881)
              ·
                refine ⟨13554258311996611929092161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18072344415995482572122881 13554258311996611929092161)
                ·
                  refine ⟨10165693733997458946819121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13554258311996611929092161 10165693733997458946819121)
                  ·
                    refine ⟨7624270300498094210114341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10165693733997458946819121 7624270300498094210114341)
                    ·
                      refine ⟨1429550681343392664396439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7624270300498094210114341 1429550681343392664396439)
                      ·
                        rfl

theorem cell23_2784040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_2784040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784040 prefixEnd_2784040 := by exact prefixLift 2784040
  have htrace : WordTrace (prefixWord ++ tailWord_2784040) baseStart_2784040 baseEnd_2784040 := by
    simpa [prefixWord, tailWord_2784040, baseEnd_2784040] using wordTrace_append hprefix tailTrace_2784040
  have hstable : (prefixWord ++ tailWord_2784040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784040).length < 2 ^ (prefixWord ++ tailWord_2784040).sum := by decide
  have hdescent : baseEnd_2784040 < baseStart_2784040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784044 : List Nat := [2, 2, 1, 1, 1, 4, 4, 2, 2, 2, 2]
def baseStart_2784044 : Nat := 118140960795 + 2784044 * 2 ^ 59
def prefixEnd_2784044 : Nat := 4983230072969 + 3 ^ 40 * 2784044 * 2
def baseEnd_2784044 : Nat := 1429552735266010648746421

theorem tailTrace_2784044 : CollatzResearch.WordTrace tailWord_2784044 prefixEnd_2784044 1429552735266010648746421 := by
  unfold tailWord_2784044
  simp only [CollatzResearch.WordTrace]
  refine ⟨50771213362945769852831593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67694951150594359803775457 50771213362945769852831593)
  ·
    refine ⟨38078410022209327389623695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50771213362945769852831593 38078410022209327389623695)
    ·
      refine ⟨57117615033313991084435543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38078410022209327389623695 57117615033313991084435543)
      ·
        refine ⟨85676422549970986626653315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57117615033313991084435543 85676422549970986626653315)
        ·
          refine ⟨128514633824956479939979973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85676422549970986626653315 128514633824956479939979973)
          ·
            refine ⟨24096493842179339988746245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128514633824956479939979973 24096493842179339988746245)
            ·
              refine ⟨4518092595408626247889921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24096493842179339988746245 4518092595408626247889921)
              ·
                refine ⟨3388569446556469685917441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4518092595408626247889921 3388569446556469685917441)
                ·
                  refine ⟨2541427084917352264438081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3388569446556469685917441 2541427084917352264438081)
                  ·
                    refine ⟨1906070313688014198328561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2541427084917352264438081 1906070313688014198328561)
                    ·
                      refine ⟨1429552735266010648746421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906070313688014198328561 1429552735266010648746421)
                      ·
                        rfl

theorem cell23_2784044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 2, 2].length) (baseStart_2784044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784044 prefixEnd_2784044 := by exact prefixLift 2784044
  have htrace : WordTrace (prefixWord ++ tailWord_2784044) baseStart_2784044 baseEnd_2784044 := by
    simpa [prefixWord, tailWord_2784044, baseEnd_2784044] using wordTrace_append hprefix tailTrace_2784044
  have hstable : (prefixWord ++ tailWord_2784044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784044).length < 2 ^ (prefixWord ++ tailWord_2784044).sum := by decide
  have hdescent : baseEnd_2784044 < baseStart_2784044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784080 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 2, 5]
def baseStart_2784080 : Nat := 118140960795 + 2784080 * 2 ^ 59
def prefixEnd_2784080 : Nat := 4983230072969 + 3 ^ 40 * 2784080 * 2
def baseEnd_2784080 : Nat := 476523740189857502632085

theorem tailTrace_2784080 : CollatzResearch.WordTrace tailWord_2784080 prefixEnd_2784080 476523740189857502632085 := by
  unfold tailWord_2784080
  simp only [CollatzResearch.WordTrace]
  refine ⟨50771869876880558926986847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67695826502507411902649129 50771869876880558926986847)
  ·
    refine ⟨76157804815320838390480271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50771869876880558926986847 76157804815320838390480271)
    ·
      refine ⟨114236707222981257585720407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76157804815320838390480271 114236707222981257585720407)
      ·
        refine ⟨171355060834471886378580611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114236707222981257585720407 171355060834471886378580611)
        ·
          refine ⟨257032591251707829567870917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171355060834471886378580611 257032591251707829567870917)
          ·
            refine ⟨48193610859695218043975797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257032591251707829567870917 48193610859695218043975797)
            ·
              refine ⟨4518151018096426691622731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48193610859695218043975797 4518151018096426691622731)
              ·
                refine ⟨6777226527144640037434097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4518151018096426691622731 6777226527144640037434097)
                ·
                  refine ⟨5082919895358480028075573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6777226527144640037434097 5082919895358480028075573)
                  ·
                    refine ⟨476523740189857502632085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5082919895358480028075573 476523740189857502632085)
                    ·
                      rfl

theorem cell23_2784080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 2, 5].length) (baseStart_2784080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784080 prefixEnd_2784080 := by exact prefixLift 2784080
  have htrace : WordTrace (prefixWord ++ tailWord_2784080) baseStart_2784080 baseEnd_2784080 := by
    simpa [prefixWord, tailWord_2784080, baseEnd_2784080] using wordTrace_append hprefix tailTrace_2784080
  have hstable : (prefixWord ++ tailWord_2784080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784080).length < 2 ^ (prefixWord ++ tailWord_2784080).sum := by decide
  have hdescent : baseEnd_2784080 < baseStart_2784080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784084 : List Nat := [2, 4, 1, 1, 4, 1, 2, 3, 5]
def baseStart_2784084 : Nat := 118140960795 + 2784084 * 2 ^ 59
def prefixEnd_2784084 : Nat := 4983230072969 + 3 ^ 40 * 2784084 * 2
def baseEnd_2784084 : Nat := 158841474943576721360693

theorem tailTrace_2784084 : CollatzResearch.WordTrace tailWord_2784084 prefixEnd_2784084 158841474943576721360693 := by
  unfold tailWord_2784084
  simp only [CollatzResearch.WordTrace]
  refine ⟨50771942822873313268559653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67695923763831084358079537 50771942822873313268559653)
  ·
    refine ⟨9519739279288746237854935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50771942822873313268559653 9519739279288746237854935)
    ·
      refine ⟨14279608918933119356782403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9519739279288746237854935 14279608918933119356782403)
      ·
        refine ⟨21419413378399679035173605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14279608918933119356782403 21419413378399679035173605)
        ·
          refine ⟨4016140008449939819095051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21419413378399679035173605 4016140008449939819095051)
          ·
            refine ⟨6024210012674909728642577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4016140008449939819095051 6024210012674909728642577)
            ·
              refine ⟨4518157509506182296481933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6024210012674909728642577 4518157509506182296481933)
              ·
                refine ⟨1694309066064818361180725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4518157509506182296481933 1694309066064818361180725)
                ·
                  refine ⟨158841474943576721360693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1694309066064818361180725 158841474943576721360693)
                  ·
                    rfl

theorem cell23_2784084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_2784084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784084 prefixEnd_2784084 := by exact prefixLift 2784084
  have htrace : WordTrace (prefixWord ++ tailWord_2784084) baseStart_2784084 baseEnd_2784084 := by
    simpa [prefixWord, tailWord_2784084, baseEnd_2784084] using wordTrace_append hprefix tailTrace_2784084
  have hstable : (prefixWord ++ tailWord_2784084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784084).length < 2 ^ (prefixWord ++ tailWord_2784084).sum := by decide
  have hdescent : baseEnd_2784084 < baseStart_2784084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784120 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 6, 2, 3]
def baseStart_2784120 : Nat := 118140960795 + 2784120 * 2 ^ 59
def prefixEnd_2784120 : Nat := 4983230072969 + 3 ^ 40 * 2784120 * 2
def baseEnd_2784120 : Nat := 1429591759795752351396071

theorem tailTrace_2784120 : CollatzResearch.WordTrace tailWord_2784120 prefixEnd_2784120 1429591759795752351396071 := by
  unfold tailWord_2784120
  simp only [CollatzResearch.WordTrace]
  refine ⟨50772599336808102342714907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67696799115744136456953209 50772599336808102342714907)
  ·
    refine ⟨76158899005212153514072361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50772599336808102342714907 76158899005212153514072361)
    ·
      refine ⟨57119174253909115135554271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76158899005212153514072361 57119174253909115135554271)
      ·
        refine ⟨85678761380863672703331407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57119174253909115135554271 85678761380863672703331407)
        ·
          refine ⟨128518142071295509054997111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85678761380863672703331407 128518142071295509054997111)
          ·
            refine ⟨192777213106943263582495667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128518142071295509054997111 192777213106943263582495667)
            ·
              refine ⟨289165819660414895373743501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192777213106943263582495667 289165819660414895373743501)
              ·
                refine ⟨108437182372655585765153813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289165819660414895373743501 108437182372655585765153813)
                ·
                  refine ⟨5082992923718230582741585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108437182372655585765153813 5082992923718230582741585)
                  ·
                    refine ⟨3812244692788672937056189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5082992923718230582741585 3812244692788672937056189)
                    ·
                      refine ⟨1429591759795752351396071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3812244692788672937056189 1429591759795752351396071)
                      ·
                        rfl

theorem cell23_2784120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_2784120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784120 prefixEnd_2784120 := by exact prefixLift 2784120
  have htrace : WordTrace (prefixWord ++ tailWord_2784120) baseStart_2784120 baseEnd_2784120 := by
    simpa [prefixWord, tailWord_2784120, baseEnd_2784120] using wordTrace_append hprefix tailTrace_2784120
  have hstable : (prefixWord ++ tailWord_2784120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784120).length < 2 ^ (prefixWord ++ tailWord_2784120).sum := by decide
  have hdescent : baseEnd_2784120 < baseStart_2784120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784143 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 6]
def baseStart_2784143 : Nat := 118140960795 + 2784143 * 2 ^ 59
def prefixEnd_2784143 : Nat := 4983230072969 + 3 ^ 40 * 2784143 * 2
def baseEnd_2784143 : Nat := 1429603569850805761408465

theorem tailTrace_2784143 : CollatzResearch.WordTrace tailWord_2784143 prefixEnd_2784143 1429603569850805761408465 := by
  unfold tailWord_2784143
  simp only [CollatzResearch.WordTrace]
  refine ⟨101546037552532879613517083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67697358368355253075678055 101546037552532879613517083)
  ·
    refine ⟨152319056328799319420275625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101546037552532879613517083 152319056328799319420275625)
    ·
      refine ⟨114239292246599489565206719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152319056328799319420275625 114239292246599489565206719)
      ·
        refine ⟨171358938369899234347810079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114239292246599489565206719 171358938369899234347810079)
        ·
          refine ⟨257038407554848851521715119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171358938369899234347810079 257038407554848851521715119)
          ·
            refine ⟨385557611332273277282572679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257038407554848851521715119 385557611332273277282572679)
            ·
              refine ⟨578336416998409915923859019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385557611332273277282572679 578336416998409915923859019)
              ·
                refine ⟨867504625497614873885788529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578336416998409915923859019 867504625497614873885788529)
                ·
                  refine ⟨650628469123211155414341397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 867504625497614873885788529 650628469123211155414341397)
                  ·
                    refine ⟨30498209490150522910047253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 650628469123211155414341397 30498209490150522910047253)
                    ·
                      refine ⟨1429603569850805761408465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30498209490150522910047253 1429603569850805761408465)
                      ·
                        rfl

theorem cell23_2784143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_2784143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784143 prefixEnd_2784143 := by exact prefixLift 2784143
  have htrace : WordTrace (prefixWord ++ tailWord_2784143) baseStart_2784143 baseEnd_2784143 := by
    simpa [prefixWord, tailWord_2784143, baseEnd_2784143] using wordTrace_append hprefix tailTrace_2784143
  have hstable : (prefixWord ++ tailWord_2784143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784143).length < 2 ^ (prefixWord ++ tailWord_2784143).sum := by decide
  have hdescent : baseEnd_2784143 < baseStart_2784143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784154 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3]
def baseStart_2784154 : Nat := 118140960795 + 2784154 * 2 ^ 59
def prefixEnd_2784154 : Nat := 4983230072969 + 3 ^ 40 * 2784154 * 2
def baseEnd_2784154 : Nat := 1429609218138005218370915

theorem tailTrace_2784154 : CollatzResearch.WordTrace tailWord_2784154 prefixEnd_2784154 1429609218138005218370915 := by
  unfold tailWord_2784154
  simp only [CollatzResearch.WordTrace]
  refine ⟨25386609688873257123041879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67697625836995352328111677 25386609688873257123041879)
  ·
    refine ⟨38079914533309885684562819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25386609688873257123041879 38079914533309885684562819)
    ·
      refine ⟨57119871799964828526844229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38079914533309885684562819 57119871799964828526844229)
      ·
        refine ⟨10709975962493405348783293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57119871799964828526844229 10709975962493405348783293)
        ·
          refine ⟨4016240985935027005793735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10709975962493405348783293 4016240985935027005793735)
          ·
            refine ⟨6024361478902540508690603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4016240985935027005793735 6024361478902540508690603)
            ·
              refine ⟨9036542218353810763035905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6024361478902540508690603 9036542218353810763035905)
              ·
                refine ⟨6777406663765358072276929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9036542218353810763035905 6777406663765358072276929)
                ·
                  refine ⟨5083054997824018554207697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6777406663765358072276929 5083054997824018554207697)
                  ·
                    refine ⟨3812291248368013915655773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5083054997824018554207697 3812291248368013915655773)
                    ·
                      refine ⟨1429609218138005218370915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3812291248368013915655773 1429609218138005218370915)
                      ·
                        rfl

theorem cell23_2784154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_2784154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784154 prefixEnd_2784154 := by exact prefixLift 2784154
  have htrace : WordTrace (prefixWord ++ tailWord_2784154) baseStart_2784154 baseEnd_2784154 := by
    simpa [prefixWord, tailWord_2784154, baseEnd_2784154] using wordTrace_append hprefix tailTrace_2784154
  have hstable : (prefixWord ++ tailWord_2784154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784154).length < 2 ^ (prefixWord ++ tailWord_2784154).sum := by decide
  have hdescent : baseEnd_2784154 < baseStart_2784154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784204 : List Nat := [2, 2, 1, 4, 1, 1, 5, 1, 1, 5]
def baseStart_2784204 : Nat := 118140960795 + 2784204 * 2 ^ 59
def prefixEnd_2784204 : Nat := 4983230072969 + 3 ^ 40 * 2784204 * 2
def baseEnd_2784204 : Nat := 476544964056910007581895

theorem tailTrace_2784204 : CollatzResearch.WordTrace tailWord_2784204 prefixEnd_2784204 476544964056910007581895 := by
  unfold tailWord_2784204
  simp only [CollatzResearch.WordTrace]
  refine ⟨50774131202655943515743833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67698841603541258020991777 50774131202655943515743833)
  ·
    refine ⟨38080598401991957636807875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50774131202655943515743833 38080598401991957636807875)
    ·
      refine ⟨57120897602987936455211813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38080598401991957636807875 57120897602987936455211813)
      ·
        refine ⟨10710168300560238085352215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57120897602987936455211813 10710168300560238085352215)
        ·
          refine ⟨16065252450840357128028323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10710168300560238085352215 16065252450840357128028323)
          ·
            refine ⟨24097878676260535692042485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16065252450840357128028323 24097878676260535692042485)
            ·
              refine ⟨2259176125899425221128983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24097878676260535692042485 2259176125899425221128983)
              ·
                refine ⟨3388764188849137831693475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2259176125899425221128983 3388764188849137831693475)
                ·
                  refine ⟨5083146283273706747540213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3388764188849137831693475 5083146283273706747540213)
                  ·
                    refine ⟨476544964056910007581895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5083146283273706747540213 476544964056910007581895)
                    ·
                      rfl

theorem cell23_2784204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_2784204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784204 prefixEnd_2784204 := by exact prefixLift 2784204
  have htrace : WordTrace (prefixWord ++ tailWord_2784204) baseStart_2784204 baseEnd_2784204 := by
    simpa [prefixWord, tailWord_2784204, baseEnd_2784204] using wordTrace_append hprefix tailTrace_2784204
  have hstable : (prefixWord ++ tailWord_2784204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784204).length < 2 ^ (prefixWord ++ tailWord_2784204).sum := by decide
  have hdescent : baseEnd_2784204 < baseStart_2784204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784218 : List Nat := [3, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3]
def baseStart_2784218 : Nat := 118140960795 + 2784218 * 2 ^ 59
def prefixEnd_2784218 : Nat := 4983230072969 + 3 ^ 40 * 2784218 * 2
def baseEnd_2784218 : Nat := 1429642080899892967970621

theorem tailTrace_2784218 : CollatzResearch.WordTrace tailWord_2784218 prefixEnd_2784218 1429642080899892967970621 := by
  unfold tailWord_2784218
  simp only [CollatzResearch.WordTrace]
  refine ⟨25387193256815291855624327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67699182018174111614998205 25387193256815291855624327)
  ·
    refine ⟨38080789885222937783436491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25387193256815291855624327 38080789885222937783436491)
    ·
      refine ⟨57121184827834406675154737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38080789885222937783436491 57121184827834406675154737)
      ·
        refine ⟨42840888620875805006366053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57121184827834406675154737 42840888620875805006366053)
        ·
          refine ⟨8032666616414213438693635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42840888620875805006366053 8032666616414213438693635)
          ·
            refine ⟨12048999924621320158040453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8032666616414213438693635 12048999924621320158040453)
            ·
              refine ⟨2259187485866497529632585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12048999924621320158040453 2259187485866497529632585)
              ·
                refine ⟨1694390614399873147224439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2259187485866497529632585 1694390614399873147224439)
                ·
                  refine ⟨2541585921599809720836659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694390614399873147224439 2541585921599809720836659)
                  ·
                    refine ⟨3812378882399714581254989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2541585921599809720836659 3812378882399714581254989)
                    ·
                      refine ⟨1429642080899892967970621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3812378882399714581254989 1429642080899892967970621)
                      ·
                        rfl

theorem cell23_2784218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_2784218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784218 prefixEnd_2784218 := by exact prefixLift 2784218
  have htrace : WordTrace (prefixWord ++ tailWord_2784218) baseStart_2784218 baseEnd_2784218 := by
    simpa [prefixWord, tailWord_2784218, baseEnd_2784218] using wordTrace_append hprefix tailTrace_2784218
  have hstable : (prefixWord ++ tailWord_2784218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784218).length < 2 ^ (prefixWord ++ tailWord_2784218).sum := by decide
  have hdescent : baseEnd_2784218 < baseStart_2784218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784227 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 3]
def baseStart_2784227 : Nat := 118140960795 + 2784227 * 2 ^ 59
def prefixEnd_2784227 : Nat := 4983230072969 + 3 ^ 40 * 2784227 * 2
def baseEnd_2784227 : Nat := 1429646702225783432758079

theorem tailTrace_2784227 : CollatzResearch.WordTrace tailWord_2784227 prefixEnd_2784227 1429646702225783432758079 := by
  unfold tailWord_2784227
  simp only [CollatzResearch.WordTrace]
  refine ⟨101549101284228561959574935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67699400856152374639716623 101549101284228561959574935)
  ·
    refine ⟨152323651926342842939362403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101549101284228561959574935 152323651926342842939362403)
    ·
      refine ⟨228485477889514264409043605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152323651926342842939362403 228485477889514264409043605)
      ·
        refine ⟨10710256776070981144173919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 228485477889514264409043605 10710256776070981144173919)
        ·
          refine ⟨16065385164106471716260879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10710256776070981144173919 16065385164106471716260879)
          ·
            refine ⟨24098077746159707574391319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16065385164106471716260879 24098077746159707574391319)
            ·
              refine ⟨36147116619239561361586979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24098077746159707574391319 36147116619239561361586979)
              ·
                refine ⟨54220674928859342042380469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36147116619239561361586979 54220674928859342042380469)
                ·
                  refine ⟨5083188274580563316473169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54220674928859342042380469 5083188274580563316473169)
                  ·
                    refine ⟨3812391205935422487354877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5083188274580563316473169 3812391205935422487354877)
                    ·
                      refine ⟨1429646702225783432758079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3812391205935422487354877 1429646702225783432758079)
                      ·
                        rfl

theorem cell23_2784227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_2784227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784227 prefixEnd_2784227 := by exact prefixLift 2784227
  have htrace : WordTrace (prefixWord ++ tailWord_2784227) baseStart_2784227 baseEnd_2784227 := by
    simpa [prefixWord, tailWord_2784227, baseEnd_2784227] using wordTrace_append hprefix tailTrace_2784227
  have hstable : (prefixWord ++ tailWord_2784227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784227).length < 2 ^ (prefixWord ++ tailWord_2784227).sum := by decide
  have hdescent : baseEnd_2784227 < baseStart_2784227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784234 : List Nat := [3, 1, 3, 1, 2, 2, 2, 3, 2, 4]
def baseStart_2784234 : Nat := 118140960795 + 2784234 * 2 ^ 59
def prefixEnd_2784234 : Nat := 4983230072969 + 3 ^ 40 * 2784234 * 2
def baseEnd_2784234 : Nat := 476550098863454968456849

theorem tailTrace_2784234 : CollatzResearch.WordTrace tailWord_2784234 prefixEnd_2784234 476550098863454968456849 := by
  unfold tailWord_2784234
  simp only [CollatzResearch.WordTrace]
  refine ⟨25387339148800800538769939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67699571063468801436719837 25387339148800800538769939)
  ·
    refine ⟨38081008723201200808154909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25387339148800800538769939 38081008723201200808154909)
    ·
      refine ⟨14280378271200450303058091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38081008723201200808154909 14280378271200450303058091)
      ·
        refine ⟨21420567406800675454587137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14280378271200450303058091 21420567406800675454587137)
        ·
          refine ⟨16065425555100506590940353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21420567406800675454587137 16065425555100506590940353)
          ·
            refine ⟨12049069166325379943205265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16065425555100506590940353 12049069166325379943205265)
            ·
              refine ⟨9036801874744034957403949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12049069166325379943205265 9036801874744034957403949)
              ·
                refine ⟨3388800703029013109026481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9036801874744034957403949 3388800703029013109026481)
                ·
                  refine ⟨2541600527271759831769861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3388800703029013109026481 2541600527271759831769861)
                  ·
                    refine ⟨476550098863454968456849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2541600527271759831769861 476550098863454968456849)
                    ·
                      rfl

theorem cell23_2784234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_2784234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784234 prefixEnd_2784234 := by exact prefixLift 2784234
  have htrace : WordTrace (prefixWord ++ tailWord_2784234) baseStart_2784234 baseEnd_2784234 := by
    simpa [prefixWord, tailWord_2784234, baseEnd_2784234] using wordTrace_append hprefix tailTrace_2784234
  have hstable : (prefixWord ++ tailWord_2784234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784234).length < 2 ^ (prefixWord ++ tailWord_2784234).sum := by decide
  have hdescent : baseEnd_2784234 < baseStart_2784234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784241 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 3, 2, 2]
def baseStart_2784241 : Nat := 118140960795 + 2784241 * 2 ^ 59
def prefixEnd_2784241 : Nat := 4983230072969 + 3 ^ 40 * 2784241 * 2
def baseEnd_2784241 : Nat := 1429653890954946377983015

theorem tailTrace_2784241 : CollatzResearch.WordTrace tailWord_2784241 prefixEnd_2784241 1429653890954946377983015 := by
  unfold tailWord_2784241
  simp only [CollatzResearch.WordTrace]
  refine ⟨101549611906177842350584577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67699741270785228233723051 101549611906177842350584577)
  ·
    refine ⟨76162208929633381762938433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101549611906177842350584577 76162208929633381762938433)
    ·
      refine ⟨57121656697225036322203825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76162208929633381762938433 57121656697225036322203825)
      ·
        refine ⟨42841242522918777241652869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57121656697225036322203825 42841242522918777241652869)
        ·
          refine ⟨8032732973047270732809913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42841242522918777241652869 8032732973047270732809913)
          ·
            refine ⟨6024549729785453049607435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8032732973047270732809913 6024549729785453049607435)
            ·
              refine ⟨9036824594678179574411153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6024549729785453049607435 9036824594678179574411153)
              ·
                refine ⟨6777618446008634680808365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9036824594678179574411153 6777618446008634680808365)
                ·
                  refine ⟨2541606917253238005303137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6777618446008634680808365 2541606917253238005303137)
                  ·
                    refine ⟨1906205187939928503977353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2541606917253238005303137 1906205187939928503977353)
                    ·
                      refine ⟨1429653890954946377983015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906205187939928503977353 1429653890954946377983015)
                      ·
                        rfl

theorem cell23_2784241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_2784241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784241 prefixEnd_2784241 := by exact prefixLift 2784241
  have htrace : WordTrace (prefixWord ++ tailWord_2784241) baseStart_2784241 baseEnd_2784241 := by
    simpa [prefixWord, tailWord_2784241, baseEnd_2784241] using wordTrace_append hprefix tailTrace_2784241
  have hstable : (prefixWord ++ tailWord_2784241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784241).length < 2 ^ (prefixWord ++ tailWord_2784241).sum := by decide
  have hdescent : baseEnd_2784241 < baseStart_2784241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784245 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_2784245 : Nat := 118140960795 + 2784245 * 2 ^ 59
def prefixEnd_2784245 : Nat := 4983230072969 + 3 ^ 40 * 2784245 * 2
def baseEnd_2784245 : Nat := 1429655944877564362332997

theorem tailTrace_2784245 : CollatzResearch.WordTrace tailWord_2784245 prefixEnd_2784245 1429655944877564362332997 := by
  unfold tailWord_2784245
  simp only [CollatzResearch.WordTrace]
  refine ⟨101549757798163351033730189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67699838532108900689153459 101549757798163351033730189)
  ·
    refine ⟨38081159174311256637648821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101549757798163351033730189 38081159174311256637648821)
    ·
      refine ⟨3570108672591680309779577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38081159174311256637648821 3570108672591680309779577)
      ·
        refine ⟨2677581504443760232334683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3570108672591680309779577 2677581504443760232334683)
        ·
          refine ⟨4016372256665640348502025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2677581504443760232334683 4016372256665640348502025)
          ·
            refine ⟨3012279192499230261376519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4016372256665640348502025 3012279192499230261376519)
            ·
              refine ⟨4518418788748845392064779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012279192499230261376519 4518418788748845392064779)
              ·
                refine ⟨6777628183123268088097169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4518418788748845392064779 6777628183123268088097169)
                ·
                  refine ⟨5083221137342451066072877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6777628183123268088097169 5083221137342451066072877)
                  ·
                    refine ⟨1906207926503419149777329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5083221137342451066072877 1906207926503419149777329)
                    ·
                      refine ⟨1429655944877564362332997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906207926503419149777329 1429655944877564362332997)
                      ·
                        rfl

theorem cell23_2784245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_2784245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784245 prefixEnd_2784245 := by exact prefixLift 2784245
  have htrace : WordTrace (prefixWord ++ tailWord_2784245) baseStart_2784245 baseEnd_2784245 := by
    simpa [prefixWord, tailWord_2784245, baseEnd_2784245] using wordTrace_append hprefix tailTrace_2784245
  have hstable : (prefixWord ++ tailWord_2784245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784245).length < 2 ^ (prefixWord ++ tailWord_2784245).sum := by decide
  have hdescent : baseEnd_2784245 < baseStart_2784245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784258 : List Nat := [3, 4, 1, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2784258 : Nat := 118140960795 + 2784258 * 2 ^ 59
def prefixEnd_2784258 : Nat := 4983230072969 + 3 ^ 40 * 2784258 * 2
def baseEnd_2784258 : Nat := 1429662620126072811470437

theorem tailTrace_2784258 : CollatzResearch.WordTrace tailWord_2784258 prefixEnd_2784258 1429662620126072811470437 := by
  unfold tailWord_2784258
  simp only [CollatzResearch.WordTrace]
  refine ⟨25387557986779063563488357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67700154631410836169302285 25387557986779063563488357)
  ·
    refine ⟨4760167122521074418154067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25387557986779063563488357 4760167122521074418154067)
    ·
      refine ⟨7140250683781611627231101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4760167122521074418154067 7140250683781611627231101)
      ·
        refine ⟨2677594006418104360211663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7140250683781611627231101 2677594006418104360211663)
        ·
          refine ⟨4016391009627156540317495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2677594006418104360211663 4016391009627156540317495)
          ·
            refine ⟨6024586514440734810476243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4016391009627156540317495 6024586514440734810476243)
            ·
              refine ⟨9036879771661102215714365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6024586514440734810476243 9036879771661102215714365)
              ·
                refine ⟨3388829914372913330892887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9036879771661102215714365 3388829914372913330892887)
                ·
                  refine ⟨5083244871559369996339331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3388829914372913330892887 5083244871559369996339331)
                  ·
                    refine ⟨7624867307339054994508997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5083244871559369996339331 7624867307339054994508997)
                    ·
                      refine ⟨1429662620126072811470437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7624867307339054994508997 1429662620126072811470437)
                      ·
                        rfl

theorem cell23_2784258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2784258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784258 prefixEnd_2784258 := by exact prefixLift 2784258
  have htrace : WordTrace (prefixWord ++ tailWord_2784258) baseStart_2784258 baseEnd_2784258 := by
    simpa [prefixWord, tailWord_2784258, baseEnd_2784258] using wordTrace_append hprefix tailTrace_2784258
  have hstable : (prefixWord ++ tailWord_2784258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784258).length < 2 ^ (prefixWord ++ tailWord_2784258).sum := by decide
  have hdescent : baseEnd_2784258 < baseStart_2784258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784288 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 1, 2, 4]
def baseStart_2784288 : Nat := 118140960795 + 2784288 * 2 ^ 59
def prefixEnd_2784288 : Nat := 4983230072969 + 3 ^ 40 * 2784288 * 2
def baseEnd_2784288 : Nat := 1429678024545707694095299

theorem tailTrace_2784288 : CollatzResearch.WordTrace tailWord_2784288 prefixEnd_2784288 1429678024545707694095299 := by
  unfold tailWord_2784288
  simp only [CollatzResearch.WordTrace]
  refine ⟨50775663068503784688772759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67700884091338379585030345 50775663068503784688772759)
  ·
    refine ⟨76163494602755677033159139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50775663068503784688772759 76163494602755677033159139)
    ·
      refine ⟨114245241904133515549738709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76163494602755677033159139 114245241904133515549738709)
      ·
        refine ⟨2677622857128129270697001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 114245241904133515549738709 2677622857128129270697001)
        ·
          refine ⟨2008217142846096953022751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2677622857128129270697001 2008217142846096953022751)
          ·
            refine ⟨3012325714269145429534127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008217142846096953022751 3012325714269145429534127)
            ·
              refine ⟨4518488571403718144301191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012325714269145429534127 4518488571403718144301191)
              ·
                refine ⟨6777732857105577216451787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4518488571403718144301191 6777732857105577216451787)
                ·
                  refine ⟨10166599285658365824677681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6777732857105577216451787 10166599285658365824677681)
                  ·
                    refine ⟨7624949464243774368508261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10166599285658365824677681 7624949464243774368508261)
                    ·
                      refine ⟨1429678024545707694095299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7624949464243774368508261 1429678024545707694095299)
                      ·
                        rfl

theorem cell23_2784288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_2784288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784288 prefixEnd_2784288 := by exact prefixLift 2784288
  have htrace : WordTrace (prefixWord ++ tailWord_2784288) baseStart_2784288 baseEnd_2784288 := by
    simpa [prefixWord, tailWord_2784288, baseEnd_2784288] using wordTrace_append hprefix tailTrace_2784288
  have hstable : (prefixWord ++ tailWord_2784288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784288).length < 2 ^ (prefixWord ++ tailWord_2784288).sum := by decide
  have hdescent : baseEnd_2784288 < baseStart_2784288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784314 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2]
def baseStart_2784314 : Nat := 118140960795 + 2784314 * 2 ^ 59
def prefixEnd_2784314 : Nat := 4983230072969 + 3 ^ 40 * 2784314 * 2
def baseEnd_2784314 : Nat := 1429691375042724592370179

theorem tailTrace_2784314 : CollatzResearch.WordTrace tailWord_2784314 prefixEnd_2784314 1429691375042724592370179 := by
  unfold tailWord_2784314
  simp only [CollatzResearch.WordTrace]
  refine ⟨25388068608728343954497999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67701516289942250545327997 25388068608728343954497999)
  ·
    refine ⟨38082102913092515931746999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25388068608728343954497999 38082102913092515931746999)
    ·
      refine ⟨57123154369638773897620499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38082102913092515931746999 57123154369638773897620499)
      ·
        refine ⟨85684731554458160846430749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57123154369638773897620499 85684731554458160846430749)
        ·
          refine ⟨32131774332921810317411531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85684731554458160846430749 32131774332921810317411531)
          ·
            refine ⟨48197661499382715476117297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32131774332921810317411531 48197661499382715476117297)
            ·
              refine ⟨36148246124537036607087973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48197661499382715476117297 36148246124537036607087973)
              ·
                refine ⟨6777796148350694363828995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36148246124537036607087973 6777796148350694363828995)
                ·
                  refine ⟨10166694222526041545743493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6777796148350694363828995 10166694222526041545743493)
                  ·
                    refine ⟨1906255166723632789826905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10166694222526041545743493 1906255166723632789826905)
                    ·
                      refine ⟨1429691375042724592370179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906255166723632789826905 1429691375042724592370179)
                      ·
                        rfl

theorem cell23_2784314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2].length) (baseStart_2784314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784314 prefixEnd_2784314 := by exact prefixLift 2784314
  have htrace : WordTrace (prefixWord ++ tailWord_2784314) baseStart_2784314 baseEnd_2784314 := by
    simpa [prefixWord, tailWord_2784314, baseEnd_2784314] using wordTrace_append hprefix tailTrace_2784314
  have hstable : (prefixWord ++ tailWord_2784314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784314).length < 2 ^ (prefixWord ++ tailWord_2784314).sum := by decide
  have hdescent : baseEnd_2784314 < baseStart_2784314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784317 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_2784317 : Nat := 118140960795 + 2784317 * 2 ^ 59
def prefixEnd_2784317 : Nat := 4983230072969 + 3 ^ 40 * 2784317 * 2
def baseEnd_2784317 : Nat := 1429692915484688080632665

theorem tailTrace_2784317 : CollatzResearch.WordTrace tailWord_2784317 prefixEnd_2784317 1429692915484688080632665 := by
  unfold tailWord_2784317
  simp only [CollatzResearch.WordTrace]
  refine ⟨101552383853902507330351205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67701589235935004886900803 101552383853902507330351205)
  ·
    refine ⟨19041071972606720124440851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101552383853902507330351205 19041071972606720124440851)
    ·
      refine ⟨28561607958910080186661277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19041071972606720124440851 28561607958910080186661277)
      ·
        refine ⟨10710602984591280069997979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28561607958910080186661277 10710602984591280069997979)
        ·
          refine ⟨16065904476886920104996969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10710602984591280069997979 16065904476886920104996969)
          ·
            refine ⟨12049428357665190078747727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16065904476886920104996969 12049428357665190078747727)
            ·
              refine ⟨18074142536497785118121591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12049428357665190078747727 18074142536497785118121591)
              ·
                refine ⟨27111213804746677677182387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18074142536497785118121591 27111213804746677677182387)
                ·
                  refine ⟨40666820707120016515773581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27111213804746677677182387 40666820707120016515773581)
                  ·
                    refine ⟨15250057765170006193415093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40666820707120016515773581 15250057765170006193415093)
                    ·
                      refine ⟨1429692915484688080632665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15250057765170006193415093 1429692915484688080632665)
                      ·
                        rfl

theorem cell23_2784317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_2784317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784317 prefixEnd_2784317 := by exact prefixLift 2784317
  have htrace : WordTrace (prefixWord ++ tailWord_2784317) baseStart_2784317 baseEnd_2784317 := by
    simpa [prefixWord, tailWord_2784317, baseEnd_2784317] using wordTrace_append hprefix tailTrace_2784317
  have hstable : (prefixWord ++ tailWord_2784317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784317).length < 2 ^ (prefixWord ++ tailWord_2784317).sum := by decide
  have hdescent : baseEnd_2784317 < baseStart_2784317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784318 : List Nat := [4, 2, 1, 3, 1, 1, 2, 3, 1, 3, 2]
def baseStart_2784318 : Nat := 118140960795 + 2784318 * 2 ^ 59
def prefixEnd_2784318 : Nat := 4983230072969 + 3 ^ 40 * 2784318 * 2
def baseEnd_2784318 : Nat := 1429693428965342576720161

theorem tailTrace_2784318 : CollatzResearch.WordTrace tailWord_2784318 prefixEnd_2784318 1429693428965342576720161 := by
  unfold tailWord_2784318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12694052540862360562642201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67701613551265923000758405 12694052540862360562642201)
  ·
    refine ⟨9520539405646770421981651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12694052540862360562642201 9520539405646770421981651)
    ·
      refine ⟨14280809108470155632972477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9520539405646770421981651 14280809108470155632972477)
      ·
        refine ⟨5355303415676308362364679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14280809108470155632972477 5355303415676308362364679)
        ·
          refine ⟨8032955123514462543547019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5355303415676308362364679 8032955123514462543547019)
          ·
            refine ⟨12049432685271693815320529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8032955123514462543547019 12049432685271693815320529)
            ·
              refine ⟨9037074513953770361490397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12049432685271693815320529 9037074513953770361490397)
              ·
                refine ⟨3388902942732663885558899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9037074513953770361490397 3388902942732663885558899)
                ·
                  refine ⟨5083354414098995828338349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3388902942732663885558899 5083354414098995828338349)
                  ·
                    refine ⟨1906257905287123435626881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5083354414098995828338349 1906257905287123435626881)
                    ·
                      refine ⟨1429693428965342576720161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906257905287123435626881 1429693428965342576720161)
                      ·
                        rfl

theorem cell23_2784318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_2784318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784318 prefixEnd_2784318 := by exact prefixLift 2784318
  have htrace : WordTrace (prefixWord ++ tailWord_2784318) baseStart_2784318 baseEnd_2784318 := by
    simpa [prefixWord, tailWord_2784318, baseEnd_2784318] using wordTrace_append hprefix tailTrace_2784318
  have hstable : (prefixWord ++ tailWord_2784318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784318).length < 2 ^ (prefixWord ++ tailWord_2784318).sum := by decide
  have hdescent : baseEnd_2784318 < baseStart_2784318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784337 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 7]
def baseStart_2784337 : Nat := 118140960795 + 2784337 * 2 ^ 59
def prefixEnd_2784337 : Nat := 4983230072969 + 3 ^ 40 * 2784337 * 2
def baseEnd_2784337 : Nat := 158855909455308666931397

theorem tailTrace_2784337 : CollatzResearch.WordTrace tailWord_2784337 prefixEnd_2784337 158855909455308666931397 := by
  unfold tailWord_2784337
  simp only [CollatzResearch.WordTrace]
  refine ⟨101553113313830050746079265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67702075542553367164052843 101553113313830050746079265)
  ·
    refine ⟨76164834985372538059559449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101553113313830050746079265 76164834985372538059559449)
    ·
      refine ⟨57123626239029403544669587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76164834985372538059559449 57123626239029403544669587)
      ·
        refine ⟨85685439358544105317004381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57123626239029403544669587 85685439358544105317004381)
        ·
          refine ⟨32132039759454039493876643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85685439358544105317004381 32132039759454039493876643)
          ·
            refine ⟨48198059639181059240814965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32132039759454039493876643 48198059639181059240814965)
            ·
              refine ⟨4518568091173224303826403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48198059639181059240814965 4518568091173224303826403)
              ·
                refine ⟨6777852136759836455739605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4518568091173224303826403 6777852136759836455739605)
                ·
                  refine ⟨158855909455308666931397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6777852136759836455739605 158855909455308666931397)
                  ·
                    rfl

theorem cell23_2784337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 7].length) (baseStart_2784337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784337 prefixEnd_2784337 := by exact prefixLift 2784337
  have htrace : WordTrace (prefixWord ++ tailWord_2784337) baseStart_2784337 baseEnd_2784337 := by
    simpa [prefixWord, tailWord_2784337, baseEnd_2784337] using wordTrace_append hprefix tailTrace_2784337
  have hstable : (prefixWord ++ tailWord_2784337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784337).length < 2 ^ (prefixWord ++ tailWord_2784337).sum := by decide
  have hdescent : baseEnd_2784337 < baseStart_2784337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784348 : List Nat := [2, 2, 4, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_2784348 : Nat := 118140960795 + 2784348 * 2 ^ 59
def prefixEnd_2784348 : Nat := 4983230072969 + 3 ^ 40 * 2784348 * 2
def baseEnd_2784348 : Nat := 1429708833384977459345023

theorem tailTrace_2784348 : CollatzResearch.WordTrace tailWord_2784348 prefixEnd_2784348 1429708833384977459345023 := by
  unfold tailWord_2784348
  simp only [CollatzResearch.WordTrace]
  refine ⟨50776757258395099812364849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67702343011193466416486465 50776757258395099812364849)
  ·
    refine ⟨38082567943796324859273637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50776757258395099812364849 38082567943796324859273637)
    ·
      refine ⟨7140481489461810911113807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38082567943796324859273637 7140481489461810911113807)
      ·
        refine ⟨10710722234192716366670711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7140481489461810911113807 10710722234192716366670711)
        ·
          refine ⟨16066083351289074550006067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10710722234192716366670711 16066083351289074550006067)
          ·
            refine ⟨24099125026933611825009101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16066083351289074550006067 24099125026933611825009101)
            ·
              refine ⟨9037171885100104434378413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24099125026933611825009101 9037171885100104434378413)
              ·
                refine ⟨3388939456912539162891905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9037171885100104434378413 3388939456912539162891905)
                ·
                  refine ⟨2541704592684404372168929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3388939456912539162891905 2541704592684404372168929)
                  ·
                    refine ⟨1906278444513303279126697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2541704592684404372168929 1906278444513303279126697)
                    ·
                      refine ⟨1429708833384977459345023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906278444513303279126697 1429708833384977459345023)
                      ·
                        rfl

theorem cell23_2784348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_2784348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784348 prefixEnd_2784348 := by exact prefixLift 2784348
  have htrace : WordTrace (prefixWord ++ tailWord_2784348) baseStart_2784348 baseEnd_2784348 := by
    simpa [prefixWord, tailWord_2784348, baseEnd_2784348] using wordTrace_append hprefix tailTrace_2784348
  have hstable : (prefixWord ++ tailWord_2784348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784348).length < 2 ^ (prefixWord ++ tailWord_2784348).sum := by decide
  have hdescent : baseEnd_2784348 < baseStart_2784348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784388 : List Nat := [2, 3, 2, 1, 2, 4, 2, 2, 5]
def baseStart_2784388 : Nat := 118140960795 + 2784388 * 2 ^ 59
def prefixEnd_2784388 : Nat := 4983230072969 + 3 ^ 40 * 2784388 * 2
def baseEnd_2784388 : Nat := 158858819179017478093871

theorem tailTrace_2784388 : CollatzResearch.WordTrace tailWord_2784388 prefixEnd_2784388 158858819179017478093871 := by
  unfold tailWord_2784388
  simp only [CollatzResearch.WordTrace]
  refine ⟨50777486718322643228092909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67703315624430190970790545 50777486718322643228092909)
  ·
    refine ⟨19041557519370991210534841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50777486718322643228092909 19041557519370991210534841)
    ·
      refine ⟨14281168139528243407901131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19041557519370991210534841 14281168139528243407901131)
      ·
        refine ⟨21421752209292365111851697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14281168139528243407901131 21421752209292365111851697)
        ·
          refine ⟨16066314156969273833888773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21421752209292365111851697 16066314156969273833888773)
          ·
            refine ⟨3012433904431738843854145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16066314156969273833888773 3012433904431738843854145)
            ·
              refine ⟨2259325428323804132890609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3012433904431738843854145 2259325428323804132890609)
              ·
                refine ⟨1694494071242853099667957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2259325428323804132890609 1694494071242853099667957)
                ·
                  refine ⟨158858819179017478093871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1694494071242853099667957 158858819179017478093871)
                  ·
                    rfl

theorem cell23_2784388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_2784388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784388 prefixEnd_2784388 := by exact prefixLift 2784388
  have htrace : WordTrace (prefixWord ++ tailWord_2784388) baseStart_2784388 baseEnd_2784388 := by
    simpa [prefixWord, tailWord_2784388, baseEnd_2784388] using wordTrace_append hprefix tailTrace_2784388
  have hstable : (prefixWord ++ tailWord_2784388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784388).length < 2 ^ (prefixWord ++ tailWord_2784388).sum := by decide
  have hdescent : baseEnd_2784388 < baseStart_2784388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784418 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_2784418 : Nat := 118140960795 + 2784418 * 2 ^ 59
def prefixEnd_2784418 : Nat := 4983230072969 + 3 ^ 40 * 2784418 * 2
def baseEnd_2784418 : Nat := 476581592343597395156567

theorem tailTrace_2784418 : CollatzResearch.WordTrace tailWord_2784418 prefixEnd_2784418 476581592343597395156567 := by
  unfold tailWord_2784418
  simp only [CollatzResearch.WordTrace]
  refine ⟨25389016906634150394944477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67704045084357734386518605 25389016906634150394944477)
  ·
    refine ⟨9520881339987806398104179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25389016906634150394944477 9520881339987806398104179)
    ·
      refine ⟨14281322009981709597156269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9520881339987806398104179 14281322009981709597156269)
      ·
        refine ⟨5355495753743141098933601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14281322009981709597156269 5355495753743141098933601)
        ·
          refine ⟨4016621815307355824200201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5355495753743141098933601 4016621815307355824200201)
          ·
            refine ⟨3012466361480516868150151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4016621815307355824200201 3012466361480516868150151)
            ·
              refine ⟨4518699542220775302225227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012466361480516868150151 4518699542220775302225227)
              ·
                refine ⟨6778049313331162953337841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4518699542220775302225227 6778049313331162953337841)
                ·
                  refine ⟨5083536984998372215003381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6778049313331162953337841 5083536984998372215003381)
                  ·
                    refine ⟨476581592343597395156567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5083536984998372215003381 476581592343597395156567)
                    ·
                      rfl

theorem cell23_2784418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_2784418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784418 prefixEnd_2784418 := by exact prefixLift 2784418
  have htrace : WordTrace (prefixWord ++ tailWord_2784418) baseStart_2784418 baseEnd_2784418 := by
    simpa [prefixWord, tailWord_2784418, baseEnd_2784418] using wordTrace_append hprefix tailTrace_2784418
  have hstable : (prefixWord ++ tailWord_2784418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784418).length < 2 ^ (prefixWord ++ tailWord_2784418).sum := by decide
  have hdescent : baseEnd_2784418 < baseStart_2784418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784421 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 2, 1, 4]
def baseStart_2784421 : Nat := 118140960795 + 2784421 * 2 ^ 59
def prefixEnd_2784421 : Nat := 4983230072969 + 3 ^ 40 * 2784421 * 2
def baseEnd_2784421 : Nat := 1429746317472755673732187

theorem tailTrace_2784421 : CollatzResearch.WordTrace tailWord_2784421 prefixEnd_2784421 1429746317472755673732187 := by
  unfold tailWord_2784421
  simp only [CollatzResearch.WordTrace]
  refine ⟨101556177045525733092137117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67704118030350488728091411 101556177045525733092137117)
  ·
    refine ⟨38083566392072149909551419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101556177045525733092137117 38083566392072149909551419)
    ·
      refine ⟨57125349588108224864327129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38083566392072149909551419 57125349588108224864327129)
      ·
        refine ⟨42844012191081168648245347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57125349588108224864327129 42844012191081168648245347)
        ·
          refine ⟨64266018286621752972368021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42844012191081168648245347 64266018286621752972368021)
          ·
            refine ⟨3012469607185394670579751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 64266018286621752972368021 3012469607185394670579751)
            ·
              refine ⟨4518704410778092005869627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012469607185394670579751 4518704410778092005869627)
              ·
                refine ⟨6778056616167138008804441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4518704410778092005869627 6778056616167138008804441)
                ·
                  refine ⟨5083542462125353506603331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6778056616167138008804441 5083542462125353506603331)
                  ·
                    refine ⟨7625313693188030259904997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5083542462125353506603331 7625313693188030259904997)
                    ·
                      refine ⟨1429746317472755673732187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7625313693188030259904997 1429746317472755673732187)
                      ·
                        rfl

theorem cell23_2784421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_2784421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784421 prefixEnd_2784421 := by exact prefixLift 2784421
  have htrace : WordTrace (prefixWord ++ tailWord_2784421) baseStart_2784421 baseEnd_2784421 := by
    simpa [prefixWord, tailWord_2784421, baseEnd_2784421] using wordTrace_append hprefix tailTrace_2784421
  have hstable : (prefixWord ++ tailWord_2784421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784421).length < 2 ^ (prefixWord ++ tailWord_2784421).sum := by decide
  have hdescent : baseEnd_2784421 < baseStart_2784421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784431 : List Nat := [1, 1, 2, 1, 2, 3, 3, 5, 1, 4]
def baseStart_2784431 : Nat := 118140960795 + 2784431 * 2 ^ 59
def prefixEnd_2784431 : Nat := 4983230072969 + 3 ^ 40 * 2784431 * 2
def baseEnd_2784431 : Nat := 476583817426433544869047

theorem tailTrace_2784431 : CollatzResearch.WordTrace tailWord_2784431 prefixEnd_2784431 476583817426433544869047 := by
  unfold tailWord_2784431
  simp only [CollatzResearch.WordTrace]
  refine ⟨101556541775489504800001147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67704361183659669866667431 101556541775489504800001147)
  ·
    refine ⟨152334812663234257200001721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101556541775489504800001147 152334812663234257200001721)
    ·
      refine ⟨114251109497425692900001291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152334812663234257200001721 114251109497425692900001291)
      ·
        refine ⟨171376664246138539350001937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114251109497425692900001291 171376664246138539350001937)
        ·
          refine ⟨128532498184603904512501453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171376664246138539350001937 128532498184603904512501453)
          ·
            refine ⟨48199686819226464192188045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128532498184603904512501453 48199686819226464192188045)
            ·
              refine ⟨18074882557209924072070517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48199686819226464192188045 18074882557209924072070517)
              ·
                refine ⟨1694520239738430381756611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18074882557209924072070517 1694520239738430381756611)
                ·
                  refine ⟨2541780359607645572634917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694520239738430381756611 2541780359607645572634917)
                  ·
                    refine ⟨476583817426433544869047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2541780359607645572634917 476583817426433544869047)
                    ·
                      rfl

theorem cell23_2784431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 1, 4].length) (baseStart_2784431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784431 prefixEnd_2784431 := by exact prefixLift 2784431
  have htrace : WordTrace (prefixWord ++ tailWord_2784431) baseStart_2784431 baseEnd_2784431 := by
    simpa [prefixWord, tailWord_2784431, baseEnd_2784431] using wordTrace_append hprefix tailTrace_2784431
  have hstable : (prefixWord ++ tailWord_2784431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784431).length < 2 ^ (prefixWord ++ tailWord_2784431).sum := by decide
  have hdescent : baseEnd_2784431 < baseStart_2784431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784444 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 8]
def baseStart_2784444 : Nat := 118140960795 + 2784444 * 2 ^ 59
def prefixEnd_2784444 : Nat := 4983230072969 + 3 ^ 40 * 2784444 * 2
def baseEnd_2784444 : Nat := 158862014169756564860509

theorem tailTrace_2784444 : CollatzResearch.WordTrace tailWord_2784444 prefixEnd_2784444 158862014169756564860509 := by
  unfold tailWord_2784444
  simp only [CollatzResearch.WordTrace]
  refine ⟨50778507962221204010112193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67704677282961605346816257 50778507962221204010112193)
  ·
    refine ⟨38083880971665903007584145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50778507962221204010112193 38083880971665903007584145)
    ·
      refine ⟨28562910728749427255688109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38083880971665903007584145 28562910728749427255688109)
      ·
        refine ⟨10711091523281035220883041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28562910728749427255688109 10711091523281035220883041)
        ·
          refine ⟨8033318642460776415662281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10711091523281035220883041 8033318642460776415662281)
          ·
            refine ⟨6024988981845582311746711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8033318642460776415662281 6024988981845582311746711)
            ·
              refine ⟨9037483472768373467620067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6024988981845582311746711 9037483472768373467620067)
              ·
                refine ⟨13556225209152560201430101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9037483472768373467620067 13556225209152560201430101)
                ·
                  refine ⟨158862014169756564860509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13556225209152560201430101 158862014169756564860509)
                  ·
                    rfl

theorem cell23_2784444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 8].length) (baseStart_2784444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784444 prefixEnd_2784444 := by exact prefixLift 2784444
  have htrace : WordTrace (prefixWord ++ tailWord_2784444) baseStart_2784444 baseEnd_2784444 := by
    simpa [prefixWord, tailWord_2784444, baseEnd_2784444] using wordTrace_append hprefix tailTrace_2784444
  have hstable : (prefixWord ++ tailWord_2784444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784444).length < 2 ^ (prefixWord ++ tailWord_2784444).sum := by decide
  have hdescent : baseEnd_2784444 < baseStart_2784444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784447 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 6]
def baseStart_2784447 : Nat := 118140960795 + 2784447 * 2 ^ 59
def prefixEnd_2784447 : Nat := 4983230072969 + 3 ^ 40 * 2784447 * 2
def baseEnd_2784447 : Nat := 1429759667969772572007067

theorem tailTrace_2784447 : CollatzResearch.WordTrace tailWord_2784447 prefixEnd_2784447 1429759667969772572007067 := by
  unfold tailWord_2784447
  simp only [CollatzResearch.WordTrace]
  refine ⟨101557125343431539532583595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67704750228954359688389063 101557125343431539532583595)
  ·
    refine ⟨152335688015147309298875393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101557125343431539532583595 152335688015147309298875393)
    ·
      refine ⟨114251766011360481974156545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152335688015147309298875393 114251766011360481974156545)
      ·
        refine ⟨85688824508520361480617409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114251766011360481974156545 85688824508520361480617409)
        ·
          refine ⟨64266618381390271110463057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85688824508520361480617409 64266618381390271110463057)
          ·
            refine ⟨48199963786042703332847293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64266618381390271110463057 48199963786042703332847293)
            ·
              refine ⟨18074986419766013749817735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48199963786042703332847293 18074986419766013749817735)
              ·
                refine ⟨27112479629649020624726603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18074986419766013749817735 27112479629649020624726603)
                ·
                  refine ⟨40668719444473530937089905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27112479629649020624726603 40668719444473530937089905)
                  ·
                    refine ⟨30501539583355148202817429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40668719444473530937089905 30501539583355148202817429)
                    ·
                      refine ⟨1429759667969772572007067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30501539583355148202817429 1429759667969772572007067)
                      ·
                        rfl

theorem cell23_2784447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_2784447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784447 prefixEnd_2784447 := by exact prefixLift 2784447
  have htrace : WordTrace (prefixWord ++ tailWord_2784447) baseStart_2784447 baseEnd_2784447 := by
    simpa [prefixWord, tailWord_2784447, baseEnd_2784447] using wordTrace_append hprefix tailTrace_2784447
  have hstable : (prefixWord ++ tailWord_2784447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784447).length < 2 ^ (prefixWord ++ tailWord_2784447).sum := by decide
  have hdescent : baseEnd_2784447 < baseStart_2784447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784471 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 3, 1, 3]
def baseStart_2784471 : Nat := 118140960795 + 2784471 * 2 ^ 59
def prefixEnd_2784471 : Nat := 4983230072969 + 3 ^ 40 * 2784471 * 2
def baseEnd_2784471 : Nat := 1429771991505480478106957

theorem tailTrace_2784471 : CollatzResearch.WordTrace tailWord_2784471 prefixEnd_2784471 1429771991505480478106957 := by
  unfold tailWord_2784471
  simp only [CollatzResearch.WordTrace]
  refine ⟨101558000695344591631457267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67705333796896394420971511 101558000695344591631457267)
  ·
    refine ⟨152337001043016887447185901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101558000695344591631457267 152337001043016887447185901)
    ·
      refine ⟨57126375391131332792694713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152337001043016887447185901 57126375391131332792694713)
      ·
        refine ⟨42844781543348499594521035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57126375391131332792694713 42844781543348499594521035)
        ·
          refine ⟨64267172315022749391781553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42844781543348499594521035 64267172315022749391781553)
          ·
            refine ⟨48200379236267062043836165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64267172315022749391781553 48200379236267062043836165)
            ·
              refine ⟨9037571106800074133219281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48200379236267062043836165 9037571106800074133219281)
              ·
                refine ⟨6778178330100055599914461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9037571106800074133219281 6778178330100055599914461)
                ·
                  refine ⟨2541816873787520849967923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6778178330100055599914461 2541816873787520849967923)
                  ·
                    refine ⟨3812725310681281274951885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2541816873787520849967923 3812725310681281274951885)
                    ·
                      refine ⟨1429771991505480478106957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3812725310681281274951885 1429771991505480478106957)
                      ·
                        rfl

theorem cell23_2784471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_2784471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784471 prefixEnd_2784471 := by exact prefixLift 2784471
  have htrace : WordTrace (prefixWord ++ tailWord_2784471) baseStart_2784471 baseEnd_2784471 := by
    simpa [prefixWord, tailWord_2784471, baseEnd_2784471] using wordTrace_append hprefix tailTrace_2784471
  have hstable : (prefixWord ++ tailWord_2784471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784471).length < 2 ^ (prefixWord ++ tailWord_2784471).sum := by decide
  have hdescent : baseEnd_2784471 < baseStart_2784471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784481 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 1, 5, 2]
def baseStart_2784481 : Nat := 118140960795 + 2784481 * 2 ^ 59
def prefixEnd_2784481 : Nat := 4983230072969 + 3 ^ 40 * 2784481 * 2
def baseEnd_2784481 : Nat := 1429777126312025438981911

theorem tailTrace_2784481 : CollatzResearch.WordTrace tailWord_2784481 prefixEnd_2784481 1429777126312025438981911 := by
  unfold tailWord_2784481
  simp only [CollatzResearch.WordTrace]
  refine ⟨101558365425308363339321297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67705576950205575559547531 101558365425308363339321297)
  ·
    refine ⟨76168774068981272504490973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101558365425308363339321297 76168774068981272504490973)
    ·
      refine ⟨28563290275867977189184115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76168774068981272504490973 28563290275867977189184115)
      ·
        refine ⟨42844935413801965783776173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28563290275867977189184115 42844935413801965783776173)
        ·
          refine ⟨16066850780175737168916065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42844935413801965783776173 16066850780175737168916065)
          ·
            refine ⟨12050138085131802876687049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16066850780175737168916065 12050138085131802876687049)
            ·
              refine ⟨9037603563848852157515287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12050138085131802876687049 9037603563848852157515287)
              ·
                refine ⟨13556405345773278236272931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9037603563848852157515287 13556405345773278236272931)
                ·
                  refine ⟨20334608018659917354409397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13556405345773278236272931 20334608018659917354409397)
                  ·
                    refine ⟨1906369501749367251975881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20334608018659917354409397 1906369501749367251975881)
                    ·
                      refine ⟨1429777126312025438981911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906369501749367251975881 1429777126312025438981911)
                      ·
                        rfl

theorem cell23_2784481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_2784481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784481 prefixEnd_2784481 := by exact prefixLift 2784481
  have htrace : WordTrace (prefixWord ++ tailWord_2784481) baseStart_2784481 baseEnd_2784481 := by
    simpa [prefixWord, tailWord_2784481, baseEnd_2784481] using wordTrace_append hprefix tailTrace_2784481
  have hstable : (prefixWord ++ tailWord_2784481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784481).length < 2 ^ (prefixWord ++ tailWord_2784481).sum := by decide
  have hdescent : baseEnd_2784481 < baseStart_2784481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784505 : List Nat := [1, 2, 1, 3, 1, 1, 7, 2, 1, 1, 3]
def baseStart_2784505 : Nat := 118140960795 + 2784505 * 2 ^ 59
def prefixEnd_2784505 : Nat := 4983230072969 + 3 ^ 40 * 2784505 * 2
def baseEnd_2784505 : Nat := 1429789449847733345081801

theorem tailTrace_2784505 : CollatzResearch.WordTrace tailWord_2784505 prefixEnd_2784505 1429789449847733345081801 := by
  unfold tailWord_2784505
  simp only [CollatzResearch.WordTrace]
  refine ⟨101559240777221415438194969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67706160518147610292129979 101559240777221415438194969)
  ·
    refine ⟨76169430582916061578646227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101559240777221415438194969 76169430582916061578646227)
    ·
      refine ⟨114254145874374092367969341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76169430582916061578646227 114254145874374092367969341)
      ·
        refine ⟨42845304702890284637988503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114254145874374092367969341 42845304702890284637988503)
        ·
          refine ⟨64267957054335426956982755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42845304702890284637988503 64267957054335426956982755)
          ·
            refine ⟨96401935581503140435474133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64267957054335426956982755 96401935581503140435474133)
            ·
              refine ⟨2259420365191479853956425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 96401935581503140435474133 2259420365191479853956425)
              ·
                refine ⟨1694565273893609890467319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2259420365191479853956425 1694565273893609890467319)
                ·
                  refine ⟨2541847910840414835700979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694565273893609890467319 2541847910840414835700979)
                  ·
                    refine ⟨3812771866260622253551469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2541847910840414835700979 3812771866260622253551469)
                    ·
                      refine ⟨1429789449847733345081801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3812771866260622253551469 1429789449847733345081801)
                      ·
                        rfl

theorem cell23_2784505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_2784505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784505 prefixEnd_2784505 := by exact prefixLift 2784505
  have htrace : WordTrace (prefixWord ++ tailWord_2784505) baseStart_2784505 baseEnd_2784505 := by
    simpa [prefixWord, tailWord_2784505, baseEnd_2784505] using wordTrace_append hprefix tailTrace_2784505
  have hstable : (prefixWord ++ tailWord_2784505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784505).length < 2 ^ (prefixWord ++ tailWord_2784505).sum := by decide
  have hdescent : baseEnd_2784505 < baseStart_2784505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784521 : List Nat := [1, 2, 1, 1, 3, 3, 3, 3, 2, 4]
def baseStart_2784521 : Nat := 118140960795 + 2784521 * 2 ^ 59
def prefixEnd_2784521 : Nat := 4983230072969 + 3 ^ 40 * 2784521 * 2
def baseEnd_2784521 : Nat := 476599221846068427493909

theorem tailTrace_2784521 : CollatzResearch.WordTrace tailWord_2784521 prefixEnd_2784521 476599221846068427493909 := by
  unfold tailWord_2784521
  simp only [CollatzResearch.WordTrace]
  refine ⟨101559824345163450170777417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67706549563442300113851611 101559824345163450170777417)
  ·
    refine ⟨76169868258872587628083063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101559824345163450170777417 76169868258872587628083063)
    ·
      refine ⟨114254802388308881442124595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76169868258872587628083063 114254802388308881442124595)
      ·
        refine ⟨171382203582463322163186893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114254802388308881442124595 171382203582463322163186893)
        ·
          refine ⟨64268326343423745811195085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171382203582463322163186893 64268326343423745811195085)
          ·
            refine ⟨24100622378783904679198157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64268326343423745811195085 24100622378783904679198157)
            ·
              refine ⟨9037733392043964254699309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24100622378783904679198157 9037733392043964254699309)
              ·
                refine ⟨3389150022016486595512241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9037733392043964254699309 3389150022016486595512241)
                ·
                  refine ⟨2541862516512364946634181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3389150022016486595512241 2541862516512364946634181)
                  ·
                    refine ⟨476599221846068427493909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2541862516512364946634181 476599221846068427493909)
                    ·
                      rfl

theorem cell23_2784521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 4].length) (baseStart_2784521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784521 prefixEnd_2784521 := by exact prefixLift 2784521
  have htrace : WordTrace (prefixWord ++ tailWord_2784521) baseStart_2784521 baseEnd_2784521 := by
    simpa [prefixWord, tailWord_2784521, baseEnd_2784521] using wordTrace_append hprefix tailTrace_2784521
  have hstable : (prefixWord ++ tailWord_2784521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784521).length < 2 ^ (prefixWord ++ tailWord_2784521).sum := by decide
  have hdescent : baseEnd_2784521 < baseStart_2784521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784524 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 1, 1, 6]
def baseStart_2784524 : Nat := 118140960795 + 2784524 * 2 ^ 59
def prefixEnd_2784524 : Nat := 4983230072969 + 3 ^ 40 * 2784524 * 2
def baseEnd_2784524 : Nat := 1429799205980168770744213

theorem tailTrace_2784524 : CollatzResearch.WordTrace tailWord_2784524 prefixEnd_2784524 1429799205980168770744213 := by
  unfold tailWord_2784524
  simp only [CollatzResearch.WordTrace]
  refine ⟨50779966882076290841568313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67706622509435054455424417 50779966882076290841568313)
  ·
    refine ⟨38084975161557218131176235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50779966882076290841568313 38084975161557218131176235)
    ·
      refine ⟨57127462742335827196764353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38084975161557218131176235 57127462742335827196764353)
      ·
        refine ⟨42845597056751870397573265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57127462742335827196764353 42845597056751870397573265)
        ·
          refine ⟨32134197792563902798179949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42845597056751870397573265 32134197792563902798179949)
          ·
            refine ⟨12050324172211463549317481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32134197792563902798179949 12050324172211463549317481)
            ·
              refine ⟨9037743129158597661988111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12050324172211463549317481 9037743129158597661988111)
              ·
                refine ⟨13556614693737896492982167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9037743129158597661988111 13556614693737896492982167)
                ·
                  refine ⟨20334922040606844739473251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13556614693737896492982167 20334922040606844739473251)
                  ·
                    refine ⟨30502383060910267109209877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20334922040606844739473251 30502383060910267109209877)
                    ·
                      refine ⟨1429799205980168770744213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30502383060910267109209877 1429799205980168770744213)
                      ·
                        rfl

theorem cell23_2784524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_2784524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784524 prefixEnd_2784524 := by exact prefixLift 2784524
  have htrace : WordTrace (prefixWord ++ tailWord_2784524) baseStart_2784524 baseEnd_2784524 := by
    simpa [prefixWord, tailWord_2784524, baseEnd_2784524] using wordTrace_append hprefix tailTrace_2784524
  have hstable : (prefixWord ++ tailWord_2784524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784524).length < 2 ^ (prefixWord ++ tailWord_2784524).sum := by decide
  have hdescent : baseEnd_2784524 < baseStart_2784524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784541 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2784541 : Nat := 118140960795 + 2784541 * 2 ^ 59
def prefixEnd_2784541 : Nat := 4983230072969 + 3 ^ 40 * 2784541 * 2
def baseEnd_2784541 : Nat := 1429807935151295204231635

theorem tailTrace_2784541 : CollatzResearch.WordTrace tailWord_2784541 prefixEnd_2784541 1429807935151295204231635 := by
  unfold tailWord_2784541
  simp only [CollatzResearch.WordTrace]
  refine ⟨101560553805090993586505477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67707035870060662391003651 101560553805090993586505477)
  ·
    refine ⟨19042603838454561297469777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101560553805090993586505477 19042603838454561297469777)
    ·
      refine ⟨14281952878840920973102333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19042603838454561297469777 14281952878840920973102333)
      ·
        refine ⟨5355732329565345364913375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14281952878840920973102333 5355732329565345364913375)
        ·
          refine ⟨8033598494348018047370063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5355732329565345364913375 8033598494348018047370063)
          ·
            refine ⟨12050397741522027071055095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8033598494348018047370063 12050397741522027071055095)
            ·
              refine ⟨18075596612283040606582643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12050397741522027071055095 18075596612283040606582643)
              ·
                refine ⟨27113394918424560909873965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18075596612283040606582643 27113394918424560909873965)
                ·
                  refine ⟨10167523094409210341202737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27113394918424560909873965 10167523094409210341202737)
                  ·
                    refine ⟨7625642320806907755902053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10167523094409210341202737 7625642320806907755902053)
                    ·
                      refine ⟨1429807935151295204231635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7625642320806907755902053 1429807935151295204231635)
                      ·
                        rfl

theorem cell23_2784541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2784541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784541 prefixEnd_2784541 := by exact prefixLift 2784541
  have htrace : WordTrace (prefixWord ++ tailWord_2784541) baseStart_2784541 baseEnd_2784541 := by
    simpa [prefixWord, tailWord_2784541, baseEnd_2784541] using wordTrace_append hprefix tailTrace_2784541
  have hstable : (prefixWord ++ tailWord_2784541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784541).length < 2 ^ (prefixWord ++ tailWord_2784541).sum := by decide
  have hdescent : baseEnd_2784541 < baseStart_2784541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784542 : List Nat := [4, 3, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_2784542 : Nat := 118140960795 + 2784542 * 2 ^ 59
def prefixEnd_2784542 : Nat := 4983230072969 + 3 ^ 40 * 2784542 * 2
def baseEnd_2784542 : Nat := 476602816210649900106377

theorem tailTrace_2784542 : CollatzResearch.WordTrace tailWord_2784542 prefixEnd_2784542 476602816210649900106377 := by
  unfold tailWord_2784542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12695073784760921344661485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67707060185391580504861253 12695073784760921344661485)
  ·
    refine ⟨4760652669285345504248057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12695073784760921344661485 4760652669285345504248057)
    ·
      refine ⟨3570489501964009128186043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4760652669285345504248057 3570489501964009128186043)
      ·
        refine ⟨5355734252946013692279065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3570489501964009128186043 5355734252946013692279065)
        ·
          refine ⟨4016800689709510269209299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5355734252946013692279065 4016800689709510269209299)
          ·
            refine ⟨6025201034564265403813949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4016800689709510269209299 6025201034564265403813949)
            ·
              refine ⟨2259450387961599526430231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6025201034564265403813949 2259450387961599526430231)
              ·
                refine ⟨3389175581942399289645347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2259450387961599526430231 3389175581942399289645347)
                ·
                  refine ⟨5083763372913598934468021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3389175581942399289645347 5083763372913598934468021)
                  ·
                    refine ⟨476602816210649900106377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5083763372913598934468021 476602816210649900106377)
                    ·
                      rfl

theorem cell23_2784542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_2784542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784542 prefixEnd_2784542 := by exact prefixLift 2784542
  have htrace : WordTrace (prefixWord ++ tailWord_2784542) baseStart_2784542 baseEnd_2784542 := by
    simpa [prefixWord, tailWord_2784542, baseEnd_2784542] using wordTrace_append hprefix tailTrace_2784542
  have hstable : (prefixWord ++ tailWord_2784542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784542).length < 2 ^ (prefixWord ++ tailWord_2784542).sum := by decide
  have hdescent : baseEnd_2784542 < baseStart_2784542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784545 : List Nat := [1, 2, 3, 2, 1, 1, 1, 7, 1, 2, 2]
def baseStart_2784545 : Nat := 118140960795 + 2784545 * 2 ^ 59
def prefixEnd_2784545 : Nat := 4983230072969 + 3 ^ 40 * 2784545 * 2
def baseEnd_2784545 : Nat := 1429809989073913188581617

theorem tailTrace_2784545 : CollatzResearch.WordTrace tailWord_2784545 prefixEnd_2784545 1429809989073913188581617 := by
  unfold tailWord_2784545
  simp only [CollatzResearch.WordTrace]
  refine ⟨101560699697076502269651089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67707133131384334846434059 101560699697076502269651089)
  ·
    refine ⟨76170524772807376702238317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101560699697076502269651089 76170524772807376702238317)
    ·
      refine ⟨28563946789802766263339369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76170524772807376702238317 28563946789802766263339369)
      ·
        refine ⟨21422960092352074697504527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28563946789802766263339369 21422960092352074697504527)
        ·
          refine ⟨32134440138528112046256791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21422960092352074697504527 32134440138528112046256791)
          ·
            refine ⟨48201660207792168069385187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32134440138528112046256791 48201660207792168069385187)
            ·
              refine ⟨72302490311688252104077781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48201660207792168069385187 72302490311688252104077781)
              ·
                refine ⟨1694589616680193408689323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 72302490311688252104077781 1694589616680193408689323)
                ·
                  refine ⟨2541884425020290113033985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694589616680193408689323 2541884425020290113033985)
                  ·
                    refine ⟨1906413318765217584775489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2541884425020290113033985 1906413318765217584775489)
                    ·
                      refine ⟨1429809989073913188581617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906413318765217584775489 1429809989073913188581617)
                      ·
                        rfl

theorem cell23_2784545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_2784545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784545 prefixEnd_2784545 := by exact prefixLift 2784545
  have htrace : WordTrace (prefixWord ++ tailWord_2784545) baseStart_2784545 baseEnd_2784545 := by
    simpa [prefixWord, tailWord_2784545, baseEnd_2784545] using wordTrace_append hprefix tailTrace_2784545
  have hstable : (prefixWord ++ tailWord_2784545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784545).length < 2 ^ (prefixWord ++ tailWord_2784545).sum := by decide
  have hdescent : baseEnd_2784545 < baseStart_2784545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784562 : List Nat := [3, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2]
def baseStart_2784562 : Nat := 118140960795 + 2784562 * 2 ^ 59
def prefixEnd_2784562 : Nat := 4983230072969 + 3 ^ 40 * 2784562 * 2
def baseEnd_2784562 : Nat := 1429818718245039622069039

theorem tailTrace_2784562 : CollatzResearch.WordTrace tailWord_2784562 prefixEnd_2784562 1429818718245039622069039 := by
  unfold tailWord_2784562
  simp only [CollatzResearch.WordTrace]
  refine ⟨25390329934503728543254985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67707546492009942782013293 25390329934503728543254985)
  ·
    refine ⟨19042747450877796407441239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25390329934503728543254985 19042747450877796407441239)
    ·
      refine ⟨28564121176316694611161859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19042747450877796407441239 28564121176316694611161859)
      ·
        refine ⟨42846181764475041916742789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28564121176316694611161859 42846181764475041916742789)
        ·
          refine ⟨8033659080839070359389273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42846181764475041916742789 8033659080839070359389273)
          ·
            refine ⟨6025244310629302769541955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8033659080839070359389273 6025244310629302769541955)
            ·
              refine ⟨9037866465943954154312933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6025244310629302769541955 9037866465943954154312933)
              ·
                refine ⟨1694599962364491403933675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9037866465943954154312933 1694599962364491403933675)
                ·
                  refine ⟨2541899943546737105900513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694599962364491403933675 2541899943546737105900513)
                  ·
                    refine ⟨1906424957660052829425385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2541899943546737105900513 1906424957660052829425385)
                    ·
                      refine ⟨1429818718245039622069039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906424957660052829425385 1429818718245039622069039)
                      ·
                        rfl

theorem cell23_2784562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_2784562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784562 prefixEnd_2784562 := by exact prefixLift 2784562
  have htrace : WordTrace (prefixWord ++ tailWord_2784562) baseStart_2784562 baseEnd_2784562 := by
    simpa [prefixWord, tailWord_2784562, baseEnd_2784562] using wordTrace_append hprefix tailTrace_2784562
  have hstable : (prefixWord ++ tailWord_2784562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784562).length < 2 ^ (prefixWord ++ tailWord_2784562).sum := by decide
  have hdescent : baseEnd_2784562 < baseStart_2784562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784584 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_2784584 : Nat := 118140960795 + 2784584 * 2 ^ 59
def prefixEnd_2784584 : Nat := 4983230072969 + 3 ^ 40 * 2784584 * 2
def baseEnd_2784584 : Nat := 1429830014819438535993937

theorem tailTrace_2784584 : CollatzResearch.WordTrace tailWord_2784584 prefixEnd_2784584 1429830014819438535993937 := by
  unfold tailWord_2784584
  simp only [CollatzResearch.WordTrace]
  refine ⟨50781061071967605965160403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67708081429290141286880537 50781061071967605965160403)
  ·
    refine ⟨76171591607951408947740605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50781061071967605965160403 76171591607951408947740605)
    ·
      refine ⟨28564346852981778355402727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76171591607951408947740605 28564346852981778355402727)
      ·
        refine ⟨42846520279472667533104091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28564346852981778355402727 42846520279472667533104091)
        ·
          refine ⟨64269780419209001299656137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42846520279472667533104091 64269780419209001299656137)
          ·
            refine ⟨48202335314406750974742103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64269780419209001299656137 48202335314406750974742103)
            ·
              refine ⟨72303502971610126462113155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48202335314406750974742103 72303502971610126462113155)
              ·
                refine ⟨108455254457415189693169733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72303502971610126462113155 108455254457415189693169733)
                ·
                  refine ⟨20335360210765348067469325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108455254457415189693169733 20335360210765348067469325)
                  ·
                    refine ⟨7625760079037005525300997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20335360210765348067469325 7625760079037005525300997)
                    ·
                      refine ⟨1429830014819438535993937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7625760079037005525300997 1429830014819438535993937)
                      ·
                        rfl

theorem cell23_2784584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_2784584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784584 prefixEnd_2784584 := by exact prefixLift 2784584
  have htrace : WordTrace (prefixWord ++ tailWord_2784584) baseStart_2784584 baseEnd_2784584 := by
    simpa [prefixWord, tailWord_2784584, baseEnd_2784584] using wordTrace_append hprefix tailTrace_2784584
  have hstable : (prefixWord ++ tailWord_2784584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784584).length < 2 ^ (prefixWord ++ tailWord_2784584).sum := by decide
  have hdescent : baseEnd_2784584 < baseStart_2784584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784588 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 3, 3, 2]
def baseStart_2784588 : Nat := 118140960795 + 2784588 * 2 ^ 59
def prefixEnd_2784588 : Nat := 4983230072969 + 3 ^ 40 * 2784588 * 2
def baseEnd_2784588 : Nat := 1429832068742056520343919

theorem tailTrace_2784588 : CollatzResearch.WordTrace tailWord_2784588 prefixEnd_2784588 1429832068742056520343919 := by
  unfold tailWord_2784588
  simp only [CollatzResearch.WordTrace]
  refine ⟨50781134017960360306733209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67708178690613813742310945 50781134017960360306733209)
  ·
    refine ⟨38085850513470270230049907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50781134017960360306733209 38085850513470270230049907)
    ·
      refine ⟨57128775770205405345074861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38085850513470270230049907 57128775770205405345074861)
      ·
        refine ⟨21423290913827027004403073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57128775770205405345074861 21423290913827027004403073)
        ·
          refine ⟨16067468185370270253302305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21423290913827027004403073 16067468185370270253302305)
          ·
            refine ⟨12050601139027702689976729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16067468185370270253302305 12050601139027702689976729)
            ·
              refine ⟨9037950854270777017482547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12050601139027702689976729 9037950854270777017482547)
              ·
                refine ⟨13556926281406165526223821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9037950854270777017482547 13556926281406165526223821)
                ·
                  refine ⟨5083847355527312072333933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13556926281406165526223821 5083847355527312072333933)
                  ·
                    refine ⟨1906442758322742027125225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5083847355527312072333933 1906442758322742027125225)
                    ·
                      refine ⟨1429832068742056520343919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906442758322742027125225 1429832068742056520343919)
                      ·
                        rfl

theorem cell23_2784588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_2784588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784588 prefixEnd_2784588 := by exact prefixLift 2784588
  have htrace : WordTrace (prefixWord ++ tailWord_2784588) baseStart_2784588 baseEnd_2784588 := by
    simpa [prefixWord, tailWord_2784588, baseEnd_2784588] using wordTrace_append hprefix tailTrace_2784588
  have hstable : (prefixWord ++ tailWord_2784588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784588).length < 2 ^ (prefixWord ++ tailWord_2784588).sum := by decide
  have hdescent : baseEnd_2784588 < baseStart_2784588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784594 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 3, 8]
def baseStart_2784594 : Nat := 118140960795 + 2784594 * 2 ^ 59
def prefixEnd_2784594 : Nat := 4983230072969 + 3 ^ 40 * 2784594 * 2
def baseEnd_2784594 : Nat := 476611716541994498956297

theorem tailTrace_2784594 : CollatzResearch.WordTrace tailWord_2784594 prefixEnd_2784594 476611716541994498956297 := by
  unfold tailWord_2784594
  simp only [CollatzResearch.WordTrace]
  refine ⟨25390621718474745909546209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67708324582599322425456557 25390621718474745909546209)
  ·
    refine ⟨19042966288856059432159657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25390621718474745909546209 19042966288856059432159657)
    ·
      refine ⟨14282224716642044574119743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19042966288856059432159657 14282224716642044574119743)
      ·
        refine ⟨21423337074963066861179615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14282224716642044574119743 21423337074963066861179615)
        ·
          refine ⟨32135005612444600291769423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21423337074963066861179615 32135005612444600291769423)
          ·
            refine ⟨48202508418666900437654135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32135005612444600291769423 48202508418666900437654135)
            ·
              refine ⟨72303762628000350656481203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48202508418666900437654135 72303762628000350656481203)
              ·
                refine ⟨108455643942000525984721805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72303762628000350656481203 108455643942000525984721805)
                ·
                  refine ⟨40670866478250197244270677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108455643942000525984721805 40670866478250197244270677)
                  ·
                    refine ⟨476611716541994498956297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40670866478250197244270677 476611716541994498956297)
                    ·
                      rfl

theorem cell23_2784594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_2784594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784594 prefixEnd_2784594 := by exact prefixLift 2784594
  have htrace : WordTrace (prefixWord ++ tailWord_2784594) baseStart_2784594 baseEnd_2784594 := by
    simpa [prefixWord, tailWord_2784594, baseEnd_2784594] using wordTrace_append hprefix tailTrace_2784594
  have hstable : (prefixWord ++ tailWord_2784594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784594).length < 2 ^ (prefixWord ++ tailWord_2784594).sum := by decide
  have hdescent : baseEnd_2784594 < baseStart_2784594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784671 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 4, 5]
def baseStart_2784671 : Nat := 118140960795 + 2784671 * 2 ^ 59
def prefixEnd_2784671 : Nat := 4983230072969 + 3 ^ 40 * 2784671 * 2
def baseEnd_2784671 : Nat := 476624895878793231868679

theorem tailTrace_2784671 : CollatzResearch.WordTrace tailWord_2784671 prefixEnd_2784671 476624895878793231868679 := by
  unfold tailWord_2784671
  simp only [CollatzResearch.WordTrace]
  refine ⟨101565295294620025788737867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67710196863080017192491911 101565295294620025788737867)
  ·
    refine ⟨152347942941930038683106801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101565295294620025788737867 152347942941930038683106801)
    ·
      refine ⟨114260957206447529012330101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152347942941930038683106801 114260957206447529012330101)
      ·
        refine ⟨10711964738104455844905947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114260957206447529012330101 10711964738104455844905947)
        ·
          refine ⟨16067947107156683767358921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10711964738104455844905947 16067947107156683767358921)
          ·
            refine ⟨12050960330367512825519191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16067947107156683767358921 12050960330367512825519191)
            ·
              refine ⟨18076440495551269238278787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12050960330367512825519191 18076440495551269238278787)
              ·
                refine ⟨27114660743326903857418181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18076440495551269238278787 27114660743326903857418181)
                ·
                  refine ⟨5083998889373794473265909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27114660743326903857418181 5083998889373794473265909)
                  ·
                    refine ⟨476624895878793231868679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5083998889373794473265909 476624895878793231868679)
                    ·
                      rfl

theorem cell23_2784671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 5].length) (baseStart_2784671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784671 prefixEnd_2784671 := by exact prefixLift 2784671
  have htrace : WordTrace (prefixWord ++ tailWord_2784671) baseStart_2784671 baseEnd_2784671 := by
    simpa [prefixWord, tailWord_2784671, baseEnd_2784671] using wordTrace_append hprefix tailTrace_2784671
  have hstable : (prefixWord ++ tailWord_2784671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784671).length < 2 ^ (prefixWord ++ tailWord_2784671).sum := by decide
  have hdescent : baseEnd_2784671 < baseStart_2784671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784728 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 2, 2, 3]
def baseStart_2784728 : Nat := 118140960795 + 2784728 * 2 ^ 59
def prefixEnd_2784728 : Nat := 4983230072969 + 3 ^ 40 * 2784728 * 2
def baseEnd_2784728 : Nat := 1429903956033685972593275

theorem tailTrace_2784728 : CollatzResearch.WordTrace tailWord_2784728 prefixEnd_2784728 1429903956033685972593275 := by
  unfold tailWord_2784728
  simp only [CollatzResearch.WordTrace]
  refine ⟨50783687127706762261781419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67711582836942349682375225 50783687127706762261781419)
  ·
    refine ⟨76175530691560143392672129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50783687127706762261781419 76175530691560143392672129)
    ·
      refine ⟨57131648018670107544504097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76175530691560143392672129 57131648018670107544504097)
      ·
        refine ⟨42848736014002580658378073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57131648018670107544504097 42848736014002580658378073)
        ·
          refine ⟨32136552010501935493783555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42848736014002580658378073 32136552010501935493783555)
          ·
            refine ⟨48204828015752903240675333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32136552010501935493783555 48204828015752903240675333)
            ·
              refine ⟨9038405252953669357626625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48204828015752903240675333 9038405252953669357626625)
              ·
                refine ⟨6778803939715252018219969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9038405252953669357626625 6778803939715252018219969)
                ·
                  refine ⟨5084102954786439013664977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6778803939715252018219969 5084102954786439013664977)
                  ·
                    refine ⟨3813077216089829260248733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5084102954786439013664977 3813077216089829260248733)
                    ·
                      refine ⟨1429903956033685972593275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3813077216089829260248733 1429903956033685972593275)
                      ·
                        rfl

theorem cell23_2784728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_2784728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784728 prefixEnd_2784728 := by exact prefixLift 2784728
  have htrace : WordTrace (prefixWord ++ tailWord_2784728) baseStart_2784728 baseEnd_2784728 := by
    simpa [prefixWord, tailWord_2784728, baseEnd_2784728] using wordTrace_append hprefix tailTrace_2784728
  have hstable : (prefixWord ++ tailWord_2784728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784728).length < 2 ^ (prefixWord ++ tailWord_2784728).sum := by decide
  have hdescent : baseEnd_2784728 < baseStart_2784728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784735 : List Nat := [1, 1, 2, 3, 3, 1, 3, 4, 1, 4]
def baseStart_2784735 : Nat := 118140960795 + 2784735 * 2 ^ 59
def prefixEnd_2784735 : Nat := 4983230072969 + 3 ^ 40 * 2784735 * 2
def baseEnd_2784735 : Nat := 476635850132755815068581

theorem tailTrace_2784735 : CollatzResearch.WordTrace tailWord_2784735 prefixEnd_2784735 476635850132755815068581 := by
  unfold tailWord_2784735
  simp only [CollatzResearch.WordTrace]
  refine ⟨101567629566388164719067659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67711753044258776479378439 101567629566388164719067659)
  ·
    refine ⟨152351444349582247078601489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101567629566388164719067659 152351444349582247078601489)
    ·
      refine ⟨114263583262186685308951117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152351444349582247078601489 114263583262186685308951117)
      ·
        refine ⟨42848843723320006990856669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114263583262186685308951117 42848843723320006990856669)
        ·
          refine ⟨16068316396245002621571251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42848843723320006990856669 16068316396245002621571251)
          ·
            refine ⟨24102474594367503932356877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16068316396245002621571251 24102474594367503932356877)
            ·
              refine ⟨9038427972887813974633829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24102474594367503932356877 9038427972887813974633829)
              ·
                refine ⟨1694705244916465120243843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9038427972887813974633829 1694705244916465120243843)
                ·
                  refine ⟨2542057867374697680365765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694705244916465120243843 2542057867374697680365765)
                  ·
                    refine ⟨476635850132755815068581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2542057867374697680365765 476635850132755815068581)
                    ·
                      rfl

theorem cell23_2784735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 1, 4].length) (baseStart_2784735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784735 prefixEnd_2784735 := by exact prefixLift 2784735
  have htrace : WordTrace (prefixWord ++ tailWord_2784735) baseStart_2784735 baseEnd_2784735 := by
    simpa [prefixWord, tailWord_2784735, baseEnd_2784735] using wordTrace_append hprefix tailTrace_2784735
  have hstable : (prefixWord ++ tailWord_2784735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784735).length < 2 ^ (prefixWord ++ tailWord_2784735).sum := by decide
  have hdescent : baseEnd_2784735 < baseStart_2784735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784782 : List Nat := [4, 1, 1, 2, 5, 1, 1, 2, 6]
def baseStart_2784782 : Nat := 118140960795 + 2784782 * 2 ^ 59
def prefixEnd_2784782 : Nat := 4983230072969 + 3 ^ 40 * 2784782 * 2
def baseEnd_2784782 : Nat := 158881298221003195702003

theorem tailTrace_2784782 : CollatzResearch.WordTrace tailWord_2784782 prefixEnd_2784782 158881298221003195702003 := by
  unfold tailWord_2784782
  simp only [CollatzResearch.WordTrace]
  refine ⟨12696167974652236468253575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67712895864811927830685733 12696167974652236468253575)
  ·
    refine ⟨19044251961978354702380363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12696167974652236468253575 19044251961978354702380363)
    ·
      refine ⟨28566377942967532053570545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19044251961978354702380363 28566377942967532053570545)
      ·
        refine ⟨21424783457225649040177909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28566377942967532053570545 21424783457225649040177909)
        ·
          refine ⟨2008573449114904597516679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21424783457225649040177909 2008573449114904597516679)
          ·
            refine ⟨3012860173672356896275019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008573449114904597516679 3012860173672356896275019)
            ·
              refine ⟨4519290260508535344412529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012860173672356896275019 4519290260508535344412529)
              ·
                refine ⟨3389467695381401508309397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4519290260508535344412529 3389467695381401508309397)
                ·
                  refine ⟨158881298221003195702003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3389467695381401508309397 158881298221003195702003)
                  ·
                    rfl

theorem cell23_2784782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_2784782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784782 prefixEnd_2784782 := by exact prefixLift 2784782
  have htrace : WordTrace (prefixWord ++ tailWord_2784782) baseStart_2784782 baseEnd_2784782 := by
    simpa [prefixWord, tailWord_2784782, baseEnd_2784782] using wordTrace_append hprefix tailTrace_2784782
  have hstable : (prefixWord ++ tailWord_2784782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784782).length < 2 ^ (prefixWord ++ tailWord_2784782).sum := by decide
  have hdescent : baseEnd_2784782 < baseStart_2784782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784792 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 3, 1, 3]
def baseStart_2784792 : Nat := 118140960795 + 2784792 * 2 ^ 59
def prefixEnd_2784792 : Nat := 4983230072969 + 3 ^ 40 * 2784792 * 2
def baseEnd_2784792 : Nat := 1429936818795573722192981

theorem tailTrace_2784792 : CollatzResearch.WordTrace tailWord_2784792 prefixEnd_2784792 1429936818795573722192981 := by
  unfold tailWord_2784792
  simp only [CollatzResearch.WordTrace]
  refine ⟨50784854263590831726946315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67713139018121108969261753 50784854263590831726946315)
  ·
    refine ⟨76177281395386247590419473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50784854263590831726946315 76177281395386247590419473)
    ·
      refine ⟨57132961046539685692814605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76177281395386247590419473 57132961046539685692814605)
      ·
        refine ⟨21424860392452382134805477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57132961046539685692814605 21424860392452382134805477)
        ·
          refine ⟨4017161323584821650276027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21424860392452382134805477 4017161323584821650276027)
          ·
            refine ⟨6025741985377232475414041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4017161323584821650276027 6025741985377232475414041)
            ·
              refine ⟨4519306489032924356560531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6025741985377232475414041 4519306489032924356560531)
              ·
                refine ⟨6778959733549386534840797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4519306489032924356560531 6778959733549386534840797)
                ·
                  refine ⟨2542109900081019950565299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6778959733549386534840797 2542109900081019950565299)
                  ·
                    refine ⟨3813164850121529925847949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2542109900081019950565299 3813164850121529925847949)
                    ·
                      refine ⟨1429936818795573722192981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3813164850121529925847949 1429936818795573722192981)
                      ·
                        rfl

theorem cell23_2784792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_2784792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784792 prefixEnd_2784792 := by exact prefixLift 2784792
  have htrace : WordTrace (prefixWord ++ tailWord_2784792) baseStart_2784792 baseEnd_2784792 := by
    simpa [prefixWord, tailWord_2784792, baseEnd_2784792] using wordTrace_append hprefix tailTrace_2784792
  have hstable : (prefixWord ++ tailWord_2784792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784792).length < 2 ^ (prefixWord ++ tailWord_2784792).sum := by decide
  have hdescent : baseEnd_2784792 < baseStart_2784792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784900 : List Nat := [2, 3, 2, 1, 5, 1, 2, 2, 1, 2, 2]
def baseStart_2784900 : Nat := 118140960795 + 2784900 * 2 ^ 59
def prefixEnd_2784900 : Nat := 4983230072969 + 3 ^ 40 * 2784900 * 2
def baseEnd_2784900 : Nat := 1429992274706259299642485

theorem tailTrace_2784900 : CollatzResearch.WordTrace tailWord_2784900 prefixEnd_2784900 1429992274706259299642485 := by
  unfold tailWord_2784900
  simp only [CollatzResearch.WordTrace]
  refine ⟨50786823805395198949412077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67715765073860265265882769 50786823805395198949412077)
  ·
    refine ⟨19045058927023199606029529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50786823805395198949412077 19045058927023199606029529)
    ·
      refine ⟨14283794195267399704522147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19045058927023199606029529 14283794195267399704522147)
      ·
        refine ⟨21425691292901099556783221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14283794195267399704522147 21425691292901099556783221)
        ·
          refine ⟨2008658558709478083448427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21425691292901099556783221 2008658558709478083448427)
          ·
            refine ⟨3012987838064217125172641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008658558709478083448427 3012987838064217125172641)
            ·
              refine ⟨2259740878548162843879481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3012987838064217125172641 2259740878548162843879481)
              ·
                refine ⟨1694805658911122132909611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2259740878548162843879481 1694805658911122132909611)
                ·
                  refine ⟨2542208488366683199364417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694805658911122132909611 2542208488366683199364417)
                  ·
                    refine ⟨1906656366275012399523313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2542208488366683199364417 1906656366275012399523313)
                    ·
                      refine ⟨1429992274706259299642485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906656366275012399523313 1429992274706259299642485)
                      ·
                        rfl

theorem cell23_2784900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_2784900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784900 prefixEnd_2784900 := by exact prefixLift 2784900
  have htrace : WordTrace (prefixWord ++ tailWord_2784900) baseStart_2784900 baseEnd_2784900 := by
    simpa [prefixWord, tailWord_2784900, baseEnd_2784900] using wordTrace_append hprefix tailTrace_2784900
  have hstable : (prefixWord ++ tailWord_2784900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784900).length < 2 ^ (prefixWord ++ tailWord_2784900).sum := by decide
  have hdescent : baseEnd_2784900 < baseStart_2784900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784908 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 1, 6, 3]
def baseStart_2784908 : Nat := 118140960795 + 2784908 * 2 ^ 59
def prefixEnd_2784908 : Nat := 4983230072969 + 3 ^ 40 * 2784908 * 2
def baseEnd_2784908 : Nat := 1429996382551495268342447

theorem tailTrace_2784908 : CollatzResearch.WordTrace tailWord_2784908 prefixEnd_2784908 1429996382551495268342447 := by
  unfold tailWord_2784908
  simp only [CollatzResearch.WordTrace]
  refine ⟨50786969697380707632557689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67715959596507610176743585 50786969697380707632557689)
  ·
    refine ⟨38090227273035530724418267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50786969697380707632557689 38090227273035530724418267)
    ·
      refine ⟨57135340909553296086627401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38090227273035530724418267 57135340909553296086627401)
      ·
        refine ⟨42851505682164972064970551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57135340909553296086627401 42851505682164972064970551)
        ·
          refine ⟨64277258523247458097455827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42851505682164972064970551 64277258523247458097455827)
          ·
            refine ⟨96415887784871187146183741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64277258523247458097455827 96415887784871187146183741)
            ·
              refine ⟨36155957919326695179818903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96415887784871187146183741 36155957919326695179818903)
              ·
                refine ⟨54233936878990042769728355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36155957919326695179818903 54233936878990042769728355)
                ·
                  refine ⟨81350905318485064154592533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54233936878990042769728355 81350905318485064154592533)
                  ·
                    refine ⟨3813323686803987382246525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81350905318485064154592533 3813323686803987382246525)
                    ·
                      refine ⟨1429996382551495268342447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3813323686803987382246525 1429996382551495268342447)
                      ·
                        rfl

theorem cell23_2784908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_2784908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784908 prefixEnd_2784908 := by exact prefixLift 2784908
  have htrace : WordTrace (prefixWord ++ tailWord_2784908) baseStart_2784908 baseEnd_2784908 := by
    simpa [prefixWord, tailWord_2784908, baseEnd_2784908] using wordTrace_append hprefix tailTrace_2784908
  have hstable : (prefixWord ++ tailWord_2784908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784908).length < 2 ^ (prefixWord ++ tailWord_2784908).sum := by decide
  have hdescent : baseEnd_2784908 < baseStart_2784908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784928 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 9]
def baseStart_2784928 : Nat := 118140960795 + 2784928 * 2 ^ 59
def prefixEnd_2784928 : Nat := 4983230072969 + 3 ^ 40 * 2784928 * 2
def baseEnd_2784928 : Nat := 158889628018287243343595

theorem tailTrace_2784928 : CollatzResearch.WordTrace tailWord_2784928 prefixEnd_2784928 158889628018287243343595 := by
  unfold tailWord_2784928
  simp only [CollatzResearch.WordTrace]
  refine ⟨50787334427344479340421719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67716445903125972453895625 50787334427344479340421719)
  ·
    refine ⟨76181001641016719010632579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50787334427344479340421719 76181001641016719010632579)
    ·
      refine ⟨114271502461525078515948869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76181001641016719010632579 114271502461525078515948869)
      ·
        refine ⟨21425906711535952221740413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114271502461525078515948869 21425906711535952221740413)
        ·
          refine ⟨8034715016825982083152655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21425906711535952221740413 8034715016825982083152655)
          ·
            refine ⟨12052072525238973124728983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8034715016825982083152655 12052072525238973124728983)
            ·
              refine ⟨18078108787858459687093475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12052072525238973124728983 18078108787858459687093475)
              ·
                refine ⟨27117163181787689530640213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18078108787858459687093475 27117163181787689530640213)
                ·
                  refine ⟨158889628018287243343595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27117163181787689530640213 158889628018287243343595)
                  ·
                    rfl

theorem cell23_2784928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 9].length) (baseStart_2784928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784928 prefixEnd_2784928 := by exact prefixLift 2784928
  have htrace : WordTrace (prefixWord ++ tailWord_2784928) baseStart_2784928 baseEnd_2784928 := by
    simpa [prefixWord, tailWord_2784928, baseEnd_2784928] using wordTrace_append hprefix tailTrace_2784928
  have hstable : (prefixWord ++ tailWord_2784928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784928).length < 2 ^ (prefixWord ++ tailWord_2784928).sum := by decide
  have hdescent : baseEnd_2784928 < baseStart_2784928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784956 : List Nat := [2, 2, 2, 3, 1, 4, 1, 2, 2, 2, 2]
def baseStart_2784956 : Nat := 118140960795 + 2784956 * 2 ^ 59
def prefixEnd_2784956 : Nat := 4983230072969 + 3 ^ 40 * 2784956 * 2
def baseEnd_2784956 : Nat := 1430021029622911080542227

theorem tailTrace_2784956 : CollatzResearch.WordTrace tailWord_2784956 prefixEnd_2784956 1430021029622911080542227 := by
  unfold tailWord_2784956
  simp only [CollatzResearch.WordTrace]
  refine ⟨50787845049293759731431361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67717126732391679641908481 50787845049293759731431361)
  ·
    refine ⟨38090883786970319798573521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50787845049293759731431361 38090883786970319798573521)
    ·
      refine ⟨28568162840227739848930141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38090883786970319798573521 28568162840227739848930141)
      ·
        refine ⟨10713061065085402443348803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28568162840227739848930141 10713061065085402443348803)
        ·
          refine ⟨16069591597628103665023205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10713061065085402443348803 16069591597628103665023205)
          ·
            refine ⟨3013048424555269437191851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16069591597628103665023205 3013048424555269437191851)
            ·
              refine ⟨4519572636832904155787777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3013048424555269437191851 4519572636832904155787777)
              ·
                refine ⟨3389679477624678116840833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4519572636832904155787777 3389679477624678116840833)
                ·
                  refine ⟨2542259608218508587630625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3389679477624678116840833 2542259608218508587630625)
                  ·
                    refine ⟨1906694706163881440722969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2542259608218508587630625 1906694706163881440722969)
                    ·
                      refine ⟨1430021029622911080542227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906694706163881440722969 1430021029622911080542227)
                      ·
                        rfl

theorem cell23_2784956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_2784956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784956 prefixEnd_2784956 := by exact prefixLift 2784956
  have htrace : WordTrace (prefixWord ++ tailWord_2784956) baseStart_2784956 baseEnd_2784956 := by
    simpa [prefixWord, tailWord_2784956, baseEnd_2784956] using wordTrace_append hprefix tailTrace_2784956
  have hstable : (prefixWord ++ tailWord_2784956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784956).length < 2 ^ (prefixWord ++ tailWord_2784956).sum := by decide
  have hdescent : baseEnd_2784956 < baseStart_2784956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2784968 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_2784968 : Nat := 118140960795 + 2784968 * 2 ^ 59
def prefixEnd_2784968 : Nat := 4983230072969 + 3 ^ 40 * 2784968 * 2
def baseEnd_2784968 : Nat := 1430027191390765033592171

theorem tailTrace_2784968 : CollatzResearch.WordTrace tailWord_2784968 prefixEnd_2784968 1430027191390765033592171 := by
  unfold tailWord_2784968
  simp only [CollatzResearch.WordTrace]
  refine ⟨50788063887272022756149779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67717418516362697008199705 50788063887272022756149779)
  ·
    refine ⟨76182095830908034134224669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50788063887272022756149779 76182095830908034134224669)
    ·
      refine ⟨28568285936590512800334251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76182095830908034134224669 28568285936590512800334251)
      ·
        refine ⟨42852428904885769200501377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28568285936590512800334251 42852428904885769200501377)
        ·
          refine ⟨32139321678664326900376033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42852428904885769200501377 32139321678664326900376033)
          ·
            refine ⟨24104491258998245175282025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32139321678664326900376033 24104491258998245175282025)
            ·
              refine ⟨18078368444248683881461519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24104491258998245175282025 18078368444248683881461519)
              ·
                refine ⟨27117552666373025822192279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18078368444248683881461519 27117552666373025822192279)
                ·
                  refine ⟨40676328999559538733288419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27117552666373025822192279 40676328999559538733288419)
                  ·
                    refine ⟨61014493499339308099932629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40676328999559538733288419 61014493499339308099932629)
                    ·
                      refine ⟨1430027191390765033592171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61014493499339308099932629 1430027191390765033592171)
                      ·
                        rfl

theorem cell23_2784968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_2784968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2784968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2784968 prefixEnd_2784968 := by exact prefixLift 2784968
  have htrace : WordTrace (prefixWord ++ tailWord_2784968) baseStart_2784968 baseEnd_2784968 := by
    simpa [prefixWord, tailWord_2784968, baseEnd_2784968] using wordTrace_append hprefix tailTrace_2784968
  have hstable : (prefixWord ++ tailWord_2784968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2784968).length < 2 ^ (prefixWord ++ tailWord_2784968).sum := by decide
  have hdescent : baseEnd_2784968 < baseStart_2784968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2784968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785008 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 6]
def baseStart_2785008 : Nat := 118140960795 + 2785008 * 2 ^ 59
def prefixEnd_2785008 : Nat := 4983230072969 + 3 ^ 40 * 2785008 * 2
def baseEnd_2785008 : Nat := 1430047730616944877091987

theorem tailTrace_2785008 : CollatzResearch.WordTrace tailWord_2785008 prefixEnd_2785008 1430047730616944877091987 := by
  unfold tailWord_2785008
  simp only [CollatzResearch.WordTrace]
  refine ⟨50788793347199566171877839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67718391129599421562503785 50788793347199566171877839)
  ·
    refine ⟨76183190020799349257816759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50788793347199566171877839 76183190020799349257816759)
    ·
      refine ⟨114274785031199023886725139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76183190020799349257816759 114274785031199023886725139)
      ·
        refine ⟨171412177546798535830087709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114274785031199023886725139 171412177546798535830087709)
        ·
          refine ⟨64279566580049450936282891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171412177546798535830087709 64279566580049450936282891)
          ·
            refine ⟨96419349870074176404424337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64279566580049450936282891 96419349870074176404424337)
            ·
              refine ⟨72314512402555632303318253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96419349870074176404424337 72314512402555632303318253)
              ·
                refine ⟨27117942150958362113744345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72314512402555632303318253 27117942150958362113744345)
                ·
                  refine ⟨20338456613218771585308259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27117942150958362113744345 20338456613218771585308259)
                  ·
                    refine ⟨30507684919828157377962389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20338456613218771585308259 30507684919828157377962389)
                    ·
                      refine ⟨1430047730616944877091987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30507684919828157377962389 1430047730616944877091987)
                      ·
                        rfl

theorem cell23_2785008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_2785008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785008 prefixEnd_2785008 := by exact prefixLift 2785008
  have htrace : WordTrace (prefixWord ++ tailWord_2785008) baseStart_2785008 baseEnd_2785008 := by
    simpa [prefixWord, tailWord_2785008, baseEnd_2785008] using wordTrace_append hprefix tailTrace_2785008
  have hstable : (prefixWord ++ tailWord_2785008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785008).length < 2 ^ (prefixWord ++ tailWord_2785008).sum := by decide
  have hdescent : baseEnd_2785008 < baseStart_2785008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785015 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 3]
def baseStart_2785015 : Nat := 118140960795 + 2785015 * 2 ^ 59
def prefixEnd_2785015 : Nat := 4983230072969 + 3 ^ 40 * 2785015 * 2
def baseEnd_2785015 : Nat := 1430051324981526349704455

theorem tailTrace_2785015 : CollatzResearch.WordTrace tailWord_2785015 prefixEnd_2785015 1430051324981526349704455 := by
  unfold tailWord_2785015
  simp only [CollatzResearch.WordTrace]
  refine ⟨101577842005373772539260499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67718561336915848359506999 101577842005373772539260499)
  ·
    refine ⟨152366763008060658808890749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101577842005373772539260499 152366763008060658808890749)
    ·
      refine ⟨57137536128022747053334031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152366763008060658808890749 57137536128022747053334031)
      ·
        refine ⟨85706304192034120580001047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57137536128022747053334031 85706304192034120580001047)
        ·
          refine ⟨128559456288051180870001571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85706304192034120580001047 128559456288051180870001571)
          ·
            refine ⟨192839184432076771305002357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128559456288051180870001571 192839184432076771305002357)
            ·
              refine ⟨18078673540507197309843971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192839184432076771305002357 18078673540507197309843971)
              ·
                refine ⟨27118010310760795964765957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18078673540507197309843971 27118010310760795964765957)
                ·
                  refine ⟨5084626933267649243393617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27118010310760795964765957 5084626933267649243393617)
                  ·
                    refine ⟨3813470199950736932545213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5084626933267649243393617 3813470199950736932545213)
                    ·
                      refine ⟨1430051324981526349704455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3813470199950736932545213 1430051324981526349704455)
                      ·
                        rfl

theorem cell23_2785015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_2785015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785015 prefixEnd_2785015 := by exact prefixLift 2785015
  have htrace : WordTrace (prefixWord ++ tailWord_2785015) baseStart_2785015 baseEnd_2785015 := by
    simpa [prefixWord, tailWord_2785015, baseEnd_2785015] using wordTrace_append hprefix tailTrace_2785015
  have hstable : (prefixWord ++ tailWord_2785015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785015).length < 2 ^ (prefixWord ++ tailWord_2785015).sum := by decide
  have hdescent : baseEnd_2785015 < baseStart_2785015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785095 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 1, 6]
def baseStart_2785095 : Nat := 118140960795 + 2785095 * 2 ^ 59
def prefixEnd_2785095 : Nat := 4983230072969 + 3 ^ 40 * 2785095 * 2
def baseEnd_2785095 : Nat := 476697467811295345568029

theorem tailTrace_2785095 : CollatzResearch.WordTrace tailWord_2785095 prefixEnd_2785095 476697467811295345568029 := by
  unfold tailWord_2785095
  simp only [CollatzResearch.WordTrace]
  refine ⟨101580759845083946202172739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67720506563389297468115159 101580759845083946202172739)
  ·
    refine ⟨152371139767625919303259109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101580759845083946202172739 152371139767625919303259109)
    ·
      refine ⟨28569588706429859869361083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152371139767625919303259109 28569588706429859869361083)
      ·
        refine ⟨42854383059644789804041625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28569588706429859869361083 42854383059644789804041625)
        ·
          refine ⟨32140787294733592353031219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42854383059644789804041625 32140787294733592353031219)
          ·
            refine ⟨48211180942100388529546829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32140787294733592353031219 48211180942100388529546829)
            ·
              refine ⟨18079192853287645698580061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48211180942100388529546829 18079192853287645698580061)
              ·
                refine ⟨6779697319982867136967523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18079192853287645698580061 6779697319982867136967523)
                ·
                  refine ⟨10169545979974300705451285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6779697319982867136967523 10169545979974300705451285)
                  ·
                    refine ⟨476697467811295345568029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10169545979974300705451285 476697467811295345568029)
                    ·
                      rfl

theorem cell23_2785095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_2785095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785095 prefixEnd_2785095 := by exact prefixLift 2785095
  have htrace : WordTrace (prefixWord ++ tailWord_2785095) baseStart_2785095 baseEnd_2785095 := by
    simpa [prefixWord, tailWord_2785095, baseEnd_2785095] using wordTrace_append hprefix tailTrace_2785095
  have hstable : (prefixWord ++ tailWord_2785095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785095).length < 2 ^ (prefixWord ++ tailWord_2785095).sum := by decide
  have hdescent : baseEnd_2785095 < baseStart_2785095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785106 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2]
def baseStart_2785106 : Nat := 118140960795 + 2785106 * 2 ^ 59
def prefixEnd_2785106 : Nat := 4983230072969 + 3 ^ 40 * 2785106 * 2
def baseEnd_2785106 : Nat := 1430098051721085493666537

theorem tailTrace_2785106 : CollatzResearch.WordTrace tailWord_2785106 prefixEnd_2785106 1430098051721085493666537 := by
  unfold tailWord_2785106
  simp only [CollatzResearch.WordTrace]
  refine ⟨25395290262011023770205793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67720774032029396720548781 25395290262011023770205793)
  ·
    refine ⟨19046467696508267827654345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25395290262011023770205793 19046467696508267827654345)
    ·
      refine ⟨14284850772381200870740759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19046467696508267827654345 14284850772381200870740759)
      ·
        refine ⟨21427276158571801306111139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14284850772381200870740759 21427276158571801306111139)
        ·
          refine ⟨32140914237857701959166709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21427276158571801306111139 32140914237857701959166709)
          ·
            refine ⟨3013210709799159558671879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32140914237857701959166709 3013210709799159558671879)
            ·
              refine ⟨4519816064698739338007819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3013210709799159558671879 4519816064698739338007819)
              ·
                refine ⟨6779724097048109007011729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4519816064698739338007819 6779724097048109007011729)
                ·
                  refine ⟨5084793072786081755258797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6779724097048109007011729 5084793072786081755258797)
                  ·
                    refine ⟨1906797402294780658222049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5084793072786081755258797 1906797402294780658222049)
                    ·
                      refine ⟨1430098051721085493666537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906797402294780658222049 1430098051721085493666537)
                      ·
                        rfl

theorem cell23_2785106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_2785106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785106 prefixEnd_2785106 := by exact prefixLift 2785106
  have htrace : WordTrace (prefixWord ++ tailWord_2785106) baseStart_2785106 baseEnd_2785106 := by
    simpa [prefixWord, tailWord_2785106, baseEnd_2785106] using wordTrace_append hprefix tailTrace_2785106
  have hstable : (prefixWord ++ tailWord_2785106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785106).length < 2 ^ (prefixWord ++ tailWord_2785106).sum := by decide
  have hdescent : baseEnd_2785106 < baseStart_2785106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785119 : List Nat := [1, 1, 2, 3, 1, 4, 4, 1, 1, 1, 4]
def baseStart_2785119 : Nat := 118140960795 + 2785119 * 2 ^ 59
def prefixEnd_2785119 : Nat := 4983230072969 + 3 ^ 40 * 2785119 * 2
def baseEnd_2785119 : Nat := 1430104726969593942803977

theorem tailTrace_2785119 : CollatzResearch.WordTrace tailWord_2785119 prefixEnd_2785119 1430104726969593942803977 := by
  unfold tailWord_2785119
  simp only [CollatzResearch.WordTrace]
  refine ⟨101581635196996998301046411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67721090131331332200697607 101581635196996998301046411)
  ·
    refine ⟨152372452795495497451569617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101581635196996998301046411 152372452795495497451569617)
    ·
      refine ⟨114279339596621623088677213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152372452795495497451569617 114279339596621623088677213)
      ·
        refine ⟨42854752348733108658253955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114279339596621623088677213 42854752348733108658253955)
        ·
          refine ⟨64282128523099662987380933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42854752348733108658253955 64282128523099662987380933)
          ·
            refine ⟨12052899098081186810133925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64282128523099662987380933 12052899098081186810133925)
            ·
              refine ⟨2259918580890222526900111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12052899098081186810133925 2259918580890222526900111)
              ·
                refine ⟨3389877871335333790350167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2259918580890222526900111 3389877871335333790350167)
                ·
                  refine ⟨5084816807003000685525251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3389877871335333790350167 5084816807003000685525251)
                  ·
                    refine ⟨7627225210504501028287877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5084816807003000685525251 7627225210504501028287877)
                    ·
                      refine ⟨1430104726969593942803977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7627225210504501028287877 1430104726969593942803977)
                      ·
                        rfl

theorem cell23_2785119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_2785119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785119 prefixEnd_2785119 := by exact prefixLift 2785119
  have htrace : WordTrace (prefixWord ++ tailWord_2785119) baseStart_2785119 baseEnd_2785119 := by
    simpa [prefixWord, tailWord_2785119, baseEnd_2785119] using wordTrace_append hprefix tailTrace_2785119
  have hstable : (prefixWord ++ tailWord_2785119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785119).length < 2 ^ (prefixWord ++ tailWord_2785119).sum := by decide
  have hdescent : baseEnd_2785119 < baseStart_2785119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785135 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 3]
def baseStart_2785135 : Nat := 118140960795 + 2785135 * 2 ^ 59
def prefixEnd_2785135 : Nat := 4983230072969 + 3 ^ 40 * 2785135 * 2
def baseEnd_2785135 : Nat := 1430112942660065880203903

theorem tailTrace_2785135 : CollatzResearch.WordTrace tailWord_2785135 prefixEnd_2785135 1430112942660065880203903 := by
  unfold tailWord_2785135
  simp only [CollatzResearch.WordTrace]
  refine ⟨101582218764939033033628859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67721479176626022022419239 101582218764939033033628859)
  ·
    refine ⟨152373328147408549550443289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101582218764939033033628859 152373328147408549550443289)
    ·
      refine ⟨114279996110556412162832467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152373328147408549550443289 114279996110556412162832467)
      ·
        refine ⟨171419994165834618244248701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114279996110556412162832467 171419994165834618244248701)
        ·
          refine ⟨64282497812187981841593263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171419994165834618244248701 64282497812187981841593263)
          ·
            refine ⟨96423746718281972762389895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64282497812187981841593263 96423746718281972762389895)
            ·
              refine ⟨144635620077422959143584843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96423746718281972762389895 144635620077422959143584843)
              ·
                refine ⟨216953430116134438715377265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144635620077422959143584843 216953430116134438715377265)
                ·
                  refine ⟨162715072587100829036532949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216953430116134438715377265 162715072587100829036532949)
                  ·
                    refine ⟨3813634513760175680543741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 162715072587100829036532949 3813634513760175680543741)
                    ·
                      refine ⟨1430112942660065880203903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3813634513760175680543741 1430112942660065880203903)
                      ·
                        rfl

theorem cell23_2785135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 3].length) (baseStart_2785135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785135 prefixEnd_2785135 := by exact prefixLift 2785135
  have htrace : WordTrace (prefixWord ++ tailWord_2785135) baseStart_2785135 baseEnd_2785135 := by
    simpa [prefixWord, tailWord_2785135, baseEnd_2785135] using wordTrace_append hprefix tailTrace_2785135
  have hstable : (prefixWord ++ tailWord_2785135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785135).length < 2 ^ (prefixWord ++ tailWord_2785135).sum := by decide
  have hdescent : baseEnd_2785135 < baseStart_2785135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785159 : List Nat := [1, 1, 4, 2, 4, 2, 2, 7]
def baseStart_2785159 : Nat := 118140960795 + 2785159 * 2 ^ 59
def prefixEnd_2785159 : Nat := 4983230072969 + 3 ^ 40 * 2785159 * 2
def baseEnd_2785159 : Nat := 52967602451695325418659

theorem tailTrace_2785159 : CollatzResearch.WordTrace tailWord_2785159 prefixEnd_2785159 52967602451695325418659 := by
  unfold tailWord_2785159
  simp only [CollatzResearch.WordTrace]
  refine ⟨101583094116852085132502531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67722062744568056755001687 101583094116852085132502531)
  ·
    refine ⟨152374641175278127698753797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101583094116852085132502531 152374641175278127698753797)
    ·
      refine ⟨28570245220364648943516337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152374641175278127698753797 28570245220364648943516337)
      ·
        refine ⟨21427683915273486707637253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28570245220364648943516337 21427683915273486707637253)
        ·
          refine ⟨4017690734113778757681985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21427683915273486707637253 4017690734113778757681985)
          ·
            refine ⟨3013268050585334068261489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4017690734113778757681985 3013268050585334068261489)
            ·
              refine ⟨2259951037939000551196117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3013268050585334068261489 2259951037939000551196117)
              ·
                refine ⟨52967602451695325418659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2259951037939000551196117 52967602451695325418659)
                ·
                  rfl

theorem cell23_2785159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 7].length) (baseStart_2785159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785159 prefixEnd_2785159 := by exact prefixLift 2785159
  have htrace : WordTrace (prefixWord ++ tailWord_2785159) baseStart_2785159 baseEnd_2785159 := by
    simpa [prefixWord, tailWord_2785159, baseEnd_2785159] using wordTrace_append hprefix tailTrace_2785159
  have hstable : (prefixWord ++ tailWord_2785159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785159).length < 2 ^ (prefixWord ++ tailWord_2785159).sum := by decide
  have hdescent : baseEnd_2785159 < baseStart_2785159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785170 : List Nat := [3, 2, 3, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_2785170 : Nat := 118140960795 + 2785170 * 2 ^ 59
def prefixEnd_2785170 : Nat := 4983230072969 + 3 ^ 40 * 2785170 * 2
def baseEnd_2785170 : Nat := 1430130914482973243266243

theorem tailTrace_2785170 : CollatzResearch.WordTrace tailWord_2785170 prefixEnd_2785170 1430130914482973243266243 := by
  unfold tailWord_2785170
  simp only [CollatzResearch.WordTrace]
  refine ⟨25395873829953058502788241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67722330213208156007435309 25395873829953058502788241)
  ·
    refine ⟨19046905372464793877091181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25395873829953058502788241 19046905372464793877091181)
    ·
      refine ⟨7142589514674297703909193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19046905372464793877091181 7142589514674297703909193)
      ·
        refine ⟨5356942136005723277931895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7142589514674297703909193 5356942136005723277931895)
        ·
          refine ⟨8035413204008584916897843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5356942136005723277931895 8035413204008584916897843)
          ·
            refine ⟨12053119806012877375346765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8035413204008584916897843 12053119806012877375346765)
            ·
              refine ⟨4519919927254829015755037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12053119806012877375346765 4519919927254829015755037)
              ·
                refine ⟨1694969972720560880908139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4519919927254829015755037 1694969972720560880908139)
                ·
                  refine ⟨2542454959080841321362209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694969972720560880908139 2542454959080841321362209)
                  ·
                    refine ⟨1906841219310630991021657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2542454959080841321362209 1906841219310630991021657)
                    ·
                      refine ⟨1430130914482973243266243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906841219310630991021657 1430130914482973243266243)
                      ·
                        rfl

theorem cell23_2785170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_2785170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785170 prefixEnd_2785170 := by exact prefixLift 2785170
  have htrace : WordTrace (prefixWord ++ tailWord_2785170) baseStart_2785170 baseEnd_2785170 := by
    simpa [prefixWord, tailWord_2785170, baseEnd_2785170] using wordTrace_append hprefix tailTrace_2785170
  have hstable : (prefixWord ++ tailWord_2785170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785170).length < 2 ^ (prefixWord ++ tailWord_2785170).sum := by decide
  have hdescent : baseEnd_2785170 < baseStart_2785170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785195 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 5]
def baseStart_2785195 : Nat := 118140960795 + 2785195 * 2 ^ 59
def prefixEnd_2785195 : Nat := 4983230072969 + 3 ^ 40 * 2785195 * 2
def baseEnd_2785195 : Nat := 1430143751499335645453627

theorem tailTrace_2785195 : CollatzResearch.WordTrace tailWord_2785195 prefixEnd_2785195 1430143751499335645453627 := by
  unfold tailWord_2785195
  simp only [CollatzResearch.WordTrace]
  refine ⟨101584407144721663280813039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67722938096481108853875359 101584407144721663280813039)
  ·
    refine ⟨152376610717082494921219559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101584407144721663280813039 152376610717082494921219559)
    ·
      refine ⟨228564916075623742381829339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152376610717082494921219559 228564916075623742381829339)
      ·
        refine ⟨342847374113435613572744009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228564916075623742381829339 342847374113435613572744009)
        ·
          refine ⟨257135530585076710179558007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342847374113435613572744009 257135530585076710179558007)
          ·
            refine ⟨385703295877615065269337011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257135530585076710179558007 385703295877615065269337011)
            ·
              refine ⟨578554943816422597904005517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385703295877615065269337011 578554943816422597904005517)
              ·
                refine ⟨216958103931158474214002069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 578554943816422597904005517 216958103931158474214002069)
                ·
                  refine ⟨10169911121773053478781347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 216958103931158474214002069 10169911121773053478781347)
                  ·
                    refine ⟨15254866682659580218172021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10169911121773053478781347 15254866682659580218172021)
                    ·
                      refine ⟨1430143751499335645453627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15254866682659580218172021 1430143751499335645453627)
                      ·
                        rfl

theorem cell23_2785195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 5].length) (baseStart_2785195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785195 prefixEnd_2785195 := by exact prefixLift 2785195
  have htrace : WordTrace (prefixWord ++ tailWord_2785195) baseStart_2785195 baseEnd_2785195 := by
    simpa [prefixWord, tailWord_2785195, baseEnd_2785195] using wordTrace_append hprefix tailTrace_2785195
  have hstable : (prefixWord ++ tailWord_2785195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785195).length < 2 ^ (prefixWord ++ tailWord_2785195).sum := by decide
  have hdescent : baseEnd_2785195 < baseStart_2785195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785209 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 1, 4, 2]
def baseStart_2785209 : Nat := 118140960795 + 2785209 * 2 ^ 59
def prefixEnd_2785209 : Nat := 4983230072969 + 3 ^ 40 * 2785209 * 2
def baseEnd_2785209 : Nat := 1430150940228498590678563

theorem tailTrace_2785209 : CollatzResearch.WordTrace tailWord_2785209 prefixEnd_2785209 1430150940228498590678563 := by
  unfold tailWord_2785209
  simp only [CollatzResearch.WordTrace]
  refine ⟨101584917766670943671822681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67723278511113962447881787 101584917766670943671822681)
  ·
    refine ⟨76188688325003207753867011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101584917766670943671822681 76188688325003207753867011)
    ·
      refine ⟨114283032487504811630800517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76188688325003207753867011 114283032487504811630800517)
      ·
        refine ⟨21428068591407152180775097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114283032487504811630800517 21428068591407152180775097)
        ·
          refine ⟨16071051443555364135581323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21428068591407152180775097 16071051443555364135581323)
          ·
            refine ⟨24106577165333046203371985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16071051443555364135581323 24106577165333046203371985)
            ·
              refine ⟨18079932873999784652528989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24106577165333046203371985 18079932873999784652528989)
              ·
                refine ⟨6779974827749919244698371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18079932873999784652528989 6779974827749919244698371)
                ·
                  refine ⟨10169962241624878867047557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6779974827749919244698371 10169962241624878867047557)
                  ·
                    refine ⟨1906867920304664787571417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10169962241624878867047557 1906867920304664787571417)
                    ·
                      refine ⟨1430150940228498590678563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906867920304664787571417 1430150940228498590678563)
                      ·
                        rfl

theorem cell23_2785209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_2785209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785209 prefixEnd_2785209 := by exact prefixLift 2785209
  have htrace : WordTrace (prefixWord ++ tailWord_2785209) baseStart_2785209 baseEnd_2785209 := by
    simpa [prefixWord, tailWord_2785209, baseEnd_2785209] using wordTrace_append hprefix tailTrace_2785209
  have hstable : (prefixWord ++ tailWord_2785209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785209).length < 2 ^ (prefixWord ++ tailWord_2785209).sum := by decide
  have hdescent : baseEnd_2785209 < baseStart_2785209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785213 : List Nat := [1, 4, 1, 2, 3, 3, 1, 2, 1, 3, 2]
def baseStart_2785213 : Nat := 118140960795 + 2785213 * 2 ^ 59
def prefixEnd_2785213 : Nat := 4983230072969 + 3 ^ 40 * 2785213 * 2
def baseEnd_2785213 : Nat := 1430152994151116575028545

theorem tailTrace_2785213 : CollatzResearch.WordTrace tailWord_2785213 prefixEnd_2785213 1430152994151116575028545 := by
  unfold tailWord_2785213
  simp only [CollatzResearch.WordTrace]
  refine ⟨101585063658656452354968293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67723375772437634903312195 101585063658656452354968293)
  ·
    refine ⟨19047199435998084816556555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101585063658656452354968293 19047199435998084816556555)
    ·
      refine ⟨28570799153997127224834833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19047199435998084816556555 28570799153997127224834833)
      ·
        refine ⟨21428099365497845418626125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28570799153997127224834833 21428099365497845418626125)
        ·
          refine ⟨8035537262061692031984797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21428099365497845418626125 8035537262061692031984797)
          ·
            refine ⟨3013326473273134511994299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8035537262061692031984797 3013326473273134511994299)
            ·
              refine ⟨4519989709909701767991449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3013326473273134511994299 4519989709909701767991449)
              ·
                refine ⟨3389992282432276325993587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4519989709909701767991449 3389992282432276325993587)
                ·
                  refine ⟨5084988423648414488990381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3389992282432276325993587 5084988423648414488990381)
                  ·
                    refine ⟨1906870658868155433371393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5084988423648414488990381 1906870658868155433371393)
                    ·
                      refine ⟨1430152994151116575028545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906870658868155433371393 1430152994151116575028545)
                      ·
                        rfl

theorem cell23_2785213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_2785213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785213 prefixEnd_2785213 := by exact prefixLift 2785213
  have htrace : WordTrace (prefixWord ++ tailWord_2785213) baseStart_2785213 baseEnd_2785213 := by
    simpa [prefixWord, tailWord_2785213, baseEnd_2785213] using wordTrace_append hprefix tailTrace_2785213
  have hstable : (prefixWord ++ tailWord_2785213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785213).length < 2 ^ (prefixWord ++ tailWord_2785213).sum := by decide
  have hdescent : baseEnd_2785213 < baseStart_2785213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785215 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 9]
def baseStart_2785215 : Nat := 118140960795 + 2785215 * 2 ^ 59
def prefixEnd_2785215 : Nat := 4983230072969 + 3 ^ 40 * 2785215 * 2
def baseEnd_2785215 : Nat := 158906002345825063022615

theorem tailTrace_2785215 : CollatzResearch.WordTrace tailWord_2785215 prefixEnd_2785215 158906002345825063022615 := by
  unfold tailWord_2785215
  simp only [CollatzResearch.WordTrace]
  refine ⟨101585136604649206696541099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67723424403099471131027399 101585136604649206696541099)
  ·
    refine ⟨152377704906973810044811649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101585136604649206696541099 152377704906973810044811649)
    ·
      refine ⟨114283278680230357533608737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152377704906973810044811649 114283278680230357533608737)
      ·
        refine ⟨85712459010172768150206553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114283278680230357533608737 85712459010172768150206553)
        ·
          refine ⟨64284344257629576112654915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85712459010172768150206553 64284344257629576112654915)
          ·
            refine ⟨96426516386444364168982373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64284344257629576112654915 96426516386444364168982373)
            ·
              refine ⟨18079971822458318281684195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96426516386444364168982373 18079971822458318281684195)
              ·
                refine ⟨27119957733687477422526293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18079971822458318281684195 27119957733687477422526293)
                ·
                  refine ⟨158906002345825063022615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27119957733687477422526293 158906002345825063022615)
                  ·
                    rfl

theorem cell23_2785215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 9].length) (baseStart_2785215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785215 prefixEnd_2785215 := by exact prefixLift 2785215
  have htrace : WordTrace (prefixWord ++ tailWord_2785215) baseStart_2785215 baseEnd_2785215 := by
    simpa [prefixWord, tailWord_2785215, baseEnd_2785215] using wordTrace_append hprefix tailTrace_2785215
  have hstable : (prefixWord ++ tailWord_2785215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785215).length < 2 ^ (prefixWord ++ tailWord_2785215).sum := by decide
  have hdescent : baseEnd_2785215 < baseStart_2785215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785299 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 2, 4, 2]
def baseStart_2785299 : Nat := 118140960795 + 2785299 * 2 ^ 59
def prefixEnd_2785299 : Nat := 4983230072969 + 3 ^ 40 * 2785299 * 2
def baseEnd_2785299 : Nat := 1430197153487403238553149

theorem tailTrace_2785299 : CollatzResearch.WordTrace tailWord_2785299 prefixEnd_2785299 1430197153487403238553149 := by
  unfold tailWord_2785299
  simp only [CollatzResearch.WordTrace]
  refine ⟨101588200336344889042598951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67725466890896592695065967 101588200336344889042598951)
  ·
    refine ⟨152382300504517333563898427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101588200336344889042598951 152382300504517333563898427)
    ·
      refine ⟨228573450756776000345847641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152382300504517333563898427 228573450756776000345847641)
      ·
        refine ⟨171430088067582000259385731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228573450756776000345847641 171430088067582000259385731)
        ·
          refine ⟨257145132101373000389078597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171430088067582000259385731 257145132101373000389078597)
          ·
            refine ⟨48214712269007437572952237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257145132101373000389078597 48214712269007437572952237)
            ·
              refine ⟨18080517100877789089857089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48214712269007437572952237 18080517100877789089857089)
              ·
                refine ⟨13560387825658341817392817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18080517100877789089857089 13560387825658341817392817)
                ·
                  refine ⟨10170290869243756363044613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13560387825658341817392817 10170290869243756363044613)
                  ·
                    refine ⟨1906929537983204318070865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10170290869243756363044613 1906929537983204318070865)
                    ·
                      refine ⟨1430197153487403238553149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1906929537983204318070865 1430197153487403238553149)
                      ·
                        rfl

theorem cell23_2785299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 4, 2].length) (baseStart_2785299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785299 prefixEnd_2785299 := by exact prefixLift 2785299
  have htrace : WordTrace (prefixWord ++ tailWord_2785299) baseStart_2785299 baseEnd_2785299 := by
    simpa [prefixWord, tailWord_2785299, baseEnd_2785299] using wordTrace_append hprefix tailTrace_2785299
  have hstable : (prefixWord ++ tailWord_2785299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785299).length < 2 ^ (prefixWord ++ tailWord_2785299).sum := by decide
  have hdescent : baseEnd_2785299 < baseStart_2785299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785326 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 3, 4]
def baseStart_2785326 : Nat := 118140960795 + 2785326 * 2 ^ 59
def prefixEnd_2785326 : Nat := 4983230072969 + 3 ^ 40 * 2785326 * 2
def baseEnd_2785326 : Nat := 476737005821691544305175

theorem tailTrace_2785326 : CollatzResearch.WordTrace tailWord_2785326 prefixEnd_2785326 476737005821691544305175 := by
  unfold tailWord_2785326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12698648138405884081728979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67726123404831381769221221 12698648138405884081728979)
  ·
    refine ⟨19047972207608826122593469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12698648138405884081728979 19047972207608826122593469)
    ·
      refine ⟨7142989577853309795972551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19047972207608826122593469 7142989577853309795972551)
      ·
        refine ⟨10714484366779964693958827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7142989577853309795972551 10714484366779964693958827)
        ·
          refine ⟨16071726550169947040938241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10714484366779964693958827 16071726550169947040938241)
          ·
            refine ⟨12053794912627460280703681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16071726550169947040938241 12053794912627460280703681)
            ·
              refine ⟨9040346184470595210527761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12053794912627460280703681 9040346184470595210527761)
              ·
                refine ⟨6780259638352946407895821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9040346184470595210527761 6780259638352946407895821)
                ·
                  refine ⟨2542597364382354902960933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6780259638352946407895821 2542597364382354902960933)
                  ·
                    refine ⟨476737005821691544305175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2542597364382354902960933 476737005821691544305175)
                    ·
                      rfl

theorem cell23_2785326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_2785326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785326 prefixEnd_2785326 := by exact prefixLift 2785326
  have htrace : WordTrace (prefixWord ++ tailWord_2785326) baseStart_2785326 baseEnd_2785326 := by
    simpa [prefixWord, tailWord_2785326, baseEnd_2785326] using wordTrace_append hprefix tailTrace_2785326
  have hstable : (prefixWord ++ tailWord_2785326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785326).length < 2 ^ (prefixWord ++ tailWord_2785326).sum := by decide
  have hdescent : baseEnd_2785326 < baseStart_2785326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785373 : List Nat := [1, 4, 4, 1, 1, 1, 4, 1, 6]
def baseStart_2785373 : Nat := 118140960795 + 2785373 * 2 ^ 59
def prefixEnd_2785373 : Nat := 4983230072969 + 3 ^ 40 * 2785373 * 2
def baseEnd_2785373 : Nat := 158915016783981772114201

theorem tailTrace_2785373 : CollatzResearch.WordTrace tailWord_2785373 prefixEnd_2785373 158915016783981772114201 := by
  unfold tailWord_2785373
  simp only [CollatzResearch.WordTrace]
  refine ⟨101590899338076799680792773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67727266225384533120528515 101590899338076799680792773)
  ·
    refine ⟨19048293625889399940148645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101590899338076799680792773 19048293625889399940148645)
    ·
      refine ⟨3571555054854262488777871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19048293625889399940148645 3571555054854262488777871)
      ·
        refine ⟨5357332582281393733166807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3571555054854262488777871 5357332582281393733166807)
        ·
          refine ⟨8035998873422090599750211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5357332582281393733166807 8035998873422090599750211)
          ·
            refine ⟨12053998310133135899625317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8035998873422090599750211 12053998310133135899625317)
            ·
              refine ⟨2260124683149962981179747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12053998310133135899625317 2260124683149962981179747)
              ·
                refine ⟨3390187024724944471769621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260124683149962981179747 3390187024724944471769621)
                ·
                  refine ⟨158915016783981772114201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3390187024724944471769621 158915016783981772114201)
                  ·
                    rfl

theorem cell23_2785373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_2785373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785373 prefixEnd_2785373 := by exact prefixLift 2785373
  have htrace : WordTrace (prefixWord ++ tailWord_2785373) baseStart_2785373 baseEnd_2785373 := by
    simpa [prefixWord, tailWord_2785373, baseEnd_2785373] using wordTrace_append hprefix tailTrace_2785373
  have hstable : (prefixWord ++ tailWord_2785373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785373).length < 2 ^ (prefixWord ++ tailWord_2785373).sum := by decide
  have hdescent : baseEnd_2785373 < baseStart_2785373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785386 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 3, 5]
def baseStart_2785386 : Nat := 118140960795 + 2785386 * 2 ^ 59
def prefixEnd_2785386 : Nat := 4983230072969 + 3 ^ 40 * 2785386 * 2
def baseEnd_2785386 : Nat := 476747275434781466055083

theorem tailTrace_2785386 : CollatzResearch.WordTrace tailWord_2785386 prefixEnd_2785386 476747275434781466055083 := by
  unfold tailWord_2785386
  simp only [CollatzResearch.WordTrace]
  refine ⟨25397843371757425725254003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67727582324686468600677341 25397843371757425725254003)
  ·
    refine ⟨38096765057636138587881005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25397843371757425725254003 38096765057636138587881005)
    ·
      refine ⟨14286286896613551970455377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38096765057636138587881005 14286286896613551970455377)
      ·
        refine ⟨10714715172460163977841533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14286286896613551970455377 10714715172460163977841533)
        ·
          refine ⟨4018018189672561491690575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10714715172460163977841533 4018018189672561491690575)
          ·
            refine ⟨6027027284508842237535863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4018018189672561491690575 6027027284508842237535863)
            ·
              refine ⟨9040540926763263356303795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6027027284508842237535863 9040540926763263356303795)
              ·
                refine ⟨13560811390144895034455693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9040540926763263356303795 13560811390144895034455693)
                ·
                  refine ⟨5085304271304335637920885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13560811390144895034455693 5085304271304335637920885)
                  ·
                    refine ⟨476747275434781466055083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5085304271304335637920885 476747275434781466055083)
                    ·
                      rfl

theorem cell23_2785386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_2785386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785386 prefixEnd_2785386 := by exact prefixLift 2785386
  have htrace : WordTrace (prefixWord ++ tailWord_2785386) baseStart_2785386 baseEnd_2785386 := by
    simpa [prefixWord, tailWord_2785386, baseEnd_2785386] using wordTrace_append hprefix tailTrace_2785386
  have hstable : (prefixWord ++ tailWord_2785386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785386).length < 2 ^ (prefixWord ++ tailWord_2785386).sum := by decide
  have hdescent : baseEnd_2785386 < baseStart_2785386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785399 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 1, 6]
def baseStart_2785399 : Nat := 118140960795 + 2785399 * 2 ^ 59
def prefixEnd_2785399 : Nat := 4983230072969 + 3 ^ 40 * 2785399 * 2
def baseEnd_2785399 : Nat := 476749500517617615767563

theorem tailTrace_2785399 : CollatzResearch.WordTrace tailWord_2785399 prefixEnd_2785399 476749500517617615767563 := by
  unfold tailWord_2785399
  simp only [CollatzResearch.WordTrace]
  refine ⟨101591847635982606121239251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67727898423988404080826167 101591847635982606121239251)
  ·
    refine ⟨152387771453973909181858877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101591847635982606121239251 152387771453973909181858877)
    ·
      refine ⟨57145414295240215943197079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152387771453973909181858877 57145414295240215943197079)
      ·
        refine ⟨85718121442860323914795619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57145414295240215943197079 85718121442860323914795619)
        ·
          refine ⟨128577182164290485872193429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85718121442860323914795619 128577182164290485872193429)
          ·
            refine ⟨6027055413951116525259067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 128577182164290485872193429 6027055413951116525259067)
            ·
              refine ⟨9040583120926674787888601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6027055413951116525259067 9040583120926674787888601)
              ·
                refine ⟨6780437340695006090916451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9040583120926674787888601 6780437340695006090916451)
                ·
                  refine ⟨10170656011042509136374677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6780437340695006090916451 10170656011042509136374677)
                  ·
                    refine ⟨476749500517617615767563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10170656011042509136374677 476749500517617615767563)
                    ·
                      rfl

theorem cell23_2785399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_2785399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785399 prefixEnd_2785399 := by exact prefixLift 2785399
  have htrace : WordTrace (prefixWord ++ tailWord_2785399) baseStart_2785399 baseEnd_2785399 := by
    simpa [prefixWord, tailWord_2785399, baseEnd_2785399] using wordTrace_append hprefix tailTrace_2785399
  have hstable : (prefixWord ++ tailWord_2785399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785399).length < 2 ^ (prefixWord ++ tailWord_2785399).sum := by decide
  have hdescent : baseEnd_2785399 < baseStart_2785399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785402 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6]
def baseStart_2785402 : Nat := 118140960795 + 2785402 * 2 ^ 59
def prefixEnd_2785402 : Nat := 4983230072969 + 3 ^ 40 * 2785402 * 2
def baseEnd_2785402 : Nat := 1430250041994816335565175

theorem tailTrace_2785402 : CollatzResearch.WordTrace tailWord_2785402 prefixEnd_2785402 1430250041994816335565175 := by
  unfold tailWord_2785402
  simp only [CollatzResearch.WordTrace]
  refine ⟨25397989263742934408399615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67727971369981158422398973 25397989263742934408399615)
  ·
    refine ⟨38096983895614401612599423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25397989263742934408399615 38096983895614401612599423)
    ·
      refine ⟨57145475843421602418899135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38096983895614401612599423 57145475843421602418899135)
      ·
        refine ⟨85718213765132403628348703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57145475843421602418899135 85718213765132403628348703)
        ·
          refine ⟨128577320647698605442523055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85718213765132403628348703 128577320647698605442523055)
          ·
            refine ⟨192865980971547908163784583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128577320647698605442523055 192865980971547908163784583)
            ·
              refine ⟨289298971457321862245676875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192865980971547908163784583 289298971457321862245676875)
              ·
                refine ⟨433948457185982793368515313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289298971457321862245676875 433948457185982793368515313)
                ·
                  refine ⟨325461342889487095026386485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433948457185982793368515313 325461342889487095026386485)
                  ·
                    refine ⟨30512000895889415158723733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 325461342889487095026386485 30512000895889415158723733)
                    ·
                      refine ⟨1430250041994816335565175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30512000895889415158723733 1430250041994816335565175)
                      ·
                        rfl

theorem cell23_2785402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_2785402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785402 prefixEnd_2785402 := by exact prefixLift 2785402
  have htrace : WordTrace (prefixWord ++ tailWord_2785402) baseStart_2785402 baseEnd_2785402 := by
    simpa [prefixWord, tailWord_2785402, baseEnd_2785402] using wordTrace_append hprefix tailTrace_2785402
  have hstable : (prefixWord ++ tailWord_2785402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785402).length < 2 ^ (prefixWord ++ tailWord_2785402).sum := by decide
  have hdescent : baseEnd_2785402 < baseStart_2785402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785426 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_2785426 : Nat := 118140960795 + 2785426 * 2 ^ 59
def prefixEnd_2785426 : Nat := 4983230072969 + 3 ^ 40 * 2785426 * 2
def baseEnd_2785426 : Nat := 1430262365530524241665065

theorem tailTrace_2785426 : CollatzResearch.WordTrace tailWord_2785426 prefixEnd_2785426 1430262365530524241665065 := by
  unfold tailWord_2785426
  simp only [CollatzResearch.WordTrace]
  refine ⟨25398208101721197433118033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67728554937923193154981421 25398208101721197433118033)
  ·
    refine ⟨19048656076290898074838525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25398208101721197433118033 19048656076290898074838525)
    ·
      refine ⟨7143246028609086778064447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19048656076290898074838525 7143246028609086778064447)
      ·
        refine ⟨10714869042913630167096671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7143246028609086778064447 10714869042913630167096671)
        ·
          refine ⟨16072303564370445250645007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10714869042913630167096671 16072303564370445250645007)
          ·
            refine ⟨24108455346555667875967511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16072303564370445250645007 24108455346555667875967511)
            ·
              refine ⟨36162683019833501813951267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24108455346555667875967511 36162683019833501813951267)
              ·
                refine ⟨54244024529750252720926901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36162683019833501813951267 54244024529750252720926901)
                ·
                  refine ⟨5085377299664086192586897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54244024529750252720926901 5085377299664086192586897)
                  ·
                    refine ⟨3814032974748064644440173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5085377299664086192586897 3814032974748064644440173)
                    ·
                      refine ⟨1430262365530524241665065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3814032974748064644440173 1430262365530524241665065)
                      ·
                        rfl

theorem cell23_2785426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_2785426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785426 prefixEnd_2785426 := by exact prefixLift 2785426
  have htrace : WordTrace (prefixWord ++ tailWord_2785426) baseStart_2785426 baseEnd_2785426 := by
    simpa [prefixWord, tailWord_2785426, baseEnd_2785426] using wordTrace_append hprefix tailTrace_2785426
  have hstable : (prefixWord ++ tailWord_2785426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785426).length < 2 ^ (prefixWord ++ tailWord_2785426).sum := by decide
  have hdescent : baseEnd_2785426 < baseStart_2785426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785436 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_2785436 : Nat := 118140960795 + 2785436 * 2 ^ 59
def prefixEnd_2785436 : Nat := 4983230072969 + 3 ^ 40 * 2785436 * 2
def baseEnd_2785436 : Nat := 1430267500337069202540019

theorem tailTrace_2785436 : CollatzResearch.WordTrace tailWord_2785436 prefixEnd_2785436 1430267500337069202540019 := by
  unfold tailWord_2785436
  simp only [CollatzResearch.WordTrace]
  refine ⟨50796598568424280720168081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67728798091232374293557441 50796598568424280720168081)
  ·
    refine ⟨38097448926318210540126061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50796598568424280720168081 38097448926318210540126061)
    ·
      refine ⟨14286543347369328952547273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38097448926318210540126061 14286543347369328952547273)
      ·
        refine ⟨10714907510526996714410455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14286543347369328952547273 10714907510526996714410455)
        ·
          refine ⟨16072361265790495071615683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10714907510526996714410455 16072361265790495071615683)
          ·
            refine ⟨24108541898685742607423525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16072361265790495071615683 24108541898685742607423525)
            ·
              refine ⟨4520351606003576738891911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24108541898685742607423525 4520351606003576738891911)
              ·
                refine ⟨6780527409005365108337867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4520351606003576738891911 6780527409005365108337867)
                ·
                  refine ⟨10170791113508047662506801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6780527409005365108337867 10170791113508047662506801)
                  ·
                    refine ⟨7628093335131035746880101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10170791113508047662506801 7628093335131035746880101)
                    ·
                      refine ⟨1430267500337069202540019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7628093335131035746880101 1430267500337069202540019)
                      ·
                        rfl

theorem cell23_2785436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_2785436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785436 prefixEnd_2785436 := by exact prefixLift 2785436
  have htrace : WordTrace (prefixWord ++ tailWord_2785436) baseStart_2785436 baseEnd_2785436 := by
    simpa [prefixWord, tailWord_2785436, baseEnd_2785436] using wordTrace_append hprefix tailTrace_2785436
  have hstable : (prefixWord ++ tailWord_2785436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785436).length < 2 ^ (prefixWord ++ tailWord_2785436).sum := by decide
  have hdescent : baseEnd_2785436 < baseStart_2785436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785454 : List Nat := [4, 1, 4, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2785454 : Nat := 118140960795 + 2785454 * 2 ^ 59
def prefixEnd_2785454 : Nat := 4983230072969 + 3 ^ 40 * 2785454 * 2
def baseEnd_2785454 : Nat := 476758914329616710704979

theorem tailTrace_2785454 : CollatzResearch.WordTrace tailWord_2785454 prefixEnd_2785454 476758914329616710704979 := by
  unfold tailWord_2785454
  simp only [CollatzResearch.WordTrace]
  refine ⟨12699231706347918814311427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67729235767188900342994277 12699231706347918814311427)
  ·
    refine ⟨19048847559521878221467141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12699231706347918814311427 19048847559521878221467141)
    ·
      refine ⟨3571658917410352166525089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19048847559521878221467141 3571658917410352166525089)
      ·
        refine ⟨2678744188057764124893817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3571658917410352166525089 2678744188057764124893817)
        ·
          refine ⟨2009058141043323093670363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2678744188057764124893817 2009058141043323093670363)
          ·
            refine ⟨3013587211564984640505545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009058141043323093670363 3013587211564984640505545)
            ·
              refine ⟨2260190408673738480379159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3013587211564984640505545 2260190408673738480379159)
              ·
                refine ⟨3390285613010607720568739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260190408673738480379159 3390285613010607720568739)
                ·
                  refine ⟨5085428419515911580853109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3390285613010607720568739 5085428419515911580853109)
                  ·
                    refine ⟨476758914329616710704979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5085428419515911580853109 476758914329616710704979)
                    ·
                      rfl

theorem cell23_2785454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2785454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785454 prefixEnd_2785454 := by exact prefixLift 2785454
  have htrace : WordTrace (prefixWord ++ tailWord_2785454) baseStart_2785454 baseEnd_2785454 := by
    simpa [prefixWord, tailWord_2785454, baseEnd_2785454] using wordTrace_append hprefix tailTrace_2785454
  have hstable : (prefixWord ++ tailWord_2785454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785454).length < 2 ^ (prefixWord ++ tailWord_2785454).sum := by decide
  have hdescent : baseEnd_2785454 < baseStart_2785454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785457 : List Nat := [1, 2, 2, 5, 3, 1, 2, 1, 1, 1, 4]
def baseStart_2785457 : Nat := 118140960795 + 2785457 * 2 ^ 59
def prefixEnd_2785457 : Nat := 4983230072969 + 3 ^ 40 * 2785457 * 2
def baseEnd_2785457 : Nat := 1430278283430813620377423

theorem tailTrace_2785457 : CollatzResearch.WordTrace tailWord_2785457 prefixEnd_2785457 1430278283430813620377423 := by
  unfold tailWord_2785457
  simp only [CollatzResearch.WordTrace]
  refine ⟨101593963069772482026850625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67729308713181654684567083 101593963069772482026850625)
  ·
    refine ⟨76195472302329361520137969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101593963069772482026850625 76195472302329361520137969)
    ·
      refine ⟨57146604226747021140103477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76195472302329361520137969 57146604226747021140103477)
      ·
        refine ⟨5357494146257533231884701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57146604226747021140103477 5357494146257533231884701)
        ·
          refine ⟨2009060304846574961956763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5357494146257533231884701 2009060304846574961956763)
          ·
            refine ⟨3013590457269862442935145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009060304846574961956763 3013590457269862442935145)
            ·
              refine ⟨2260192842952396832201359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3013590457269862442935145 2260192842952396832201359)
              ·
                refine ⟨3390289264428595248302039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260192842952396832201359 3390289264428595248302039)
                ·
                  refine ⟨5085433896642892872453059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3390289264428595248302039 5085433896642892872453059)
                  ·
                    refine ⟨7628150844964339308679589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5085433896642892872453059 7628150844964339308679589)
                    ·
                      refine ⟨1430278283430813620377423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7628150844964339308679589 1430278283430813620377423)
                      ·
                        rfl

theorem cell23_2785457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_2785457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785457 prefixEnd_2785457 := by exact prefixLift 2785457
  have htrace : WordTrace (prefixWord ++ tailWord_2785457) baseStart_2785457 baseEnd_2785457 := by
    simpa [prefixWord, tailWord_2785457, baseEnd_2785457] using wordTrace_append hprefix tailTrace_2785457
  have hstable : (prefixWord ++ tailWord_2785457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785457).length < 2 ^ (prefixWord ++ tailWord_2785457).sum := by decide
  have hdescent : baseEnd_2785457 < baseStart_2785457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785474 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_2785474 : Nat := 118140960795 + 2785474 * 2 ^ 59
def prefixEnd_2785474 : Nat := 4983230072969 + 3 ^ 40 * 2785474 * 2
def baseEnd_2785474 : Nat := 1430287012601940053864845

theorem tailTrace_2785474 : CollatzResearch.WordTrace tailWord_2785474 prefixEnd_2785474 1430287012601940053864845 := by
  unfold tailWord_2785474
  simp only [CollatzResearch.WordTrace]
  refine ⟨25398645777677723482554869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67729722073807262620146317 25398645777677723482554869)
  ·
    refine ⟨2381123041657286576489519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25398645777677723482554869 2381123041657286576489519)
    ·
      refine ⟨3571684562485929864734279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381123041657286576489519 3571684562485929864734279)
      ·
        refine ⟨5357526843728894797101419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3571684562485929864734279 5357526843728894797101419)
        ·
          refine ⟨8036290265593342195652129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5357526843728894797101419 8036290265593342195652129)
          ·
            refine ⟨6027217699195006646739097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8036290265593342195652129 6027217699195006646739097)
            ·
              refine ⟨4520413274396254985054323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6027217699195006646739097 4520413274396254985054323)
              ·
                refine ⟨6780619911594382477581485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4520413274396254985054323 6780619911594382477581485)
                ·
                  refine ⟨2542732466847893429093057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6780619911594382477581485 2542732466847893429093057)
                  ·
                    refine ⟨1907049350135920071819793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2542732466847893429093057 1907049350135920071819793)
                    ·
                      refine ⟨1430287012601940053864845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1907049350135920071819793 1430287012601940053864845)
                      ·
                        rfl

theorem cell23_2785474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_2785474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785474 prefixEnd_2785474 := by exact prefixLift 2785474
  have htrace : WordTrace (prefixWord ++ tailWord_2785474) baseStart_2785474 baseEnd_2785474 := by
    simpa [prefixWord, tailWord_2785474, baseEnd_2785474] using wordTrace_append hprefix tailTrace_2785474
  have hstable : (prefixWord ++ tailWord_2785474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785474).length < 2 ^ (prefixWord ++ tailWord_2785474).sum := by decide
  have hdescent : baseEnd_2785474 < baseStart_2785474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785489 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 2, 6]
def baseStart_2785489 : Nat := 118140960795 + 2785489 * 2 ^ 59
def prefixEnd_2785489 : Nat := 4983230072969 + 3 ^ 40 * 2785489 * 2
def baseEnd_2785489 : Nat := 476764904937252498392425

theorem tailTrace_2785489 : CollatzResearch.WordTrace tailWord_2785489 prefixEnd_2785489 476764904937252498392425 := by
  unfold tailWord_2785489
  simp only [CollatzResearch.WordTrace]
  refine ⟨101595130205656551492015521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67730086803771034328010347 101595130205656551492015521)
  ·
    refine ⟨76196347654242413619011641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101595130205656551492015521 76196347654242413619011641)
    ·
      refine ⟨57147260740681810214258731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76196347654242413619011641 57147260740681810214258731)
      ·
        refine ⟨85720891111022715321388097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57147260740681810214258731 85720891111022715321388097)
        ·
          refine ⟨64290668333267036491041073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85720891111022715321388097 64290668333267036491041073)
          ·
            refine ⟨48218001249950277368280805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64290668333267036491041073 48218001249950277368280805)
            ·
              refine ⟨9040875234365677006552651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48218001249950277368280805 9040875234365677006552651)
              ·
                refine ⟨13561312851548515509828977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9040875234365677006552651 13561312851548515509828977)
                ·
                  refine ⟨10170984638661386632371733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13561312851548515509828977 10170984638661386632371733)
                  ·
                    refine ⟨476764904937252498392425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10170984638661386632371733 476764904937252498392425)
                    ·
                      rfl

theorem cell23_2785489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_2785489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785489 prefixEnd_2785489 := by exact prefixLift 2785489
  have htrace : WordTrace (prefixWord ++ tailWord_2785489) baseStart_2785489 baseEnd_2785489 := by
    simpa [prefixWord, tailWord_2785489, baseEnd_2785489] using wordTrace_append hprefix tailTrace_2785489
  have hstable : (prefixWord ++ tailWord_2785489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785489).length < 2 ^ (prefixWord ++ tailWord_2785489).sum := by decide
  have hdescent : baseEnd_2785489 < baseStart_2785489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785499 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 3]
def baseStart_2785499 : Nat := 118140960795 + 2785499 * 2 ^ 59
def prefixEnd_2785499 : Nat := 4983230072969 + 3 ^ 40 * 2785499 * 2
def baseEnd_2785499 : Nat := 1430299849618302456052229

theorem tailTrace_2785499 : CollatzResearch.WordTrace tailWord_2785499 prefixEnd_2785499 1430299849618302456052229 := by
  unfold tailWord_2785499
  simp only [CollatzResearch.WordTrace]
  refine ⟨101595494935620323199879551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67730329957080215466586367 101595494935620323199879551)
  ·
    refine ⟨152393242403430484799819327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101595494935620323199879551 152393242403430484799819327)
    ·
      refine ⟨228589863605145727199728991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152393242403430484799819327 228589863605145727199728991)
      ·
        refine ⟨342884795407718590799593487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228589863605145727199728991 342884795407718590799593487)
        ·
          refine ⟨514327193111577886199390231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342884795407718590799593487 514327193111577886199390231)
          ·
            refine ⟨771490789667366829299085347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514327193111577886199390231 771490789667366829299085347)
            ·
              refine ⟨1157236184501050243948628021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771490789667366829299085347 1157236184501050243948628021)
              ·
                refine ⟨108490892296973460370183877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1157236184501050243948628021 108490892296973460370183877)
                ·
                  refine ⟨20342042305682523819409477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108490892296973460370183877 20342042305682523819409477)
                  ·
                    refine ⟨3814132932315473216139277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20342042305682523819409477 3814132932315473216139277)
                    ·
                      refine ⟨1430299849618302456052229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3814132932315473216139277 1430299849618302456052229)
                      ·
                        rfl

theorem cell23_2785499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 3].length) (baseStart_2785499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785499 prefixEnd_2785499 := by exact prefixLift 2785499
  have htrace : WordTrace (prefixWord ++ tailWord_2785499) baseStart_2785499 baseEnd_2785499 := by
    simpa [prefixWord, tailWord_2785499, baseEnd_2785499] using wordTrace_append hprefix tailTrace_2785499
  have hstable : (prefixWord ++ tailWord_2785499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785499).length < 2 ^ (prefixWord ++ tailWord_2785499).sum := by decide
  have hdescent : baseEnd_2785499 < baseStart_2785499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785526 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_2785526 : Nat := 118140960795 + 2785526 * 2 ^ 59
def prefixEnd_2785526 : Nat := 4983230072969 + 3 ^ 40 * 2785526 * 2
def baseEnd_2785526 : Nat := 1430313713595973850414605

theorem tailTrace_2785526 : CollatzResearch.WordTrace tailWord_2785526 prefixEnd_2785526 1430313713595973850414605 := by
  unfold tailWord_2785526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6349779981657656675694527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67730986471015004540741621 6349779981657656675694527)
  ·
    refine ⟨9524669972486485013541791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6349779981657656675694527 9524669972486485013541791)
    ·
      refine ⟨14287004958729727520312687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9524669972486485013541791 14287004958729727520312687)
      ·
        refine ⟨21430507438094591280469031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14287004958729727520312687 21430507438094591280469031)
        ·
          refine ⟨32145761157141886920703547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21430507438094591280469031 32145761157141886920703547)
          ·
            refine ⟨48218641735712830381055321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32145761157141886920703547 48218641735712830381055321)
            ·
              refine ⟨36163981301784622785791491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48218641735712830381055321 36163981301784622785791491)
              ·
                refine ⟨54245971952676934178687237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36163981301784622785791491 54245971952676934178687237)
                ·
                  refine ⟨10171119741126925158503857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54245971952676934178687237 10171119741126925158503857)
                  ·
                    refine ⟨7628339805845193868877893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10171119741126925158503857 7628339805845193868877893)
                    ·
                      refine ⟨1430313713595973850414605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7628339805845193868877893 1430313713595973850414605)
                      ·
                        rfl

theorem cell23_2785526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_2785526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785526 prefixEnd_2785526 := by exact prefixLift 2785526
  have htrace : WordTrace (prefixWord ++ tailWord_2785526) baseStart_2785526 baseEnd_2785526 := by
    simpa [prefixWord, tailWord_2785526, baseEnd_2785526] using wordTrace_append hprefix tailTrace_2785526
  have hstable : (prefixWord ++ tailWord_2785526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785526).length < 2 ^ (prefixWord ++ tailWord_2785526).sum := by decide
  have hdescent : baseEnd_2785526 < baseStart_2785526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785536 : List Nat := [2, 1, 1, 2, 1, 1, 4, 6, 5]
def baseStart_2785536 : Nat := 118140960795 + 2785536 * 2 ^ 59
def prefixEnd_2785536 : Nat := 4983230072969 + 3 ^ 40 * 2785536 * 2
def baseEnd_2785536 : Nat := 158924316489168756809951

theorem tailTrace_2785536 : CollatzResearch.WordTrace tailWord_2785536 prefixEnd_2785536 158924316489168756809951 := by
  unfold tailWord_2785536
  simp only [CollatzResearch.WordTrace]
  refine ⟨50798422218243139259488231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67731229624324185679317641 50798422218243139259488231)
  ·
    refine ⟨76197633327364708889232347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50798422218243139259488231 76197633327364708889232347)
    ·
      refine ⟨114296449991047063333848521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76197633327364708889232347 114296449991047063333848521)
      ·
        refine ⟨85722337493285297500386391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114296449991047063333848521 85722337493285297500386391)
        ·
          refine ⟨128583506239927946250579587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85722337493285297500386391 128583506239927946250579587)
          ·
            refine ⟨192875259359891919375869381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128583506239927946250579587 192875259359891919375869381)
            ·
              refine ⟨36164111129979734882975509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192875259359891919375869381 36164111129979734882975509)
              ·
                refine ⟨1695192709217800072639477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36164111129979734882975509 1695192709217800072639477)
                ·
                  refine ⟨158924316489168756809951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1695192709217800072639477 158924316489168756809951)
                  ·
                    rfl

theorem cell23_2785536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 5].length) (baseStart_2785536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785536 prefixEnd_2785536 := by exact prefixLift 2785536
  have htrace : WordTrace (prefixWord ++ tailWord_2785536) baseStart_2785536 baseEnd_2785536 := by
    simpa [prefixWord, tailWord_2785536, baseEnd_2785536] using wordTrace_append hprefix tailTrace_2785536
  have hstable : (prefixWord ++ tailWord_2785536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785536).length < 2 ^ (prefixWord ++ tailWord_2785536).sum := by decide
  have hdescent : baseEnd_2785536 < baseStart_2785536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785546 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3]
def baseStart_2785546 : Nat := 118140960795 + 2785546 * 2 ^ 59
def prefixEnd_2785546 : Nat := 4983230072969 + 3 ^ 40 * 2785546 * 2
def baseEnd_2785546 : Nat := 1430323983209063772164513

theorem tailTrace_2785546 : CollatzResearch.WordTrace tailWord_2785546 prefixEnd_2785546 1430323983209063772164513 := by
  unfold tailWord_2785546
  simp only [CollatzResearch.WordTrace]
  refine ⟨25399302291612512556710123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67731472777633366817893661 25399302291612512556710123)
  ·
    refine ⟨38098953437418768835065185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25399302291612512556710123 38098953437418768835065185)
    ·
      refine ⟨28574215078064076626298889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38098953437418768835065185 28574215078064076626298889)
      ·
        refine ⟨21430661308548057469724167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28574215078064076626298889 21430661308548057469724167)
        ·
          refine ⟨32145991962822086204586251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21430661308548057469724167 32145991962822086204586251)
          ·
            refine ⟨48218987944233129306879377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32145991962822086204586251 48218987944233129306879377)
            ·
              refine ⟨36164240958174846980159533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48218987944233129306879377 36164240958174846980159533)
              ·
                refine ⟨13561590359315567617559825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36164240958174846980159533 13561590359315567617559825)
                ·
                  refine ⟨10171192769486675713169869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13561590359315567617559825 10171192769486675713169869)
                  ·
                    refine ⟨3814197288557503392438701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10171192769486675713169869 3814197288557503392438701)
                    ·
                      refine ⟨1430323983209063772164513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3814197288557503392438701 1430323983209063772164513)
                      ·
                        rfl

theorem cell23_2785546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_2785546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785546 prefixEnd_2785546 := by exact prefixLift 2785546
  have htrace : WordTrace (prefixWord ++ tailWord_2785546) baseStart_2785546 baseEnd_2785546 := by
    simpa [prefixWord, tailWord_2785546, baseEnd_2785546] using wordTrace_append hprefix tailTrace_2785546
  have hstable : (prefixWord ++ tailWord_2785546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785546).length < 2 ^ (prefixWord ++ tailWord_2785546).sum := by decide
  have hdescent : baseEnd_2785546 < baseStart_2785546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785609 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 10]
def baseStart_2785609 : Nat := 118140960795 + 2785609 * 2 ^ 59
def prefixEnd_2785609 : Nat := 4983230072969 + 3 ^ 40 * 2785609 * 2
def baseEnd_2785609 : Nat := 158928481387810780630747

theorem tailTrace_2785609 : CollatzResearch.WordTrace tailWord_2785609 prefixEnd_2785609 158928481387810780630747 := by
  unfold tailWord_2785609
  simp only [CollatzResearch.WordTrace]
  refine ⟨101599506965221811986383881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67733004643481207990922587 101599506965221811986383881)
  ·
    refine ⟨76199630223916358989787911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101599506965221811986383881 76199630223916358989787911)
    ·
      refine ⟨114299445335874538484681867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76199630223916358989787911 114299445335874538484681867)
      ·
        refine ⟨171449168003811807727022801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114299445335874538484681867 171449168003811807727022801)
        ·
          refine ⟨128586876002858855795267101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171449168003811807727022801 128586876002858855795267101)
          ·
            refine ⟨48220078501072070923225163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128586876002858855795267101 48220078501072070923225163)
            ·
              refine ⟨72330117751608106384837745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48220078501072070923225163 72330117751608106384837745)
              ·
                refine ⟨54247588313706079788628309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72330117751608106384837745 54247588313706079788628309)
                ·
                  refine ⟨158928481387810780630747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 54247588313706079788628309 158928481387810780630747)
                  ·
                    rfl

theorem cell23_2785609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 10].length) (baseStart_2785609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785609 prefixEnd_2785609 := by exact prefixLift 2785609
  have htrace : WordTrace (prefixWord ++ tailWord_2785609) baseStart_2785609 baseEnd_2785609 := by
    simpa [prefixWord, tailWord_2785609, baseEnd_2785609] using wordTrace_append hprefix tailTrace_2785609
  have hstable : (prefixWord ++ tailWord_2785609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785609).length < 2 ^ (prefixWord ++ tailWord_2785609).sum := by decide
  have hdescent : baseEnd_2785609 < baseStart_2785609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785620 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_2785620 : Nat := 118140960795 + 2785620 * 2 ^ 59
def prefixEnd_2785620 : Nat := 4983230072969 + 3 ^ 40 * 2785620 * 2
def baseEnd_2785620 : Nat := 1430361980777496482639173

theorem tailTrace_2785620 : CollatzResearch.WordTrace tailWord_2785620 prefixEnd_2785620 1430361980777496482639173 := by
  unfold tailWord_2785620
  simp only [CollatzResearch.WordTrace]
  refine ⟨50799954084090980432517157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67733272112121307243356209 50799954084090980432517157)
  ·
    refine ⟨9524991390767058831096967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50799954084090980432517157 9524991390767058831096967)
    ·
      refine ⟨14287487086150588246645451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9524991390767058831096967 14287487086150588246645451)
      ·
        refine ⟨21431230629225882369968177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14287487086150588246645451 21431230629225882369968177)
        ·
          refine ⟨16073422971919411777476133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21431230629225882369968177 16073422971919411777476133)
          ·
            refine ⟨3013766807234889708276775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16073422971919411777476133 3013766807234889708276775)
            ·
              refine ⟨4520650210852334562415163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3013766807234889708276775 4520650210852334562415163)
              ·
                refine ⟨6780975316278501843622745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4520650210852334562415163 6780975316278501843622745)
                ·
                  refine ⟨5085731487208876382717059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6780975316278501843622745 5085731487208876382717059)
                  ·
                    refine ⟨7628597230813314574075589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5085731487208876382717059 7628597230813314574075589)
                    ·
                      refine ⟨1430361980777496482639173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7628597230813314574075589 1430361980777496482639173)
                      ·
                        rfl

theorem cell23_2785620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_2785620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785620 prefixEnd_2785620 := by exact prefixLift 2785620
  have htrace : WordTrace (prefixWord ++ tailWord_2785620) baseStart_2785620 baseEnd_2785620 := by
    simpa [prefixWord, tailWord_2785620, baseEnd_2785620] using wordTrace_append hprefix tailTrace_2785620
  have hstable : (prefixWord ++ tailWord_2785620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785620).length < 2 ^ (prefixWord ++ tailWord_2785620).sum := by decide
  have hdescent : baseEnd_2785620 < baseStart_2785620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785663 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 4, 3, 2]
def baseStart_2785663 : Nat := 118140960795 + 2785663 * 2 ^ 59
def prefixEnd_2785663 : Nat := 4983230072969 + 3 ^ 40 * 2785663 * 2
def baseEnd_2785663 : Nat := 1430384060445639814401475

theorem tailTrace_2785663 : CollatzResearch.WordTrace tailWord_2785663 prefixEnd_2785663 1430384060445639814401475 := by
  unfold tailWord_2785663
  simp only [CollatzResearch.WordTrace]
  refine ⟨101601476507026179208849643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67734317671350786139233095 101601476507026179208849643)
  ·
    refine ⟨152402214760539268813274465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101601476507026179208849643 152402214760539268813274465)
    ·
      refine ⟨114301661070404451609955849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152402214760539268813274465 114301661070404451609955849)
      ·
        refine ⟨85726245802803338707466887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114301661070404451609955849 85726245802803338707466887)
        ·
          refine ⟨128589368704205008061200331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85726245802803338707466887 128589368704205008061200331)
          ·
            refine ⟨192884053056307512091800497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128589368704205008061200331 192884053056307512091800497)
            ·
              refine ⟨144663039792230634068850373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192884053056307512091800497 144663039792230634068850373)
              ·
                refine ⟨27124319961043243887909445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144663039792230634068850373 27124319961043243887909445)
                ·
                  refine ⟨5085809992695608228983021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27124319961043243887909445 5085809992695608228983021)
                  ·
                    refine ⟨1907178747260853085868633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5085809992695608228983021 1907178747260853085868633)
                    ·
                      refine ⟨1430384060445639814401475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1907178747260853085868633 1430384060445639814401475)
                      ·
                        rfl

theorem cell23_2785663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 3, 2].length) (baseStart_2785663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785663 prefixEnd_2785663 := by exact prefixLift 2785663
  have htrace : WordTrace (prefixWord ++ tailWord_2785663) baseStart_2785663 baseEnd_2785663 := by
    simpa [prefixWord, tailWord_2785663, baseEnd_2785663] using wordTrace_append hprefix tailTrace_2785663
  have hstable : (prefixWord ++ tailWord_2785663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785663).length < 2 ^ (prefixWord ++ tailWord_2785663).sum := by decide
  have hdescent : baseEnd_2785663 < baseStart_2785663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785673 : List Nat := [1, 2, 1, 1, 6, 1, 1, 4, 1, 5]
def baseStart_2785673 : Nat := 118140960795 + 2785673 * 2 ^ 59
def prefixEnd_2785673 : Nat := 4983230072969 + 3 ^ 40 * 2785673 * 2
def baseEnd_2785673 : Nat := 476796398417394925092143

theorem tailTrace_2785673 : CollatzResearch.WordTrace tailWord_2785673 prefixEnd_2785673 476796398417394925092143 := by
  unfold tailWord_2785673
  simp only [CollatzResearch.WordTrace]
  refine ⟨101601841236989950916713673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67734560824659967277809115 101601841236989950916713673)
  ·
    refine ⟨76201380927742463187535255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101601841236989950916713673 76201380927742463187535255)
    ·
      refine ⟨114302071391613694781302883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76201380927742463187535255 114302071391613694781302883)
      ·
        refine ⟨171453107087420542171954325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114302071391613694781302883 171453107087420542171954325)
        ·
          refine ⟨8036864394722837914310359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 171453107087420542171954325 8036864394722837914310359)
          ·
            refine ⟨12055296592084256871465539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8036864394722837914310359 12055296592084256871465539)
            ·
              refine ⟨18082944888126385307198309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12055296592084256871465539 18082944888126385307198309)
              ·
                refine ⟨3390552166523697245099683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18082944888126385307198309 3390552166523697245099683)
                ·
                  refine ⟨5085828249785545867649525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3390552166523697245099683 5085828249785545867649525)
                  ·
                    refine ⟨476796398417394925092143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5085828249785545867649525 476796398417394925092143)
                    ·
                      rfl

theorem cell23_2785673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 5].length) (baseStart_2785673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785673 prefixEnd_2785673 := by exact prefixLift 2785673
  have htrace : WordTrace (prefixWord ++ tailWord_2785673) baseStart_2785673 baseEnd_2785673 := by
    simpa [prefixWord, tailWord_2785673, baseEnd_2785673] using wordTrace_append hprefix tailTrace_2785673
  have hstable : (prefixWord ++ tailWord_2785673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785673).length < 2 ^ (prefixWord ++ tailWord_2785673).sum := by decide
  have hdescent : baseEnd_2785673 < baseStart_2785673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785687 : List Nat := [1, 1, 3, 3, 1, 1, 5, 3, 1, 1, 3]
def baseStart_2785687 : Nat := 118140960795 + 2785687 * 2 ^ 59
def prefixEnd_2785687 : Nat := 4983230072969 + 3 ^ 40 * 2785687 * 2
def baseEnd_2785687 : Nat := 1430396383981347720501365

theorem tailTrace_2785687 : CollatzResearch.WordTrace tailWord_2785687 prefixEnd_2785687 1430396383981347720501365 := by
  unfold tailWord_2785687
  simp only [CollatzResearch.WordTrace]
  refine ⟨101602351858939231307723315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67734901239292820871815543 101602351858939231307723315)
  ·
    refine ⟨152403527788408846961584973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101602351858939231307723315 152403527788408846961584973)
    ·
      refine ⟨57151322920653317610594365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152403527788408846961584973 57151322920653317610594365)
      ·
        refine ⟨21431746095244994103972887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57151322920653317610594365 21431746095244994103972887)
        ·
          refine ⟨32147619142867491155959331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21431746095244994103972887 32147619142867491155959331)
          ·
            refine ⟨48221428714301236733938997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32147619142867491155959331 48221428714301236733938997)
            ·
              refine ⟨4520758941965740943806781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48221428714301236733938997 4520758941965740943806781)
              ·
                refine ⟨1695284603237152853927543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4520758941965740943806781 1695284603237152853927543)
                ·
                  refine ⟨2542926904855729280891315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1695284603237152853927543 2542926904855729280891315)
                  ·
                    refine ⟨3814390357283593921336973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2542926904855729280891315 3814390357283593921336973)
                    ·
                      refine ⟨1430396383981347720501365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3814390357283593921336973 1430396383981347720501365)
                      ·
                        rfl

theorem cell23_2785687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_2785687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785687 prefixEnd_2785687 := by exact prefixLift 2785687
  have htrace : WordTrace (prefixWord ++ tailWord_2785687) baseStart_2785687 baseEnd_2785687 := by
    simpa [prefixWord, tailWord_2785687, baseEnd_2785687] using wordTrace_append hprefix tailTrace_2785687
  have hstable : (prefixWord ++ tailWord_2785687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785687).length < 2 ^ (prefixWord ++ tailWord_2785687).sum := by decide
  have hdescent : baseEnd_2785687 < baseStart_2785687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785704 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_2785704 : Nat := 118140960795 + 2785704 * 2 ^ 59
def prefixEnd_2785704 : Nat := 4983230072969 + 3 ^ 40 * 2785704 * 2
def baseEnd_2785704 : Nat := 1430405113152474153988787

theorem tailTrace_2785704 : CollatzResearch.WordTrace tailWord_2785704 prefixEnd_2785704 1430405113152474153988787 := by
  unfold tailWord_2785704
  simp only [CollatzResearch.WordTrace]
  refine ⟨50801485949938821605546083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67735314599918428807394777 50801485949938821605546083)
  ·
    refine ⟨76202228924908232408319125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50801485949938821605546083 76202228924908232408319125)
    ·
      refine ⟨3571979480855073394139959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76202228924908232408319125 3571979480855073394139959)
      ·
        refine ⟨5357969221282610091209939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3571979480855073394139959 5357969221282610091209939)
        ·
          refine ⟨8036953831923915136814909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5357969221282610091209939 8036953831923915136814909)
          ·
            refine ⟨3013857686971468176305591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8036953831923915136814909 3013857686971468176305591)
            ·
              refine ⟨4520786530457202264458387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3013857686971468176305591 4520786530457202264458387)
              ·
                refine ⟨6781179795685803396687581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4520786530457202264458387 6781179795685803396687581)
                ·
                  refine ⟨2542942423382176273757843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6781179795685803396687581 2542942423382176273757843)
                  ·
                    refine ⟨3814413635073264410636765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2542942423382176273757843 3814413635073264410636765)
                    ·
                      refine ⟨1430405113152474153988787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3814413635073264410636765 1430405113152474153988787)
                      ·
                        rfl

theorem cell23_2785704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_2785704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785704 prefixEnd_2785704 := by exact prefixLift 2785704
  have htrace : WordTrace (prefixWord ++ tailWord_2785704) baseStart_2785704 baseEnd_2785704 := by
    simpa [prefixWord, tailWord_2785704, baseEnd_2785704] using wordTrace_append hprefix tailTrace_2785704
  have hstable : (prefixWord ++ tailWord_2785704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785704).length < 2 ^ (prefixWord ++ tailWord_2785704).sum := by decide
  have hdescent : baseEnd_2785704 < baseStart_2785704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785713 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 1, 1, 5]
def baseStart_2785713 : Nat := 118140960795 + 2785713 * 2 ^ 59
def prefixEnd_2785713 : Nat := 4983230072969 + 3 ^ 40 * 2785713 * 2
def baseEnd_2785713 : Nat := 1430409734478364618776245

theorem tailTrace_2785713 : CollatzResearch.WordTrace tailWord_2785713 prefixEnd_2785713 1430409734478364618776245 := by
  unfold tailWord_2785713
  simp only [CollatzResearch.WordTrace]
  refine ⟨101603300156845037748169793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67735533437896691832113195 101603300156845037748169793)
  ·
    refine ⟨76202475117633778311127345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101603300156845037748169793 76202475117633778311127345)
    ·
      refine ⟨57151856338225333733345509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76202475117633778311127345 57151856338225333733345509)
      ·
        refine ⟨10715973063417250075002283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57151856338225333733345509 10715973063417250075002283)
        ·
          refine ⟨16073959595125875112503425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10715973063417250075002283 16073959595125875112503425)
          ·
            refine ⟨12055469696344406334377569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16073959595125875112503425 12055469696344406334377569)
            ·
              refine ⟨9041602272258304750783177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12055469696344406334377569 9041602272258304750783177)
              ·
                refine ⟨6781201704193728563087383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9041602272258304750783177 6781201704193728563087383)
                ·
                  refine ⟨10171802556290592844631075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6781201704193728563087383 10171802556290592844631075)
                  ·
                    refine ⟨15257703834435889266946613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10171802556290592844631075 15257703834435889266946613)
                    ·
                      refine ⟨1430409734478364618776245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15257703834435889266946613 1430409734478364618776245)
                      ·
                        rfl

theorem cell23_2785713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_2785713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785713 prefixEnd_2785713 := by exact prefixLift 2785713
  have htrace : WordTrace (prefixWord ++ tailWord_2785713) baseStart_2785713 baseEnd_2785713 := by
    simpa [prefixWord, tailWord_2785713, baseEnd_2785713] using wordTrace_append hprefix tailTrace_2785713
  have hstable : (prefixWord ++ tailWord_2785713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785713).length < 2 ^ (prefixWord ++ tailWord_2785713).sum := by decide
  have hdescent : baseEnd_2785713 < baseStart_2785713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785740 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 1, 2, 4]
def baseStart_2785740 : Nat := 118140960795 + 2785740 * 2 ^ 59
def prefixEnd_2785740 : Nat := 4983230072969 + 3 ^ 40 * 2785740 * 2
def baseEnd_2785740 : Nat := 1430423598456036013138621

theorem tailTrace_2785740 : CollatzResearch.WordTrace tailWord_2785740 prefixEnd_2785740 1430423598456036013138621 := by
  unfold tailWord_2785740
  simp only [CollatzResearch.WordTrace]
  refine ⟨50802142463873610679701337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67736189951831480906268449 50802142463873610679701337)
  ·
    refine ⟨38101606847905208009776003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50802142463873610679701337 38101606847905208009776003)
    ·
      refine ⟨57152410271857812014664005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38101606847905208009776003 57152410271857812014664005)
      ·
        refine ⟨10716076925973339752749501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57152410271857812014664005 10716076925973339752749501)
        ·
          refine ⟨4018528847240002407281063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10716076925973339752749501 4018528847240002407281063)
          ·
            refine ⟨6027793270860003610921595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4018528847240002407281063 6027793270860003610921595)
            ·
              refine ⟨9041689906290005416382393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6027793270860003610921595 9041689906290005416382393)
              ·
                refine ⟨6781267429717504062286795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9041689906290005416382393 6781267429717504062286795)
                ·
                  refine ⟨10171901144576256093430193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6781267429717504062286795 10171901144576256093430193)
                  ·
                    refine ⟨7628925858432192070072645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10171901144576256093430193 7628925858432192070072645)
                    ·
                      refine ⟨1430423598456036013138621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7628925858432192070072645 1430423598456036013138621)
                      ·
                        rfl

theorem cell23_2785740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_2785740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785740 prefixEnd_2785740 := by exact prefixLift 2785740
  have htrace : WordTrace (prefixWord ++ tailWord_2785740) baseStart_2785740 baseEnd_2785740 := by
    simpa [prefixWord, tailWord_2785740, baseEnd_2785740] using wordTrace_append hprefix tailTrace_2785740
  have hstable : (prefixWord ++ tailWord_2785740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785740).length < 2 ^ (prefixWord ++ tailWord_2785740).sum := by decide
  have hdescent : baseEnd_2785740 < baseStart_2785740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785798 : List Nat := [6, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_2785798 : Nat := 118140960795 + 2785798 * 2 ^ 59
def prefixEnd_2785798 : Nat := 4983230072969 + 3 ^ 40 * 2785798 * 2
def baseEnd_2785798 : Nat := 1430453380333996786213355

theorem tailTrace_2785798 : CollatzResearch.WordTrace tailWord_2785798 prefixEnd_2785798 1430453380333996786213355 := by
  unfold tailWord_2785798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3175200011298034289531689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67737600241024731510009365 3175200011298034289531689)
  ·
    refine ⟨2381400008473525717148767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3175200011298034289531689 2381400008473525717148767)
    ·
      refine ⟨3572100012710288575723151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381400008473525717148767 3572100012710288575723151)
      ·
        refine ⟨5358150019065432863584727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3572100012710288575723151 5358150019065432863584727)
        ·
          refine ⟨8037225028598149295377091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5358150019065432863584727 8037225028598149295377091)
          ·
            refine ⟨12055837542897223943065637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8037225028598149295377091 12055837542897223943065637)
            ·
              refine ⟨2260469539293229489324807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12055837542897223943065637 2260469539293229489324807)
              ·
                refine ⟨3390704308939844233987211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260469539293229489324807 3390704308939844233987211)
                ·
                  refine ⟨5086056463409766350980817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3390704308939844233987211 5086056463409766350980817)
                  ·
                    refine ⟨3814542347557324763235613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5086056463409766350980817 3814542347557324763235613)
                    ·
                      refine ⟨1430453380333996786213355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3814542347557324763235613 1430453380333996786213355)
                      ·
                        rfl

theorem cell23_2785798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_2785798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785798 prefixEnd_2785798 := by exact prefixLift 2785798
  have htrace : WordTrace (prefixWord ++ tailWord_2785798) baseStart_2785798 baseEnd_2785798 := by
    simpa [prefixWord, tailWord_2785798, baseEnd_2785798] using wordTrace_append hprefix tailTrace_2785798
  have hstable : (prefixWord ++ tailWord_2785798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785798).length < 2 ^ (prefixWord ++ tailWord_2785798).sum := by decide
  have hdescent : baseEnd_2785798 < baseStart_2785798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785804 : List Nat := [2, 2, 1, 2, 4, 1, 4, 1, 1, 3, 2]
def baseStart_2785804 : Nat := 118140960795 + 2785804 * 2 ^ 59
def prefixEnd_2785804 : Nat := 4983230072969 + 3 ^ 40 * 2785804 * 2
def baseEnd_2785804 : Nat := 1430456461217923762738327

theorem tailTrace_2785804 : CollatzResearch.WordTrace tailWord_2785804 prefixEnd_2785804 1430456461217923762738327 := by
  unfold tailWord_2785804
  simp only [CollatzResearch.WordTrace]
  refine ⟨50803309599757680144866233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67737746133010240193154977 50803309599757680144866233)
  ·
    refine ⟨38102482199818260108649675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50803309599757680144866233 38102482199818260108649675)
    ·
      refine ⟨57153723299727390162974513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38102482199818260108649675 57153723299727390162974513)
      ·
        refine ⟨42865292474795542622230885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57153723299727390162974513 42865292474795542622230885)
        ·
          refine ⟨8037242339024164241668291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42865292474795542622230885 8037242339024164241668291)
          ·
            refine ⟨12055863508536246362502437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8037242339024164241668291 12055863508536246362502437)
            ·
              refine ⟨2260474407850546192969207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12055863508536246362502437 2260474407850546192969207)
              ·
                refine ⟨3390711611775819289453811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260474407850546192969207 3390711611775819289453811)
                ·
                  refine ⟨5086067417663728934180717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3390711611775819289453811 5086067417663728934180717)
                  ·
                    refine ⟨1907275281623898350317769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5086067417663728934180717 1907275281623898350317769)
                    ·
                      refine ⟨1430456461217923762738327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1907275281623898350317769 1430456461217923762738327)
                      ·
                        rfl

theorem cell23_2785804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_2785804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785804 prefixEnd_2785804 := by exact prefixLift 2785804
  have htrace : WordTrace (prefixWord ++ tailWord_2785804) baseStart_2785804 baseEnd_2785804 := by
    simpa [prefixWord, tailWord_2785804, baseEnd_2785804] using wordTrace_append hprefix tailTrace_2785804
  have hstable : (prefixWord ++ tailWord_2785804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785804).length < 2 ^ (prefixWord ++ tailWord_2785804).sum := by decide
  have hdescent : baseEnd_2785804 < baseStart_2785804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785813 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_2785813 : Nat := 118140960795 + 2785813 * 2 ^ 59
def prefixEnd_2785813 : Nat := 4983230072969 + 3 ^ 40 * 2785813 * 2
def baseEnd_2785813 : Nat := 1430461082543814227525785

theorem tailTrace_2785813 : CollatzResearch.WordTrace tailWord_2785813 prefixEnd_2785813 1430461082543814227525785 := by
  unfold tailWord_2785813
  simp only [CollatzResearch.WordTrace]
  refine ⟨101606947456482754826810093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67737964970988503217873395 101606947456482754826810093)
  ·
    refine ⟨38102605296181033060053785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101606947456482754826810093 38102605296181033060053785)
    ·
      refine ⟨28576953972135774795040339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38102605296181033060053785 28576953972135774795040339)
      ·
        refine ⟨42865430958203662192560509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28576953972135774795040339 42865430958203662192560509)
        ·
          refine ⟨16074536609326373322210191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42865430958203662192560509 16074536609326373322210191)
          ·
            refine ⟨24111804913989559983315287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16074536609326373322210191 24111804913989559983315287)
            ·
              refine ⟨36167707370984339974972931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24111804913989559983315287 36167707370984339974972931)
              ·
                refine ⟨54251561056476509962459397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36167707370984339974972931 54251561056476509962459397)
                ·
                  refine ⟨10172167698089345617961137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54251561056476509962459397 10172167698089345617961137)
                  ·
                    refine ⟨7629125773567009213470853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10172167698089345617961137 7629125773567009213470853)
                    ·
                      refine ⟨1430461082543814227525785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7629125773567009213470853 1430461082543814227525785)
                      ·
                        rfl

theorem cell23_2785813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_2785813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785813 prefixEnd_2785813 := by exact prefixLift 2785813
  have htrace : WordTrace (prefixWord ++ tailWord_2785813) baseStart_2785813 baseEnd_2785813 := by
    simpa [prefixWord, tailWord_2785813, baseEnd_2785813] using wordTrace_append hprefix tailTrace_2785813
  have hstable : (prefixWord ++ tailWord_2785813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785813).length < 2 ^ (prefixWord ++ tailWord_2785813).sum := by decide
  have hdescent : baseEnd_2785813 < baseStart_2785813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785834 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_2785834 : Nat := 118140960795 + 2785834 * 2 ^ 59
def prefixEnd_2785834 : Nat := 4983230072969 + 3 ^ 40 * 2785834 * 2
def baseEnd_2785834 : Nat := 1430471865637558645363189

theorem tailTrace_2785834 : CollatzResearch.WordTrace tailWord_2785834 prefixEnd_2785834 1430471865637558645363189 := by
  unfold tailWord_2785834
  simp only [CollatzResearch.WordTrace]
  refine ⟨25401928347351668853331139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67738475592937783608883037 25401928347351668853331139)
  ·
    refine ⟨38102892521027503279996709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25401928347351668853331139 38102892521027503279996709)
    ·
      refine ⟨7144292347692656864999383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38102892521027503279996709 7144292347692656864999383)
      ·
        refine ⟨10716438521538985297499075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7144292347692656864999383 10716438521538985297499075)
        ·
          refine ⟨16074657782308477946248613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10716438521538985297499075 16074657782308477946248613)
          ·
            refine ⟨3013998334182839614921615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16074657782308477946248613 3013998334182839614921615)
            ·
              refine ⟨4520997501274259422382423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3013998334182839614921615 4520997501274259422382423)
              ·
                refine ⟨6781496251911389133573635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4520997501274259422382423 6781496251911389133573635)
                ·
                  refine ⟨10172244377867083700360453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6781496251911389133573635 10172244377867083700360453)
                  ·
                    refine ⟨1907295820850078193817585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10172244377867083700360453 1907295820850078193817585)
                    ·
                      refine ⟨1430471865637558645363189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1907295820850078193817585 1430471865637558645363189)
                      ·
                        rfl

theorem cell23_2785834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_2785834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785834 prefixEnd_2785834 := by exact prefixLift 2785834
  have htrace : WordTrace (prefixWord ++ tailWord_2785834) baseStart_2785834 baseEnd_2785834 := by
    simpa [prefixWord, tailWord_2785834, baseEnd_2785834] using wordTrace_append hprefix tailTrace_2785834
  have hstable : (prefixWord ++ tailWord_2785834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785834).length < 2 ^ (prefixWord ++ tailWord_2785834).sum := by decide
  have hdescent : baseEnd_2785834 < baseStart_2785834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785857 : List Nat := [1, 2, 5, 1, 1, 2, 3, 3, 5]
def baseStart_2785857 : Nat := 118140960795 + 2785857 * 2 ^ 59
def prefixEnd_2785857 : Nat := 4983230072969 + 3 ^ 40 * 2785857 * 2
def baseEnd_2785857 : Nat := 158942630632512450597287

theorem tailTrace_2785857 : CollatzResearch.WordTrace tailWord_2785857 prefixEnd_2785857 158942630632512450597287 := by
  unfold tailWord_2785857
  simp only [CollatzResearch.WordTrace]
  refine ⟨101608552268323350341411825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67739034845548900227607883 101608552268323350341411825)
  ·
    refine ⟨76206414201242512756058869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101608552268323350341411825 76206414201242512756058869)
    ·
      refine ⟨7144351331366485570880519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76206414201242512756058869 7144351331366485570880519)
      ·
        refine ⟨10716526997049728356320779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7144351331366485570880519 10716526997049728356320779)
        ·
          refine ⟨16074790495574592534481169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10716526997049728356320779 16074790495574592534481169)
          ·
            refine ⟨12056092871680944400860877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16074790495574592534481169 12056092871680944400860877)
            ·
              refine ⟨4521034826880354150322829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12056092871680944400860877 4521034826880354150322829)
              ·
                refine ⟨1695388060080132806371061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4521034826880354150322829 1695388060080132806371061)
                ·
                  refine ⟨158942630632512450597287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1695388060080132806371061 158942630632512450597287)
                  ·
                    rfl

theorem cell23_2785857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 5].length) (baseStart_2785857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785857 prefixEnd_2785857 := by exact prefixLift 2785857
  have htrace : WordTrace (prefixWord ++ tailWord_2785857) baseStart_2785857 baseEnd_2785857 := by
    simpa [prefixWord, tailWord_2785857, baseEnd_2785857] using wordTrace_append hprefix tailTrace_2785857
  have hstable : (prefixWord ++ tailWord_2785857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785857).length < 2 ^ (prefixWord ++ tailWord_2785857).sum := by decide
  have hdescent : baseEnd_2785857 < baseStart_2785857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785900 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 3, 4]
def baseStart_2785900 : Nat := 118140960795 + 2785900 * 2 ^ 59
def prefixEnd_2785900 : Nat := 4983230072969 + 3 ^ 40 * 2785900 * 2
def baseEnd_2785900 : Nat := 476835251786918462379295

theorem tailTrace_2785900 : CollatzResearch.WordTrace tailWord_2785900 prefixEnd_2785900 476835251786918462379295 := by
  unfold tailWord_2785900
  simp only [CollatzResearch.WordTrace]
  refine ⟨50805060303583784342613577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67740080404778379123484769 50805060303583784342613577)
  ·
    refine ⟨38103795227687838256960183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50805060303583784342613577 38103795227687838256960183)
    ·
      refine ⟨57155692841531757385440275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38103795227687838256960183 57155692841531757385440275)
      ·
        refine ⟨85733539262297636078160413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57155692841531757385440275 85733539262297636078160413)
        ·
          refine ⟨32150077223361613529310155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85733539262297636078160413 32150077223361613529310155)
          ·
            refine ⟨48225115835042420293965233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32150077223361613529310155 48225115835042420293965233)
            ·
              refine ⟨36168836876281815220473925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48225115835042420293965233 36168836876281815220473925)
              ·
                refine ⟨6781656914302840353838861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36168836876281815220473925 6781656914302840353838861)
                ·
                  refine ⟨2543121342863565132689573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6781656914302840353838861 2543121342863565132689573)
                  ·
                    refine ⟨476835251786918462379295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2543121342863565132689573 476835251786918462379295)
                    ·
                      rfl

theorem cell23_2785900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_2785900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785900 prefixEnd_2785900 := by exact prefixLift 2785900
  have htrace : WordTrace (prefixWord ++ tailWord_2785900) baseStart_2785900 baseEnd_2785900 := by
    simpa [prefixWord, tailWord_2785900, baseEnd_2785900] using wordTrace_append hprefix tailTrace_2785900
  have hstable : (prefixWord ++ tailWord_2785900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785900).length < 2 ^ (prefixWord ++ tailWord_2785900).sum := by decide
  have hdescent : baseEnd_2785900 < baseStart_2785900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
