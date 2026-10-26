import V185TrunkScan22Chunk349

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3121714 : List Nat := [3, 2, 1, 1, 2, 1, 6, 6]
def baseStart_3121714 : Nat := 118140960795 + 3121714 * 2 ^ 59
def prefixEnd_3121714 : Nat := 4983230072969 + 3 ^ 40 * 3121714 * 2
def baseEnd_3121714 : Nat := 118736277619978112097667

theorem tailTrace_3121714 : CollatzResearch.WordTrace tailWord_3121714 prefixEnd_3121714 118736277619978112097667 := by
  unfold tailWord_3121714
  simp only [CollatzResearch.WordTrace]
  refine ⟨28464565853142699787591049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75905508941713866100242797 28464565853142699787591049)
  ·
    refine ⟨21348424389857024840693287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28464565853142699787591049 21348424389857024840693287)
    ·
      refine ⟨32022636584785537261039931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21348424389857024840693287 32022636584785537261039931)
      ·
        refine ⟨48033954877178305891559897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32022636584785537261039931 48033954877178305891559897)
        ·
          refine ⟨36025466157883729418669923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48033954877178305891559897 36025466157883729418669923)
          ·
            refine ⟨54038199236825594128004885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36025466157883729418669923 54038199236825594128004885)
            ·
              refine ⟨2533040589226199724750229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54038199236825594128004885 2533040589226199724750229)
              ·
                refine ⟨118736277619978112097667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2533040589226199724750229 118736277619978112097667)
                ·
                  rfl

theorem cell22_3121714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 6].length) (baseStart_3121714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121714 prefixEnd_3121714 := by exact prefixLift 3121714
  have htrace : WordTrace (prefixWord ++ tailWord_3121714) baseStart_3121714 baseEnd_3121714 := by
    simpa [prefixWord, tailWord_3121714, baseEnd_3121714] using wordTrace_append hprefix tailTrace_3121714
  have hstable : (prefixWord ++ tailWord_3121714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121714).length < 2 ^ (prefixWord ++ tailWord_3121714).sum := by decide
  have hdescent : baseEnd_3121714 < baseStart_3121714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121787 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 10]
def baseStart_3121787 : Nat := 118140960795 + 3121787 * 2 ^ 59
def prefixEnd_3121787 : Nat := 4983230072969 + 3 ^ 40 * 3121787 * 2
def baseEnd_3121787 : Nat := 356217162657218383934593

theorem tailTrace_3121787 : CollatzResearch.WordTrace tailWord_3121787 prefixEnd_3121787 356217162657218383934593 := by
  unfold tailWord_3121787
  simp only [CollatzResearch.WordTrace]
  refine ⟨113860925941306332617771615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75907283960870888411847743 113860925941306332617771615)
  ·
    refine ⟨170791388911959498926657423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113860925941306332617771615 170791388911959498926657423)
    ·
      refine ⟨256187083367939248389986135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170791388911959498926657423 256187083367939248389986135)
      ·
        refine ⟨384280625051908872584979203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256187083367939248389986135 384280625051908872584979203)
        ·
          refine ⟨576420937577863308877468805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384280625051908872584979203 576420937577863308877468805)
          ·
            refine ⟨108078925795849370414525401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 576420937577863308877468805 108078925795849370414525401)
            ·
              refine ⟨81059194346887027810894051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108078925795849370414525401 81059194346887027810894051)
              ·
                refine ⟨121588791520330541716341077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81059194346887027810894051 121588791520330541716341077)
                ·
                  refine ⟨356217162657218383934593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 121588791520330541716341077 356217162657218383934593)
                  ·
                    rfl

theorem cell22_3121787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 10].length) (baseStart_3121787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121787 prefixEnd_3121787 := by exact prefixLift 3121787
  have htrace : WordTrace (prefixWord ++ tailWord_3121787) baseStart_3121787 baseEnd_3121787 := by
    simpa [prefixWord, tailWord_3121787, baseEnd_3121787] using wordTrace_append hprefix tailTrace_3121787
  have hstable : (prefixWord ++ tailWord_3121787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121787).length < 2 ^ (prefixWord ++ tailWord_3121787).sum := by decide
  have hdescent : baseEnd_3121787 < baseStart_3121787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121853 : List Nat := [1, 4, 1, 2, 1, 3, 3, 2, 2, 3]
def baseStart_3121853 : Nat := 118140960795 + 3121853 * 2 ^ 59
def prefixEnd_3121853 : Nat := 4983230072969 + 3 ^ 40 * 3121853 * 2
def baseEnd_3121853 : Nat := 1068674081120452979653577

theorem tailTrace_3121853 : CollatzResearch.WordTrace tailWord_3121853 prefixEnd_3121853 1068674081120452979653577 := by
  unfold tailWord_3121853
  simp only [CollatzResearch.WordTrace]
  refine ⟨113863333159067225889674213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75908888772711483926449475 113863333159067225889674213)
  ·
    refine ⟨21349374967325104854313915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113863333159067225889674213 21349374967325104854313915)
    ·
      refine ⟨32024062450987657281470873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21349374967325104854313915 32024062450987657281470873)
      ·
        refine ⟨24018046838240742961103155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32024062450987657281470873 24018046838240742961103155)
        ·
          refine ⟨36027070257361114441654733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24018046838240742961103155 36027070257361114441654733)
          ·
            refine ⟨13510151346510417915620525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36027070257361114441654733 13510151346510417915620525)
            ·
              refine ⟨5066306754941406718357697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13510151346510417915620525 5066306754941406718357697)
              ·
                refine ⟨3799730066206055038768273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5066306754941406718357697 3799730066206055038768273)
                ·
                  refine ⟨2849797549654541279076205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3799730066206055038768273 2849797549654541279076205)
                  ·
                    refine ⟨1068674081120452979653577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2849797549654541279076205 1068674081120452979653577)
                    ·
                      rfl

theorem cell22_3121853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_3121853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121853 prefixEnd_3121853 := by exact prefixLift 3121853
  have htrace : WordTrace (prefixWord ++ tailWord_3121853) baseStart_3121853 baseEnd_3121853 := by
    simpa [prefixWord, tailWord_3121853, baseEnd_3121853] using wordTrace_append hprefix tailTrace_3121853
  have hstable : (prefixWord ++ tailWord_3121853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121853).length < 2 ^ (prefixWord ++ tailWord_3121853).sum := by decide
  have hdescent : baseEnd_3121853 < baseStart_3121853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121870 : List Nat := [4, 1, 1, 1, 3, 3, 3, 1, 2, 3]
def baseStart_3121870 : Nat := 118140960795 + 3121870 * 2 ^ 59
def prefixEnd_3121870 : Nat := 4983230072969 + 3 ^ 40 * 3121870 * 2
def baseEnd_3121870 : Nat := 1068679900567870601978525

theorem tailTrace_3121870 : CollatzResearch.WordTrace tailWord_3121870 prefixEnd_3121870 1068679900567870601978525 := by
  unfold tailWord_3121870
  simp only [CollatzResearch.WordTrace]
  refine ⟨14232994150000704724130383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75909302133337091862028709 14232994150000704724130383)
  ·
    refine ⟨21349491225001057086195575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14232994150000704724130383 21349491225001057086195575)
    ·
      refine ⟨32024236837501585629293363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21349491225001057086195575 32024236837501585629293363)
      ·
        refine ⟨48036355256252378443940045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32024236837501585629293363 48036355256252378443940045)
        ·
          refine ⟨18013633221094641916477517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48036355256252378443940045 18013633221094641916477517)
          ·
            refine ⟨6755112457910490718679069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18013633221094641916477517 6755112457910490718679069)
            ·
              refine ⟨2533167171716434019504651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6755112457910490718679069 2533167171716434019504651)
              ·
                refine ⟨3799750757574651029256977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533167171716434019504651 3799750757574651029256977)
                ·
                  refine ⟨2849813068180988271942733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3799750757574651029256977 2849813068180988271942733)
                  ·
                    refine ⟨1068679900567870601978525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2849813068180988271942733 1068679900567870601978525)
                    ·
                      rfl

theorem cell22_3121870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_3121870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121870 prefixEnd_3121870 := by exact prefixLift 3121870
  have htrace : WordTrace (prefixWord ++ tailWord_3121870) baseStart_3121870 baseEnd_3121870 := by
    simpa [prefixWord, tailWord_3121870, baseEnd_3121870] using wordTrace_append hprefix tailTrace_3121870
  have hstable : (prefixWord ++ tailWord_3121870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121870).length < 2 ^ (prefixWord ++ tailWord_3121870).sum := by decide
  have hdescent : baseEnd_3121870 < baseStart_3121870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121881 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 3, 3]
def baseStart_3121881 : Nat := 118140960795 + 3121881 * 2 ^ 59
def prefixEnd_3121881 : Nat := 4983230072969 + 3 ^ 40 * 3121881 * 2
def baseEnd_3121881 : Nat := 1068683666092670239953491

theorem tailTrace_3121881 : CollatzResearch.WordTrace tailWord_3121881 prefixEnd_3121881 1068683666092670239953491 := by
  unfold tailWord_3121881
  simp only [CollatzResearch.WordTrace]
  refine ⟨113864354402965786671693497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75909569601977191114462331 113864354402965786671693497)
  ·
    refine ⟨85398265802224340003770123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113864354402965786671693497 85398265802224340003770123)
    ·
      refine ⟨128097398703336510005655185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85398265802224340003770123 128097398703336510005655185)
      ·
        refine ⟨96073049027502382504241389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128097398703336510005655185 96073049027502382504241389)
        ·
          refine ⟨36027393385313393439090521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96073049027502382504241389 36027393385313393439090521)
          ·
            refine ⟨27020545038985045079317891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36027393385313393439090521 27020545038985045079317891)
            ·
              refine ⟨40530817558477567618976837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27020545038985045079317891 40530817558477567618976837)
              ·
                refine ⟨7599528292214543928558157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40530817558477567618976837 7599528292214543928558157)
                ·
                  refine ⟨2849823109580453973209309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7599528292214543928558157 2849823109580453973209309)
                  ·
                    refine ⟨1068683666092670239953491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2849823109580453973209309 1068683666092670239953491)
                    ·
                      rfl

theorem cell22_3121881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 3].length) (baseStart_3121881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121881 prefixEnd_3121881 := by exact prefixLift 3121881
  have htrace : WordTrace (prefixWord ++ tailWord_3121881) baseStart_3121881 baseEnd_3121881 := by
    simpa [prefixWord, tailWord_3121881, baseEnd_3121881] using wordTrace_append hprefix tailTrace_3121881
  have hstable : (prefixWord ++ tailWord_3121881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121881).length < 2 ^ (prefixWord ++ tailWord_3121881).sum := by decide
  have hdescent : baseEnd_3121881 < baseStart_3121881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121928 : List Nat := [2, 1, 3, 2, 2, 2, 4, 1, 5]
def baseStart_3121928 : Nat := 118140960795 + 3121928 * 2 ^ 59
def prefixEnd_3121928 : Nat := 4983230072969 + 3 ^ 40 * 3121928 * 2
def baseEnd_3121928 : Nat := 356233251717725928009449

theorem tailTrace_3121928 : CollatzResearch.WordTrace tailWord_3121928 prefixEnd_3121928 356233251717725928009449 := by
  unfold tailWord_3121928
  simp only [CollatzResearch.WordTrace]
  refine ⟨56933034316897756849327219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75910712422530342465769625 56933034316897756849327219)
  ·
    refine ⟨85399551475346635273990829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56933034316897756849327219 85399551475346635273990829)
    ·
      refine ⟨32024831803254988227746561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85399551475346635273990829 32024831803254988227746561)
      ·
        refine ⟨24018623852441241170809921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32024831803254988227746561 24018623852441241170809921)
        ·
          refine ⟨18013967889330930878107441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24018623852441241170809921 18013967889330930878107441)
          ·
            refine ⟨13510475916998198158580581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18013967889330930878107441 13510475916998198158580581)
            ·
              refine ⟨2533214234437162154733859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13510475916998198158580581 2533214234437162154733859)
              ·
                refine ⟨3799821351655743232100789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533214234437162154733859 3799821351655743232100789)
                ·
                  refine ⟨356233251717725928009449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3799821351655743232100789 356233251717725928009449)
                  ·
                    rfl

theorem cell22_3121928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 5].length) (baseStart_3121928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121928 prefixEnd_3121928 := by exact prefixLift 3121928
  have htrace : WordTrace (prefixWord ++ tailWord_3121928) baseStart_3121928 baseEnd_3121928 := by
    simpa [prefixWord, tailWord_3121928, baseEnd_3121928] using wordTrace_append hprefix tailTrace_3121928
  have hstable : (prefixWord ++ tailWord_3121928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121928).length < 2 ^ (prefixWord ++ tailWord_3121928).sum := by decide
  have hdescent : baseEnd_3121928 < baseStart_3121928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121939 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 8]
def baseStart_3121939 : Nat := 118140960795 + 3121939 * 2 ^ 59
def prefixEnd_3121939 : Nat := 4983230072969 + 3 ^ 40 * 3121939 * 2
def baseEnd_3121939 : Nat := 356234506892659140667771

theorem tailTrace_3121939 : CollatzResearch.WordTrace tailWord_3121939 prefixEnd_3121939 356234506892659140667771 := by
  unfold tailWord_3121939
  simp only [CollatzResearch.WordTrace]
  refine ⟨113866469836755662577304871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75910979891170441718203247 113866469836755662577304871)
  ·
    refine ⟨170799704755133493865957307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113866469836755662577304871 170799704755133493865957307)
    ·
      refine ⟨256199557132700240798935961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170799704755133493865957307 256199557132700240798935961)
      ·
        refine ⟨192149667849525180599201971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256199557132700240798935961 192149667849525180599201971)
        ·
          refine ⟨288224501774287770898802957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192149667849525180599201971 288224501774287770898802957)
          ·
            refine ⟨108084188165357914087051109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288224501774287770898802957 108084188165357914087051109)
            ·
              refine ⟨20265785281004608891322083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108084188165357914087051109 20265785281004608891322083)
              ·
                refine ⟨30398677921506913336983125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20265785281004608891322083 30398677921506913336983125)
                ·
                  refine ⟨356234506892659140667771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30398677921506913336983125 356234506892659140667771)
                  ·
                    rfl

theorem cell22_3121939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 8].length) (baseStart_3121939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121939 prefixEnd_3121939 := by exact prefixLift 3121939
  have htrace : WordTrace (prefixWord ++ tailWord_3121939) baseStart_3121939 baseEnd_3121939 := by
    simpa [prefixWord, tailWord_3121939, baseEnd_3121939] using wordTrace_append hprefix tailTrace_3121939
  have hstable : (prefixWord ++ tailWord_3121939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121939).length < 2 ^ (prefixWord ++ tailWord_3121939).sum := by decide
  have hdescent : baseEnd_3121939 < baseStart_3121939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121941 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 3, 4]
def baseStart_3121941 : Nat := 118140960795 + 3121941 * 2 ^ 59
def prefixEnd_3121941 : Nat := 4983230072969 + 3 ^ 40 * 3121941 * 2
def baseEnd_3121941 : Nat := 1068704205318850083453307

theorem tailTrace_3121941 : CollatzResearch.WordTrace tailWord_3121941 prefixEnd_3121941 1068704205318850083453307 := by
  unfold tailWord_3121941
  simp only [CollatzResearch.WordTrace]
  refine ⟨113866542782748416918877677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75911028521832277945918451 113866542782748416918877677)
  ·
    refine ⟨42699953543530656344579129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113866542782748416918877677 42699953543530656344579129)
    ·
      refine ⟨32024965157647992258434347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42699953543530656344579129 32024965157647992258434347)
      ·
        refine ⟨48037447736471988387651521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32024965157647992258434347 48037447736471988387651521)
        ·
          refine ⟨36028085802353991290738641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48037447736471988387651521 36028085802353991290738641)
          ·
            refine ⟨27021064351765493468053981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36028085802353991290738641 27021064351765493468053981)
            ·
              refine ⟨10132899131912060050520243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27021064351765493468053981 10132899131912060050520243)
              ·
                refine ⟨15199348697868090075780365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10132899131912060050520243 15199348697868090075780365)
                ·
                  refine ⟨5699755761700533778417637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15199348697868090075780365 5699755761700533778417637)
                  ·
                    refine ⟨1068704205318850083453307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5699755761700533778417637 1068704205318850083453307)
                    ·
                      rfl

theorem cell22_3121941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_3121941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121941 prefixEnd_3121941 := by exact prefixLift 3121941
  have htrace : WordTrace (prefixWord ++ tailWord_3121941) baseStart_3121941 baseEnd_3121941 := by
    simpa [prefixWord, tailWord_3121941, baseEnd_3121941] using wordTrace_append hprefix tailTrace_3121941
  have hstable : (prefixWord ++ tailWord_3121941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121941).length < 2 ^ (prefixWord ++ tailWord_3121941).sum := by decide
  have hdescent : baseEnd_3121941 < baseStart_3121941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122018 : List Nat := [3, 3, 2, 1, 3, 1, 9]
def baseStart_3122018 : Nat := 118140960795 + 3122018 * 2 ^ 59
def prefixEnd_3122018 : Nat := 4983230072969 + 3 ^ 40 * 3122018 * 2
def baseEnd_3122018 : Nat := 39582613481201761084373

theorem tailTrace_3122018 : CollatzResearch.WordTrace tailWord_3122018 prefixEnd_3122018 39582613481201761084373 := by
  unfold tailWord_3122018
  simp only [CollatzResearch.WordTrace]
  refine ⟨28467337800867364767357677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75912900802312972712953805 28467337800867364767357677)
  ·
    refine ⟨10675251675325261787759129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28467337800867364767357677 10675251675325261787759129)
    ·
      refine ⟨8006438756493946340819347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10675251675325261787759129 8006438756493946340819347)
      ·
        refine ⟨12009658134740919511229021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8006438756493946340819347 12009658134740919511229021)
        ·
          refine ⟨4503621800527844816710883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12009658134740919511229021 4503621800527844816710883)
          ·
            refine ⟨6755432700791767225066325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4503621800527844816710883 6755432700791767225066325)
            ·
              refine ⟨39582613481201761084373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6755432700791767225066325 39582613481201761084373)
              ·
                rfl

theorem cell22_3122018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 9].length) (baseStart_3122018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122018 prefixEnd_3122018 := by exact prefixLift 3122018
  have htrace : WordTrace (prefixWord ++ tailWord_3122018) baseStart_3122018 baseEnd_3122018 := by
    simpa [prefixWord, tailWord_3122018, baseEnd_3122018] using wordTrace_append hprefix tailTrace_3122018
  have hstable : (prefixWord ++ tailWord_3122018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122018).length < 2 ^ (prefixWord ++ tailWord_3122018).sum := by decide
  have hdescent : baseEnd_3122018 < baseStart_3122018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122033 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 3, 3]
def baseStart_3122033 : Nat := 118140960795 + 3122033 * 2 ^ 59
def prefixEnd_3122033 : Nat := 4983230072969 + 3 ^ 40 * 3122033 * 2
def baseEnd_3122033 : Nat := 1068735698798992510153025

theorem tailTrace_3122033 : CollatzResearch.WordTrace tailWord_3122033 prefixEnd_3122033 1068735698798992510153025 := by
  unfold tailWord_3122033
  simp only [CollatzResearch.WordTrace]
  refine ⟨113869898298415116631226753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75913265532276744420817835 113869898298415116631226753)
  ·
    refine ⟨85402423723811337473420065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113869898298415116631226753 85402423723811337473420065)
    ·
      refine ⟨64051817792858503105065049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85402423723811337473420065 64051817792858503105065049)
      ·
        refine ⟨48038863344643877328798787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64051817792858503105065049 48038863344643877328798787)
        ·
          refine ⟨72058295016965815993198181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48038863344643877328798787 72058295016965815993198181)
          ·
            refine ⟨13510930315681090498724659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72058295016965815993198181 13510930315681090498724659)
            ·
              refine ⟨20266395473521635748086989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13510930315681090498724659 20266395473521635748086989)
              ·
                refine ⟨7599898302570613405532621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20266395473521635748086989 7599898302570613405532621)
                ·
                  refine ⟨2849961863463980027074733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7599898302570613405532621 2849961863463980027074733)
                  ·
                    refine ⟨1068735698798992510153025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2849961863463980027074733 1068735698798992510153025)
                    ·
                      rfl

theorem cell22_3122033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_3122033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122033 prefixEnd_3122033 := by exact prefixLift 3122033
  have htrace : WordTrace (prefixWord ++ tailWord_3122033) baseStart_3122033 baseEnd_3122033 := by
    simpa [prefixWord, tailWord_3122033, baseEnd_3122033] using wordTrace_append hprefix tailTrace_3122033
  have hstable : (prefixWord ++ tailWord_3122033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122033).length < 2 ^ (prefixWord ++ tailWord_3122033).sum := by decide
  have hdescent : baseEnd_3122033 < baseStart_3122033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122097 : List Nat := [1, 2, 2, 4, 3, 2, 2, 1, 5]
def baseStart_3122097 : Nat := 118140960795 + 3122097 * 2 ^ 59
def prefixEnd_3122097 : Nat := 4983230072969 + 3 ^ 40 * 3122097 * 2
def baseEnd_3122097 : Nat := 356252535768972558850943

theorem tailTrace_3122097 : CollatzResearch.WordTrace tailWord_3122097 prefixEnd_3122097 356252535768972558850943 := by
  unfold tailWord_3122097
  simp only [CollatzResearch.WordTrace]
  refine ⟨113872232570183255561556545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75914821713455503707704363 113872232570183255561556545)
  ·
    refine ⟨85404174427637441671167409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113872232570183255561556545 85404174427637441671167409)
    ·
      refine ⟨64053130820728081253375557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85404174427637441671167409 64053130820728081253375557)
      ·
        refine ⟨12009962028886515235007917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64053130820728081253375557 12009962028886515235007917)
        ·
          refine ⟨4503735760832443213127969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12009962028886515235007917 4503735760832443213127969)
          ·
            refine ⟨3377801820624332409845977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4503735760832443213127969 3377801820624332409845977)
            ·
              refine ⟨2533351365468249307384483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3377801820624332409845977 2533351365468249307384483)
              ·
                refine ⟨3800027048202373961076725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533351365468249307384483 3800027048202373961076725)
                ·
                  refine ⟨356252535768972558850943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3800027048202373961076725 356252535768972558850943)
                  ·
                    rfl

theorem cell22_3122097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 5].length) (baseStart_3122097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122097 prefixEnd_3122097 := by exact prefixLift 3122097
  have htrace : WordTrace (prefixWord ++ tailWord_3122097) baseStart_3122097 baseEnd_3122097 := by
    simpa [prefixWord, tailWord_3122097, baseEnd_3122097] using wordTrace_append hprefix tailTrace_3122097
  have hstable : (prefixWord ++ tailWord_3122097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122097).length < 2 ^ (prefixWord ++ tailWord_3122097).sum := by decide
  have hdescent : baseEnd_3122097 < baseStart_3122097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122123 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 1, 5]
def baseStart_3122123 : Nat := 118140960795 + 3122123 * 2 ^ 59
def prefixEnd_3122123 : Nat := 4983230072969 + 3 ^ 40 * 3122123 * 2
def baseEnd_3122123 : Nat := 1068766507638262275402749

theorem tailTrace_3122123 : CollatzResearch.WordTrace tailWord_3122123 prefixEnd_3122123 1068766507638262275402749 := by
  unfold tailWord_3122123
  simp only [CollatzResearch.WordTrace]
  refine ⟨113873180868089062002003023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75915453912059374668002015 113873180868089062002003023)
  ·
    refine ⟨170809771302133593003004535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113873180868089062002003023 170809771302133593003004535)
    ·
      refine ⟨256214656953200389504506803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170809771302133593003004535 256214656953200389504506803)
      ·
        refine ⟨384321985429800584256760205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256214656953200389504506803 384321985429800584256760205)
        ·
          refine ⟨144120744536175219096285077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384321985429800584256760205 144120744536175219096285077)
          ·
            refine ⟨6755659900133213395138363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 144120744536175219096285077 6755659900133213395138363)
            ·
              refine ⟨10133489850199820092707545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6755659900133213395138363 10133489850199820092707545)
              ·
                refine ⟨7600117387649865069530659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10133489850199820092707545 7600117387649865069530659)
                ·
                  refine ⟨11400176081474797604295989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7600117387649865069530659 11400176081474797604295989)
                  ·
                    refine ⟨1068766507638262275402749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11400176081474797604295989 1068766507638262275402749)
                    ·
                      rfl

theorem cell22_3122123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 5].length) (baseStart_3122123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122123 prefixEnd_3122123 := by exact prefixLift 3122123
  have htrace : WordTrace (prefixWord ++ tailWord_3122123) baseStart_3122123 baseEnd_3122123 := by
    simpa [prefixWord, tailWord_3122123, baseEnd_3122123] using wordTrace_append hprefix tailTrace_3122123
  have hstable : (prefixWord ++ tailWord_3122123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122123).length < 2 ^ (prefixWord ++ tailWord_3122123).sum := by decide
  have hdescent : baseEnd_3122123 < baseStart_3122123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122136 : List Nat := [2, 1, 2, 2, 2, 13]
def baseStart_3122136 : Nat := 118140960795 + 3122136 * 2 ^ 59
def prefixEnd_3122136 : Nat := 4983230072969 + 3 ^ 40 * 3122136 * 2
def baseEnd_3122136 : Nat := 13194703182764624380589

theorem tailTrace_3122136 : CollatzResearch.WordTrace tailWord_3122136 prefixEnd_3122136 13194703182764624380589 := by
  unfold tailWord_3122136
  simp only [CollatzResearch.WordTrace]
  refine ⟨56936827508520982611113131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75915770011361310148150841 56936827508520982611113131)
  ·
    refine ⟨85405241262781473916669697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56936827508520982611113131 85405241262781473916669697)
    ·
      refine ⟨64053930947086105437502273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85405241262781473916669697 64053930947086105437502273)
      ·
        refine ⟨48040448210314579078126705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64053930947086105437502273 48040448210314579078126705)
        ·
          refine ⟨36030336157735934308595029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48040448210314579078126705 36030336157735934308595029)
          ·
            refine ⟨13194703182764624380589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 36030336157735934308595029 13194703182764624380589)
            ·
              rfl

theorem cell22_3122136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 13].length) (baseStart_3122136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122136 prefixEnd_3122136 := by exact prefixLift 3122136
  have htrace : WordTrace (prefixWord ++ tailWord_3122136) baseStart_3122136 baseEnd_3122136 := by
    simpa [prefixWord, tailWord_3122136, baseEnd_3122136] using wordTrace_append hprefix tailTrace_3122136
  have hstable : (prefixWord ++ tailWord_3122136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122136).length < 2 ^ (prefixWord ++ tailWord_3122136).sum := by decide
  have hdescent : baseEnd_3122136 < baseStart_3122136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122178 : List Nat := [3, 4, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_3122178 : Nat := 118140960795 + 3122178 * 2 ^ 59
def prefixEnd_3122178 : Nat := 4983230072969 + 3 ^ 40 * 3122178 * 2
def baseEnd_3122178 : Nat := 1068785335262260465277581

theorem tailTrace_3122178 : CollatzResearch.WordTrace tailWord_3122178 prefixEnd_3122178 1068785335262260465277581 := by
  unfold tailWord_3122178
  simp only [CollatzResearch.WordTrace]
  refine ⟨28468796720722451598813797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75916791255259870930170125 28468796720722451598813797)
  ·
    refine ⟨5337899385135459674777587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28468796720722451598813797 5337899385135459674777587)
    ·
      refine ⟨8006849077703189512166381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5337899385135459674777587 8006849077703189512166381)
      ·
        refine ⟨3002568404138696067062393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8006849077703189512166381 3002568404138696067062393)
        ·
          refine ⟨2251926303104022050296795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3002568404138696067062393 2251926303104022050296795)
          ·
            refine ⟨3377889454656033075445193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2251926303104022050296795 3377889454656033075445193)
            ·
              refine ⟨2533417090992024806583895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3377889454656033075445193 2533417090992024806583895)
              ·
                refine ⟨3800125636488037209875843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533417090992024806583895 3800125636488037209875843)
                ·
                  refine ⟨5700188454732055814813765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3800125636488037209875843 5700188454732055814813765)
                  ·
                    refine ⟨1068785335262260465277581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5700188454732055814813765 1068785335262260465277581)
                    ·
                      rfl

theorem cell22_3122178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_3122178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122178 prefixEnd_3122178 := by exact prefixLift 3122178
  have htrace : WordTrace (prefixWord ++ tailWord_3122178) baseStart_3122178 baseEnd_3122178 := by
    simpa [prefixWord, tailWord_3122178, baseEnd_3122178] using wordTrace_append hprefix tailTrace_3122178
  have hstable : (prefixWord ++ tailWord_3122178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122178).length < 2 ^ (prefixWord ++ tailWord_3122178).sum := by decide
  have hdescent : baseEnd_3122178 < baseStart_3122178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122202 : List Nat := [3, 1, 1, 3, 1, 2, 1, 6, 1, 3]
def baseStart_3122202 : Nat := 118140960795 + 3122202 * 2 ^ 59
def prefixEnd_3122202 : Nat := 4983230072969 + 3 ^ 40 * 3122202 * 2
def baseEnd_3122202 : Nat := 1068793550952732402677507

theorem tailTrace_3122202 : CollatzResearch.WordTrace tailWord_3122202 prefixEnd_3122202 1068793550952732402677507 := by
  unfold tailWord_3122202
  simp only [CollatzResearch.WordTrace]
  refine ⟨28469015558700714623532215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75917374823201905662752573 28469015558700714623532215)
  ·
    refine ⟨42703523338051071935298323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28469015558700714623532215 42703523338051071935298323)
    ·
      refine ⟨64055285007076607902947485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42703523338051071935298323 64055285007076607902947485)
      ·
        refine ⟨24020731877653727963605307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64055285007076607902947485 24020731877653727963605307)
        ·
          refine ⟨36031097816480591945407961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24020731877653727963605307 36031097816480591945407961)
          ·
            refine ⟨27023323362360443959055971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36031097816480591945407961 27023323362360443959055971)
            ·
              refine ⟨40534985043540665938583957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27023323362360443959055971 40534985043540665938583957)
              ·
                refine ⟨1900077423915968715871123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40534985043540665938583957 1900077423915968715871123)
                ·
                  refine ⟨2850116135873953073806685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1900077423915968715871123 2850116135873953073806685)
                  ·
                    refine ⟨1068793550952732402677507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2850116135873953073806685 1068793550952732402677507)
                    ·
                      rfl

theorem cell22_3122202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_3122202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122202 prefixEnd_3122202 := by exact prefixLift 3122202
  have htrace : WordTrace (prefixWord ++ tailWord_3122202) baseStart_3122202 baseEnd_3122202 := by
    simpa [prefixWord, tailWord_3122202, baseEnd_3122202] using wordTrace_append hprefix tailTrace_3122202
  have hstable : (prefixWord ++ tailWord_3122202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122202).length < 2 ^ (prefixWord ++ tailWord_3122202).sum := by decide
  have hdescent : baseEnd_3122202 < baseStart_3122202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122213 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 2, 5]
def baseStart_3122213 : Nat := 118140960795 + 3122213 * 2 ^ 59
def prefixEnd_3122213 : Nat := 4983230072969 + 3 ^ 40 * 3122213 * 2
def baseEnd_3122213 : Nat := 1068797316477532040652473

theorem tailTrace_3122213 : CollatzResearch.WordTrace tailWord_3122213 prefixEnd_3122213 1068797316477532040652473 := by
  unfold tailWord_3122213
  simp only [CollatzResearch.WordTrace]
  refine ⟨113876463437763007372779293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75917642291842004915186195 113876463437763007372779293)
  ·
    refine ⟨42703673789161127764792235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113876463437763007372779293 42703673789161127764792235)
    ·
      refine ⟨64055510683741691647188353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42703673789161127764792235 64055510683741691647188353)
      ·
        refine ⟨48041633012806268735391265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64055510683741691647188353 48041633012806268735391265)
        ·
          refine ⟨36031224759604701551543449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48041633012806268735391265 36031224759604701551543449)
          ·
            refine ⟨27023418569703526163657587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36031224759604701551543449 27023418569703526163657587)
            ·
              refine ⟨40535127854555289245486381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27023418569703526163657587 40535127854555289245486381)
              ·
                refine ⟨15200672945458233467057393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40535127854555289245486381 15200672945458233467057393)
                ·
                  refine ⟨11400504709093675100293045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15200672945458233467057393 11400504709093675100293045)
                  ·
                    refine ⟨1068797316477532040652473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11400504709093675100293045 1068797316477532040652473)
                    ·
                      rfl

theorem cell22_3122213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_3122213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122213 prefixEnd_3122213 := by exact prefixLift 3122213
  have htrace : WordTrace (prefixWord ++ tailWord_3122213) baseStart_3122213 baseEnd_3122213 := by
    simpa [prefixWord, tailWord_3122213, baseEnd_3122213] using wordTrace_append hprefix tailTrace_3122213
  have hstable : (prefixWord ++ tailWord_3122213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122213).length < 2 ^ (prefixWord ++ tailWord_3122213).sum := by decide
  have hdescent : baseEnd_3122213 < baseStart_3122213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122245 : List Nat := [1, 3, 1, 1, 1, 3, 4, 3, 1, 4]
def baseStart_3122245 : Nat := 118140960795 + 3122245 * 2 ^ 59
def prefixEnd_3122245 : Nat := 4983230072969 + 3 ^ 40 * 3122245 * 2
def baseEnd_3122245 : Nat := 1068808270731494623852375

theorem tailTrace_3122245 : CollatzResearch.WordTrace tailWord_3122245 prefixEnd_3122245 1068808270731494623852375 := by
  unfold tailWord_3122245
  simp only [CollatzResearch.WordTrace]
  refine ⟨113877630573647076837944189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75918420382431384558629459 113877630573647076837944189)
  ·
    refine ⟨42704111465117653814229071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113877630573647076837944189 42704111465117653814229071)
    ·
      refine ⟨64056167197676480721343607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42704111465117653814229071 64056167197676480721343607)
      ·
        refine ⟨96084250796514721082015411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64056167197676480721343607 96084250796514721082015411)
        ·
          refine ⟨144126376194772081623023117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96084250796514721082015411 144126376194772081623023117)
          ·
            refine ⟨54047391073039530608633669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144126376194772081623023117 54047391073039530608633669)
            ·
              refine ⟨10133885826194911989118813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54047391073039530608633669 10133885826194911989118813)
              ·
                refine ⟨3800207184823091995919555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10133885826194911989118813 3800207184823091995919555)
                ·
                  refine ⟨5700310777234637993879333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3800207184823091995919555 5700310777234637993879333)
                  ·
                    refine ⟨1068808270731494623852375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5700310777234637993879333 1068808270731494623852375)
                    ·
                      rfl

theorem cell22_3122245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_3122245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122245 prefixEnd_3122245 := by exact prefixLift 3122245
  have htrace : WordTrace (prefixWord ++ tailWord_3122245) baseStart_3122245 baseEnd_3122245 := by
    simpa [prefixWord, tailWord_3122245, baseEnd_3122245] using wordTrace_append hprefix tailTrace_3122245
  have hstable : (prefixWord ++ tailWord_3122245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122245).length < 2 ^ (prefixWord ++ tailWord_3122245).sum := by decide
  have hdescent : baseEnd_3122245 < baseStart_3122245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122260 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 6]
def baseStart_3122260 : Nat := 118140960795 + 3122260 * 2 ^ 59
def prefixEnd_3122260 : Nat := 4983230072969 + 3 ^ 40 * 3122260 * 2
def baseEnd_3122260 : Nat := 356271135179346528242443

theorem tailTrace_3122260 : CollatzResearch.WordTrace tailWord_3122260 prefixEnd_3122260 356271135179346528242443 := by
  unfold tailWord_3122260
  simp only [CollatzResearch.WordTrace]
  refine ⟨56939088834296367199870117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75918785112395156266493489 56939088834296367199870117)
  ·
    refine ⟨10676079156430568849975647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56939088834296367199870117 10676079156430568849975647)
    ·
      refine ⟨16014118734645853274963471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10676079156430568849975647 16014118734645853274963471)
      ·
        refine ⟨24021178101968779912445207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16014118734645853274963471 24021178101968779912445207)
        ·
          refine ⟨36031767152953169868667811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24021178101968779912445207 36031767152953169868667811)
          ·
            refine ⟨54047650729429754803001717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36031767152953169868667811 54047650729429754803001717)
            ·
              refine ⟨5066967255884039512781411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54047650729429754803001717 5066967255884039512781411)
              ·
                refine ⟨7600450883826059269172117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5066967255884039512781411 7600450883826059269172117)
                ·
                  refine ⟨356271135179346528242443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7600450883826059269172117 356271135179346528242443)
                  ·
                    rfl

theorem cell22_3122260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_3122260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122260 prefixEnd_3122260 := by exact prefixLift 3122260
  have htrace : WordTrace (prefixWord ++ tailWord_3122260) baseStart_3122260 baseEnd_3122260 := by
    simpa [prefixWord, tailWord_3122260, baseEnd_3122260] using wordTrace_append hprefix tailTrace_3122260
  have hstable : (prefixWord ++ tailWord_3122260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122260).length < 2 ^ (prefixWord ++ tailWord_3122260).sum := by decide
  have hdescent : baseEnd_3122260 < baseStart_3122260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122273 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 3, 6]
def baseStart_3122273 : Nat := 118140960795 + 3122273 * 2 ^ 59
def prefixEnd_3122273 : Nat := 4983230072969 + 3 ^ 40 * 3122273 * 2
def baseEnd_3122273 : Nat := 1068817855703711884152289

theorem tailTrace_3122273 : CollatzResearch.WordTrace tailWord_3122273 prefixEnd_3122273 1068817855703711884152289 := by
  unfold tailWord_3122273
  simp only [CollatzResearch.WordTrace]
  refine ⟨113878651817545637619963473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75919101211697091746642315 113878651817545637619963473)
  ·
    refine ⟨85408988863159228214972605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113878651817545637619963473 85408988863159228214972605)
    ·
      refine ⟨32028370823684710580614727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85408988863159228214972605 32028370823684710580614727)
      ·
        refine ⟨48042556235527065870922091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32028370823684710580614727 48042556235527065870922091)
        ·
          refine ⟨72063834353290598806383137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48042556235527065870922091 72063834353290598806383137)
          ·
            refine ⟨54047875764967949104787353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72063834353290598806383137 54047875764967949104787353)
            ·
              refine ⟨40535906823725961828590515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54047875764967949104787353 40535906823725961828590515)
              ·
                refine ⟨60803860235588942742885773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40535906823725961828590515 60803860235588942742885773)
                ·
                  refine ⟨22801447588345853528582165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60803860235588942742885773 22801447588345853528582165)
                  ·
                    refine ⟨1068817855703711884152289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22801447588345853528582165 1068817855703711884152289)
                    ·
                      rfl

theorem cell22_3122273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_3122273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122273 prefixEnd_3122273 := by exact prefixLift 3122273
  have htrace : WordTrace (prefixWord ++ tailWord_3122273) baseStart_3122273 baseEnd_3122273 := by
    simpa [prefixWord, tailWord_3122273, baseEnd_3122273] using wordTrace_append hprefix tailTrace_3122273
  have hstable : (prefixWord ++ tailWord_3122273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122273).length < 2 ^ (prefixWord ++ tailWord_3122273).sum := by decide
  have hdescent : baseEnd_3122273 < baseStart_3122273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122288 : List Nat := [2, 1, 1, 1, 5, 1, 1, 10]
def baseStart_3122288 : Nat := 118140960795 + 3122288 * 2 ^ 59
def prefixEnd_3122288 : Nat := 4983230072969 + 3 ^ 40 * 3122288 * 2
def baseEnd_3122288 : Nat := 118758110056695205003027

theorem tailTrace_3122288 : CollatzResearch.WordTrace tailWord_3122288 prefixEnd_3122288 118758110056695205003027 := by
  unfold tailWord_3122288
  simp only [CollatzResearch.WordTrace]
  refine ⟨56939599456245647590879759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75919465941660863454506345 56939599456245647590879759)
  ·
    refine ⟨85409399184368471386319639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56939599456245647590879759 85409399184368471386319639)
    ·
      refine ⟨128114098776552707079479459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85409399184368471386319639 128114098776552707079479459)
      ·
        refine ⟨192171148164829060619219189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128114098776552707079479459 192171148164829060619219189)
        ·
          refine ⟨18016045140452724433051799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192171148164829060619219189 18016045140452724433051799)
          ·
            refine ⟨27024067710679086649577699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18016045140452724433051799 27024067710679086649577699)
            ·
              refine ⟨40536101566018629974366549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27024067710679086649577699 40536101566018629974366549)
              ·
                refine ⟨118758110056695205003027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40536101566018629974366549 118758110056695205003027)
                ·
                  rfl

theorem cell22_3122288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 10].length) (baseStart_3122288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122288 prefixEnd_3122288 := by exact prefixLift 3122288
  have htrace : WordTrace (prefixWord ++ tailWord_3122288) baseStart_3122288 baseEnd_3122288 := by
    simpa [prefixWord, tailWord_3122288, baseEnd_3122288] using wordTrace_append hprefix tailTrace_3122288
  have hstable : (prefixWord ++ tailWord_3122288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122288).length < 2 ^ (prefixWord ++ tailWord_3122288).sum := by decide
  have hdescent : baseEnd_3122288 < baseStart_3122288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122309 : List Nat := [1, 3, 1, 1, 6, 1, 2, 2, 2, 3]
def baseStart_3122309 : Nat := 118140960795 + 3122309 * 2 ^ 59
def prefixEnd_3122309 : Nat := 4983230072969 + 3 ^ 40 * 3122309 * 2
def baseEnd_3122309 : Nat := 1068830179239419790252179

theorem tailTrace_3122309 : CollatzResearch.WordTrace tailWord_3122309 prefixEnd_3122309 1068830179239419790252179 := by
  unfold tailWord_3122309
  simp only [CollatzResearch.WordTrace]
  refine ⟨113879964845415215768273981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75919976563610143845515987 113879964845415215768273981)
  ·
    refine ⟨42704986817030705913102743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113879964845415215768273981 42704986817030705913102743)
    ·
      refine ⟨64057480225546058869654115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42704986817030705913102743 64057480225546058869654115)
      ·
        refine ⟨96086220338319088304481173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64057480225546058869654115 96086220338319088304481173)
        ·
          refine ⟨4504041578358707264272555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96086220338319088304481173 4504041578358707264272555)
          ·
            refine ⟨6756062367538060896408833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4504041578358707264272555 6756062367538060896408833)
            ·
              refine ⟨5067046775653545672306625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6756062367538060896408833 5067046775653545672306625)
              ·
                refine ⟨3800285081740159254229969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5067046775653545672306625 3800285081740159254229969)
                ·
                  refine ⟨2850213811305119440672477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3800285081740159254229969 2850213811305119440672477)
                  ·
                    refine ⟨1068830179239419790252179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2850213811305119440672477 1068830179239419790252179)
                    ·
                      rfl

theorem cell22_3122309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_3122309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122309 prefixEnd_3122309 := by exact prefixLift 3122309
  have htrace : WordTrace (prefixWord ++ tailWord_3122309) baseStart_3122309 baseEnd_3122309 := by
    simpa [prefixWord, tailWord_3122309, baseEnd_3122309] using wordTrace_append hprefix tailTrace_3122309
  have hstable : (prefixWord ++ tailWord_3122309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122309).length < 2 ^ (prefixWord ++ tailWord_3122309).sum := by decide
  have hdescent : baseEnd_3122309 < baseStart_3122309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122322 : List Nat := [3, 2, 3, 1, 1, 4, 1, 7]
def baseStart_3122322 : Nat := 118140960795 + 3122322 * 2 ^ 59
def prefixEnd_3122322 : Nat := 4983230072969 + 3 ^ 40 * 3122322 * 2
def baseEnd_3122322 : Nat := 118759403267232454408571

theorem tailTrace_3122322 : CollatzResearch.WordTrace tailWord_3122322 prefixEnd_3122322 118759403267232454408571 := by
  unfold tailWord_3122322
  simp only [CollatzResearch.WordTrace]
  refine ⟨28470109748592029747124305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75920292662912079325664813 28470109748592029747124305)
  ·
    refine ⟨21352582311444022310343229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28470109748592029747124305 21352582311444022310343229)
    ·
      refine ⟨8007218366791508366378711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21352582311444022310343229 8007218366791508366378711)
      ·
        refine ⟨12010827550187262549568067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8007218366791508366378711 12010827550187262549568067)
        ·
          refine ⟨18016241325280893824352101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12010827550187262549568067 18016241325280893824352101)
          ·
            refine ⟨3378045248490167592066019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18016241325280893824352101 3378045248490167592066019)
            ·
              refine ⟨5067067872735251388099029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3378045248490167592066019 5067067872735251388099029)
              ·
                refine ⟨118759403267232454408571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5067067872735251388099029 118759403267232454408571)
                ·
                  rfl

theorem cell22_3122322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 7].length) (baseStart_3122322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122322 prefixEnd_3122322 := by exact prefixLift 3122322
  have htrace : WordTrace (prefixWord ++ tailWord_3122322) baseStart_3122322 baseEnd_3122322 := by
    simpa [prefixWord, tailWord_3122322, baseEnd_3122322] using wordTrace_append hprefix tailTrace_3122322
  have hstable : (prefixWord ++ tailWord_3122322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122322).length < 2 ^ (prefixWord ++ tailWord_3122322).sum := by decide
  have hdescent : baseEnd_3122322 < baseStart_3122322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122337 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 3, 3]
def baseStart_3122337 : Nat := 118140960795 + 3122337 * 2 ^ 59
def prefixEnd_3122337 : Nat := 4983230072969 + 3 ^ 40 * 3122337 * 2
def baseEnd_3122337 : Nat := 1068839764211637050552093

theorem tailTrace_3122337 : CollatzResearch.WordTrace tailWord_3122337 prefixEnd_3122337 1068839764211637050552093 := by
  unfold tailWord_3122337
  simp only [CollatzResearch.WordTrace]
  refine ⟨113880986089313776550293265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75920657392875851033528843 113880986089313776550293265)
  ·
    refine ⟨85410739566985332412719949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113880986089313776550293265 85410739566985332412719949)
    ·
      refine ⟨32029027337619499654769981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85410739566985332412719949 32029027337619499654769981)
      ·
        refine ⟨12010885251607312370538743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32029027337619499654769981 12010885251607312370538743)
        ·
          refine ⟨18016327877410968555808115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12010885251607312370538743 18016327877410968555808115)
          ·
            refine ⟨27024491816116452833712173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18016327877410968555808115 27024491816116452833712173)
            ·
              refine ⟨10134184431043669812642065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27024491816116452833712173 10134184431043669812642065)
              ·
                refine ⟨7600638323282752359481549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10134184431043669812642065 7600638323282752359481549)
                ·
                  refine ⟨2850239371231032134805581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7600638323282752359481549 2850239371231032134805581)
                  ·
                    refine ⟨1068839764211637050552093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2850239371231032134805581 1068839764211637050552093)
                    ·
                      rfl

theorem cell22_3122337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_3122337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122337 prefixEnd_3122337 := by exact prefixLift 3122337
  have htrace : WordTrace (prefixWord ++ tailWord_3122337) baseStart_3122337 baseEnd_3122337 := by
    simpa [prefixWord, tailWord_3122337, baseEnd_3122337] using wordTrace_append hprefix tailTrace_3122337
  have hstable : (prefixWord ++ tailWord_3122337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122337).length < 2 ^ (prefixWord ++ tailWord_3122337).sum := by decide
  have hdescent : baseEnd_3122337 < baseStart_3122337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122354 : List Nat := [3, 2, 1, 1, 1, 4, 1, 5, 1, 3]
def baseStart_3122354 : Nat := 118140960795 + 3122354 * 2 ^ 59
def prefixEnd_3122354 : Nat := 4983230072969 + 3 ^ 40 * 3122354 * 2
def baseEnd_3122354 : Nat := 1068845583659054672877041

theorem tailTrace_3122354 : CollatzResearch.WordTrace tailWord_3122354 prefixEnd_3122354 1068845583659054672877041 := by
  unfold tailWord_3122354
  simp only [CollatzResearch.WordTrace]
  refine ⟨28470401532563047113415529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75921070753501458969108077 28470401532563047113415529)
  ·
    refine ⟨21352801149422285335061647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28470401532563047113415529 21352801149422285335061647)
    ·
      refine ⟨32029201724133428002592471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21352801149422285335061647 32029201724133428002592471)
      ·
        refine ⟨48043802586200142003888707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32029201724133428002592471 48043802586200142003888707)
        ·
          refine ⟨72065703879300213005833061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48043802586200142003888707 72065703879300213005833061)
          ·
            refine ⟨13512319477368789938593699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72065703879300213005833061 13512319477368789938593699)
            ·
              refine ⟨20268479216053184907890549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13512319477368789938593699 20268479216053184907890549)
              ·
                refine ⟨1900169926504986085114739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20268479216053184907890549 1900169926504986085114739)
                ·
                  refine ⟨2850254889757479127672109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1900169926504986085114739 2850254889757479127672109)
                  ·
                    refine ⟨1068845583659054672877041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2850254889757479127672109 1068845583659054672877041)
                    ·
                      rfl

theorem cell22_3122354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_3122354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122354 prefixEnd_3122354 := by exact prefixLift 3122354
  have htrace : WordTrace (prefixWord ++ tailWord_3122354) baseStart_3122354 baseEnd_3122354 := by
    simpa [prefixWord, tailWord_3122354, baseEnd_3122354] using wordTrace_append hprefix tailTrace_3122354
  have hstable : (prefixWord ++ tailWord_3122354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122354).length < 2 ^ (prefixWord ++ tailWord_3122354).sum := by decide
  have hdescent : baseEnd_3122354 < baseStart_3122354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122365 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_3122365 : Nat := 118140960795 + 3122365 * 2 ^ 59
def prefixEnd_3122365 : Nat := 4983230072969 + 3 ^ 40 * 3122365 * 2
def baseEnd_3122365 : Nat := 1068849349183854310852007

theorem tailTrace_3122365 : CollatzResearch.WordTrace tailWord_3122365 prefixEnd_3122365 1068849349183854310852007 := by
  unfold tailWord_3122365
  simp only [CollatzResearch.WordTrace]
  refine ⟨113882007333212337332312549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75921338222141558221541699 113882007333212337332312549)
  ·
    refine ⟨21352876374977313249808603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113882007333212337332312549 21352876374977313249808603)
    ·
      refine ⟨32029314562465969874712905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21352876374977313249808603 32029314562465969874712905)
      ·
        refine ⟨24021985921849477406034679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32029314562465969874712905 24021985921849477406034679)
        ·
          refine ⟨36032978882774216109052019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24021985921849477406034679 36032978882774216109052019)
          ·
            refine ⟨54049468324161324163578029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36032978882774216109052019 54049468324161324163578029)
            ·
              refine ⟨20268550621560496561341761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54049468324161324163578029 20268550621560496561341761)
              ·
                refine ⟨15201412966170372421006321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20268550621560496561341761 15201412966170372421006321)
                ·
                  refine ⟨11401059724627779315754741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15201412966170372421006321 11401059724627779315754741)
                  ·
                    refine ⟨1068849349183854310852007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11401059724627779315754741 1068849349183854310852007)
                    ·
                      rfl

theorem cell22_3122365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_3122365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122365 prefixEnd_3122365 := by exact prefixLift 3122365
  have htrace : WordTrace (prefixWord ++ tailWord_3122365) baseStart_3122365 baseEnd_3122365 := by
    simpa [prefixWord, tailWord_3122365, baseEnd_3122365] using wordTrace_append hprefix tailTrace_3122365
  have hstable : (prefixWord ++ tailWord_3122365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122365).length < 2 ^ (prefixWord ++ tailWord_3122365).sum := by decide
  have hdescent : baseEnd_3122365 < baseStart_3122365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122444 : List Nat := [2, 2, 1, 2, 2, 4, 1, 3, 2, 3]
def baseStart_3122444 : Nat := 118140960795 + 3122444 * 2 ^ 59
def prefixEnd_3122444 : Nat := 4983230072969 + 3 ^ 40 * 3122444 * 2
def baseEnd_3122444 : Nat := 1068876392498324438126765

theorem tailTrace_3122444 : CollatzResearch.WordTrace tailWord_3122444 prefixEnd_3122444 1068876392498324438126765 := by
  unfold tailWord_3122444
  simp only [CollatzResearch.WordTrace]
  refine ⟨56942444349963066912219193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75923259133284089216292257 56942444349963066912219193)
  ·
    refine ⟨42706833262472300184164395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56942444349963066912219193 42706833262472300184164395)
    ·
      refine ⟨64060249893708450276246593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42706833262472300184164395 64060249893708450276246593)
      ·
        refine ⟨48045187420281337707184945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64060249893708450276246593 48045187420281337707184945)
        ·
          refine ⟨36033890565211003280388709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48045187420281337707184945 36033890565211003280388709)
          ·
            refine ⟨6756354480977063115072883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36033890565211003280388709 6756354480977063115072883)
            ·
              refine ⟨10134531721465594672609325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6756354480977063115072883 10134531721465594672609325)
              ·
                refine ⟨3800449395549598002228497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10134531721465594672609325 3800449395549598002228497)
                ·
                  refine ⟨2850337046662198501671373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3800449395549598002228497 2850337046662198501671373)
                  ·
                    refine ⟨1068876392498324438126765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2850337046662198501671373 1068876392498324438126765)
                    ·
                      rfl

theorem cell22_3122444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_3122444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122444 prefixEnd_3122444 := by exact prefixLift 3122444
  have htrace : WordTrace (prefixWord ++ tailWord_3122444) baseStart_3122444 baseEnd_3122444 := by
    simpa [prefixWord, tailWord_3122444, baseEnd_3122444] using wordTrace_append hprefix tailTrace_3122444
  have hstable : (prefixWord ++ tailWord_3122444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122444).length < 2 ^ (prefixWord ++ tailWord_3122444).sum := by decide
  have hdescent : baseEnd_3122444 < baseStart_3122444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122536 : List Nat := [2, 1, 4, 2, 3, 2, 1, 2, 5]
def baseStart_3122536 : Nat := 118140960795 + 3122536 * 2 ^ 59
def prefixEnd_3122536 : Nat := 4983230072969 + 3 ^ 40 * 3122536 * 2
def baseEnd_3122536 : Nat := 356302628659488954942161

theorem tailTrace_3122536 : CollatzResearch.WordTrace tailWord_3122536 prefixEnd_3122536 356302628659488954942161 := by
  unfold tailWord_3122536
  simp only [CollatzResearch.WordTrace]
  refine ⟨56944122107796416768393731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75925496143728555691191641 56944122107796416768393731)
  ·
    refine ⟨85416183161694625152590597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56944122107796416768393731 85416183161694625152590597)
    ·
      refine ⟨16015534342817742216110737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85416183161694625152590597 16015534342817742216110737)
      ·
        refine ⟨12011650757113306662083053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16015534342817742216110737 12011650757113306662083053)
        ·
          refine ⟨4504369033917489998281145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12011650757113306662083053 4504369033917489998281145)
          ·
            refine ⟨3378276775438117498710859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4504369033917489998281145 3378276775438117498710859)
            ·
              refine ⟨5067415163157176248066289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3378276775438117498710859 5067415163157176248066289)
              ·
                refine ⟨3800561372367882186049717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5067415163157176248066289 3800561372367882186049717)
                ·
                  refine ⟨356302628659488954942161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3800561372367882186049717 356302628659488954942161)
                  ·
                    rfl

theorem cell22_3122536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 5].length) (baseStart_3122536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122536 prefixEnd_3122536 := by exact prefixLift 3122536
  have htrace : WordTrace (prefixWord ++ tailWord_3122536) baseStart_3122536 baseEnd_3122536 := by
    simpa [prefixWord, tailWord_3122536, baseEnd_3122536] using wordTrace_append hprefix tailTrace_3122536
  have hstable : (prefixWord ++ tailWord_3122536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122536).length < 2 ^ (prefixWord ++ tailWord_3122536).sum := by decide
  have hdescent : baseEnd_3122536 < baseStart_3122536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122594 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3122594 : Nat := 118140960795 + 3122594 * 2 ^ 59
def prefixEnd_3122594 : Nat := 4983230072969 + 3 ^ 40 * 3122594 * 2
def baseEnd_3122594 : Nat := 1068927740563774046876305

theorem tailTrace_3122594 : CollatzResearch.WordTrace tailWord_3122594 prefixEnd_3122594 1068927740563774046876305 := by
  unfold tailWord_3122594
  simp only [CollatzResearch.WordTrace]
  refine ⟨28472589912345677360599709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75926906432921806294932557 28472589912345677360599709)
  ·
    refine ⟨10677221217129629010224891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28472589912345677360599709 10677221217129629010224891)
    ·
      refine ⟨16015831825694443515337337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10677221217129629010224891 16015831825694443515337337)
      ·
        refine ⟨12011873869270832636503003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16015831825694443515337337 12011873869270832636503003)
        ·
          refine ⟨18017810803906248954754505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12011873869270832636503003 18017810803906248954754505)
          ·
            refine ⟨13513358102929686716065879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18017810803906248954754505 13513358102929686716065879)
            ·
              refine ⟨20270037154394530074098819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13513358102929686716065879 20270037154394530074098819)
              ·
                refine ⟨30405055731591795111148229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20270037154394530074098819 30405055731591795111148229)
                ·
                  refine ⟨5700947949673461583340293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30405055731591795111148229 5700947949673461583340293)
                  ·
                    refine ⟨1068927740563774046876305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5700947949673461583340293 1068927740563774046876305)
                    ·
                      rfl

theorem cell22_3122594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3122594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122594 prefixEnd_3122594 := by exact prefixLift 3122594
  have htrace : WordTrace (prefixWord ++ tailWord_3122594) baseStart_3122594 baseEnd_3122594 := by
    simpa [prefixWord, tailWord_3122594, baseEnd_3122594] using wordTrace_append hprefix tailTrace_3122594
  have hstable : (prefixWord ++ tailWord_3122594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122594).length < 2 ^ (prefixWord ++ tailWord_3122594).sum := by decide
  have hdescent : baseEnd_3122594 < baseStart_3122594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122613 : List Nat := [1, 3, 3, 2, 2, 1, 4, 1, 2, 3]
def baseStart_3122613 : Nat := 118140960795 + 3122613 * 2 ^ 59
def prefixEnd_3122613 : Nat := 4983230072969 + 3 ^ 40 * 3122613 * 2
def baseEnd_3122613 : Nat := 1068934244652064330651247

theorem tailTrace_3122613 : CollatzResearch.WordTrace tailWord_3122613 prefixEnd_3122613 1068934244652064330651247 := by
  unfold tailWord_3122613
  simp only [CollatzResearch.WordTrace]
  refine ⟨113891052636313875687340493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75927368424209250458226995 113891052636313875687340493)
  ·
    refine ⟨42709144738617703382752685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113891052636313875687340493 42709144738617703382752685)
    ·
      refine ⟨16015929276981638768532257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42709144738617703382752685 16015929276981638768532257)
      ·
        refine ⟨12011946957736229076399193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16015929276981638768532257 12011946957736229076399193)
        ·
          refine ⟨9008960218302171807299395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12011946957736229076399193 9008960218302171807299395)
          ·
            refine ⟨13513440327453257710949093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9008960218302171807299395 13513440327453257710949093)
            ·
              refine ⟨2533770061397485820802955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13513440327453257710949093 2533770061397485820802955)
              ·
                refine ⟨3800655092096228731204433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533770061397485820802955 3800655092096228731204433)
                ·
                  refine ⟨2850491319072171548403325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3800655092096228731204433 2850491319072171548403325)
                  ·
                    refine ⟨1068934244652064330651247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2850491319072171548403325 1068934244652064330651247)
                    ·
                      rfl

theorem cell22_3122613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_3122613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122613 prefixEnd_3122613 := by exact prefixLift 3122613
  have htrace : WordTrace (prefixWord ++ tailWord_3122613) baseStart_3122613 baseEnd_3122613 := by
    simpa [prefixWord, tailWord_3122613, baseEnd_3122613] using wordTrace_append hprefix tailTrace_3122613
  have hstable : (prefixWord ++ tailWord_3122613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122613).length < 2 ^ (prefixWord ++ tailWord_3122613).sum := by decide
  have hdescent : baseEnd_3122613 < baseStart_3122613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122624 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 3, 3]
def baseStart_3122624 : Nat := 118140960795 + 3122624 * 2 ^ 59
def prefixEnd_3122624 : Nat := 4983230072969 + 3 ^ 40 * 3122624 * 2
def baseEnd_3122624 : Nat := 1068938010176863968626213

theorem tailTrace_3122624 : CollatzResearch.WordTrace tailWord_3122624 prefixEnd_3122624 1068938010176863968626213 := by
  unfold tailWord_3122624
  simp only [CollatzResearch.WordTrace]
  refine ⟨56945726919637012282995463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75927635892849349710660617 56945726919637012282995463)
  ·
    refine ⟨85418590379455518424493195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56945726919637012282995463 85418590379455518424493195)
    ·
      refine ⟨128127885569183277636739793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85418590379455518424493195 128127885569183277636739793)
      ·
        refine ⟨96095914176887458227554845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128127885569183277636739793 96095914176887458227554845)
        ·
          refine ⟨36035967816332796835333067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96095914176887458227554845 36035967816332796835333067)
          ·
            refine ⟨54053951724499195252999601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36035967816332796835333067 54053951724499195252999601)
            ·
              refine ⟨40540463793374396439749701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54053951724499195252999601 40540463793374396439749701)
              ·
                refine ⟨7601336961257699332453069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40540463793374396439749701 7601336961257699332453069)
                ·
                  refine ⟨2850501360471637249669901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7601336961257699332453069 2850501360471637249669901)
                  ·
                    refine ⟨1068938010176863968626213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2850501360471637249669901 1068938010176863968626213)
                    ·
                      rfl

theorem cell22_3122624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 3, 3].length) (baseStart_3122624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122624 prefixEnd_3122624 := by exact prefixLift 3122624
  have htrace : WordTrace (prefixWord ++ tailWord_3122624) baseStart_3122624 baseEnd_3122624 := by
    simpa [prefixWord, tailWord_3122624, baseEnd_3122624] using wordTrace_append hprefix tailTrace_3122624
  have hstable : (prefixWord ++ tailWord_3122624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122624).length < 2 ^ (prefixWord ++ tailWord_3122624).sum := by decide
  have hdescent : baseEnd_3122624 < baseStart_3122624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122684 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 3, 4]
def baseStart_3122684 : Nat := 118140960795 + 3122684 * 2 ^ 59
def prefixEnd_3122684 : Nat := 4983230072969 + 3 ^ 40 * 3122684 * 2
def baseEnd_3122684 : Nat := 1068958549403043812126029

theorem tailTrace_3122684 : CollatzResearch.WordTrace tailWord_3122684 prefixEnd_3122684 1068958549403043812126029 := by
  unfold tailWord_3122684
  simp only [CollatzResearch.WordTrace]
  refine ⟨56946821109528327406587553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75929094812704436542116737 56946821109528327406587553)
  ·
    refine ⟨42710115832146245554940665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56946821109528327406587553 42710115832146245554940665)
    ·
      refine ⟨32032586874109684166205499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42710115832146245554940665 32032586874109684166205499)
      ·
        refine ⟨48048880311164526249308249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32032586874109684166205499 48048880311164526249308249)
        ·
          refine ⟨36036660233373394686981187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48048880311164526249308249 36036660233373394686981187)
          ·
            refine ⟨54054990350060092030471781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36036660233373394686981187 54054990350060092030471781)
            ·
              refine ⟨10135310690636267255713459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54054990350060092030471781 10135310690636267255713459)
              ·
                refine ⟨15202966035954400883570189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10135310690636267255713459 15202966035954400883570189)
                ·
                  refine ⟨5701112263482900331338821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15202966035954400883570189 5701112263482900331338821)
                  ·
                    refine ⟨1068958549403043812126029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5701112263482900331338821 1068958549403043812126029)
                    ·
                      rfl

theorem cell22_3122684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_3122684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122684 prefixEnd_3122684 := by exact prefixLift 3122684
  have htrace : WordTrace (prefixWord ++ tailWord_3122684) baseStart_3122684 baseEnd_3122684 := by
    simpa [prefixWord, tailWord_3122684, baseEnd_3122684] using wordTrace_append hprefix tailTrace_3122684
  have hstable : (prefixWord ++ tailWord_3122684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122684).length < 2 ^ (prefixWord ++ tailWord_3122684).sum := by decide
  have hdescent : baseEnd_3122684 < baseStart_3122684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122716 : List Nat := [2, 2, 3, 1, 2, 1, 1, 6, 4]
def baseStart_3122716 : Nat := 118140960795 + 3122716 * 2 ^ 59
def prefixEnd_3122716 : Nat := 4983230072969 + 3 ^ 40 * 3122716 * 2
def baseEnd_3122716 : Nat := 356323167885668798441977

theorem tailTrace_3122716 : CollatzResearch.WordTrace tailWord_3122716 prefixEnd_3122716 356323167885668798441977 := by
  unfold tailWord_3122716
  simp only [CollatzResearch.WordTrace]
  refine ⟨56947404677470362139170001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75929872903293816185560001 56947404677470362139170001)
  ·
    refine ⟨42710553508102771604377501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56947404677470362139170001 42710553508102771604377501)
    ·
      refine ⟨16016457565538539351641563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42710553508102771604377501 16016457565538539351641563)
      ·
        refine ⟨24024686348307809027462345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16016457565538539351641563 24024686348307809027462345)
        ·
          refine ⟨18018514761230856770596759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24024686348307809027462345 18018514761230856770596759)
          ·
            refine ⟨27027772141846285155895139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18018514761230856770596759 27027772141846285155895139)
            ·
              refine ⟨40541658212769427733842709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27027772141846285155895139 40541658212769427733842709)
              ·
                refine ⟨1900390228723566925023877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40541658212769427733842709 1900390228723566925023877)
                ·
                  refine ⟨356323167885668798441977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1900390228723566925023877 356323167885668798441977)
                  ·
                    rfl

theorem cell22_3122716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_3122716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122716 prefixEnd_3122716 := by exact prefixLift 3122716
  have htrace : WordTrace (prefixWord ++ tailWord_3122716) baseStart_3122716 baseEnd_3122716 := by
    simpa [prefixWord, tailWord_3122716, baseEnd_3122716] using wordTrace_append hprefix tailTrace_3122716
  have hstable : (prefixWord ++ tailWord_3122716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122716).length < 2 ^ (prefixWord ++ tailWord_3122716).sum := by decide
  have hdescent : baseEnd_3122716 < baseStart_3122716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122744 : List Nat := [2, 1, 2, 1, 4, 3, 1, 8]
def baseStart_3122744 : Nat := 118140960795 + 3122744 * 2 ^ 59
def prefixEnd_3122744 : Nat := 4983230072969 + 3 ^ 40 * 3122744 * 2
def baseEnd_3122744 : Nat := 118775454292135961736205

theorem tailTrace_3122744 : CollatzResearch.WordTrace tailWord_3122744 prefixEnd_3122744 118775454292135961736205 := by
  unfold tailWord_3122744
  simp only [CollatzResearch.WordTrace]
  refine ⟨56947915299419642530179643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75930553732559523373572857 56947915299419642530179643)
  ·
    refine ⟨85421872949129463795269465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56947915299419642530179643 85421872949129463795269465)
    ·
      refine ⟨64066404711847097846452099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85421872949129463795269465 64066404711847097846452099)
      ·
        refine ⟨96099607067770646769678149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64066404711847097846452099 96099607067770646769678149)
        ·
          refine ⟨18018676325206996269314653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96099607067770646769678149 18018676325206996269314653)
          ·
            refine ⟨6757003621952623600992995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18018676325206996269314653 6757003621952623600992995)
            ·
              refine ⟨10135505432928935401489493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6757003621952623600992995 10135505432928935401489493)
              ·
                refine ⟨118775454292135961736205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10135505432928935401489493 118775454292135961736205)
                ·
                  rfl

theorem cell22_3122744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 8].length) (baseStart_3122744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122744 prefixEnd_3122744 := by exact prefixLift 3122744
  have htrace : WordTrace (prefixWord ++ tailWord_3122744) baseStart_3122744 baseEnd_3122744 := by
    simpa [prefixWord, tailWord_3122744, baseEnd_3122744] using wordTrace_append hprefix tailTrace_3122744
  have hstable : (prefixWord ++ tailWord_3122744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122744).length < 2 ^ (prefixWord ++ tailWord_3122744).sum := by decide
  have hdescent : baseEnd_3122744 < baseStart_3122744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122866 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_3122866 : Nat := 118140960795 + 3122866 * 2 ^ 59
def prefixEnd_3122866 : Nat := 4983230072969 + 3 ^ 40 * 3122866 * 2
def baseEnd_3122866 : Nat := 1069020851722456004075471

theorem tailTrace_3122866 : CollatzResearch.WordTrace tailWord_3122866 prefixEnd_3122866 1069020851722456004075471 := by
  unfold tailWord_3122866
  simp only [CollatzResearch.WordTrace]
  refine ⟨28475070076099324974075113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75933520202931533264200301 28475070076099324974075113)
  ·
    refine ⟨21356302557074493730556335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28475070076099324974075113 21356302557074493730556335)
    ·
      refine ⟨32034453835611740595834503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21356302557074493730556335 32034453835611740595834503)
      ·
        refine ⟨48051680753417610893751755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32034453835611740595834503 48051680753417610893751755)
        ·
          refine ⟨72077521130126416340627633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48051680753417610893751755 72077521130126416340627633)
          ·
            refine ⟨54058140847594812255470725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72077521130126416340627633 54058140847594812255470725)
            ·
              refine ⟨10135901408924027297900761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54058140847594812255470725 10135901408924027297900761)
              ·
                refine ⟨7601926056693020473425571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10135901408924027297900761 7601926056693020473425571)
                ·
                  refine ⟨11402889085039530710138357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7601926056693020473425571 11402889085039530710138357)
                  ·
                    refine ⟨1069020851722456004075471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11402889085039530710138357 1069020851722456004075471)
                    ·
                      rfl

theorem cell22_3122866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_3122866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122866 prefixEnd_3122866 := by exact prefixLift 3122866
  have htrace : WordTrace (prefixWord ++ tailWord_3122866) baseStart_3122866 baseEnd_3122866 := by
    simpa [prefixWord, tailWord_3122866, baseEnd_3122866] using wordTrace_append hprefix tailTrace_3122866
  have hstable : (prefixWord ++ tailWord_3122866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122866).length < 2 ^ (prefixWord ++ tailWord_3122866).sum := by decide
  have hdescent : baseEnd_3122866 < baseStart_3122866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122879 : List Nat := [1, 1, 2, 2, 2, 3, 11]
def baseStart_3122879 : Nat := 118140960795 + 3122879 * 2 ^ 59
def prefixEnd_3122879 : Nat := 4983230072969 + 3 ^ 40 * 3122879 * 2
def baseEnd_3122879 : Nat := 39593529699560307537053

theorem tailTrace_3122879 : CollatzResearch.WordTrace tailWord_3122879 prefixEnd_3122879 39593529699560307537053 := by
  unfold tailWord_3122879
  simp only [CollatzResearch.WordTrace]
  refine ⟨113900754453350203116523691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75933836302233468744349127 113900754453350203116523691)
  ·
    refine ⟨170851131680025304674785537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113900754453350203116523691 170851131680025304674785537)
    ·
      refine ⟨128138348760018978506089153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170851131680025304674785537 128138348760018978506089153)
      ·
        refine ⟨96103761570014233879566865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128138348760018978506089153 96103761570014233879566865)
        ·
          refine ⟨72077821177510675409675149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96103761570014233879566865 72077821177510675409675149)
          ·
            refine ⟨27029182941566503278628181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72077821177510675409675149 27029182941566503278628181)
            ·
              refine ⟨39593529699560307537053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27029182941566503278628181 39593529699560307537053)
              ·
                rfl

theorem cell22_3122879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 11].length) (baseStart_3122879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122879 prefixEnd_3122879 := by exact prefixLift 3122879
  have htrace : WordTrace (prefixWord ++ tailWord_3122879) baseStart_3122879 baseEnd_3122879 := by
    simpa [prefixWord, tailWord_3122879, baseEnd_3122879] using wordTrace_append hprefix tailTrace_3122879
  have hstable : (prefixWord ++ tailWord_3122879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122879).length < 2 ^ (prefixWord ++ tailWord_3122879).sum := by decide
  have hdescent : baseEnd_3122879 < baseStart_3122879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122900 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_3122900 : Nat := 118140960795 + 3122900 * 2 ^ 59
def prefixEnd_3122900 : Nat := 4983230072969 + 3 ^ 40 * 3122900 * 2
def baseEnd_3122900 : Nat := 1069032490617291248725367

theorem tailTrace_3122900 : CollatzResearch.WordTrace tailWord_3122900 prefixEnd_3122900 1069032490617291248725367 := by
  unfold tailWord_3122900
  simp only [CollatzResearch.WordTrace]
  refine ⟨56950760193137061851519077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75934346924182749135358769 56950760193137061851519077)
  ·
    refine ⟨10678267536213199097159827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56950760193137061851519077 10678267536213199097159827)
    ·
      refine ⟨16017401304319798645739741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10678267536213199097159827 16017401304319798645739741)
      ·
        refine ⟨6006525489119924492152403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16017401304319798645739741 6006525489119924492152403)
        ·
          refine ⟨9009788233679886738228605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6006525489119924492152403 9009788233679886738228605)
          ·
            refine ⟨3378670587629957526835727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9009788233679886738228605 3378670587629957526835727)
            ·
              refine ⟨5068005881444936290253591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3378670587629957526835727 5068005881444936290253591)
              ·
                refine ⟨7602008822167404435380387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5068005881444936290253591 7602008822167404435380387)
                ·
                  refine ⟨11403013233251106653070581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7602008822167404435380387 11403013233251106653070581)
                  ·
                    refine ⟨1069032490617291248725367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11403013233251106653070581 1069032490617291248725367)
                    ·
                      rfl

theorem cell22_3122900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_3122900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122900 prefixEnd_3122900 := by exact prefixLift 3122900
  have htrace : WordTrace (prefixWord ++ tailWord_3122900) baseStart_3122900 baseEnd_3122900 := by
    simpa [prefixWord, tailWord_3122900, baseEnd_3122900] using wordTrace_append hprefix tailTrace_3122900
  have hstable : (prefixWord ++ tailWord_3122900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122900).length < 2 ^ (prefixWord ++ tailWord_3122900).sum := by decide
  have hdescent : baseEnd_3122900 < baseStart_3122900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122919 : List Nat := [1, 1, 5, 4, 2, 1, 1, 3, 4]
def baseStart_3122919 : Nat := 118140960795 + 3122919 * 2 ^ 59
def prefixEnd_3122919 : Nat := 4983230072969 + 3 ^ 40 * 3122919 * 2
def baseEnd_3122919 : Nat := 356346331568527177500103

theorem tailTrace_3122919 : CollatzResearch.WordTrace tailWord_3122919 prefixEnd_3122919 356346331568527177500103 := by
  unfold tailWord_3122919
  simp only [CollatzResearch.WordTrace]
  refine ⟨113902213373205289947979811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75934808915470193298653207 113902213373205289947979811)
  ·
    refine ⟨170853320059807934921969717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113902213373205289947979811 170853320059807934921969717)
    ·
      refine ⟨16017498755606993898934661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170853320059807934921969717 16017498755606993898934661)
      ·
        refine ⟨3003281016676311356050249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16017498755606993898934661 3003281016676311356050249)
        ·
          refine ⟨2252460762507233517037687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3003281016676311356050249 2252460762507233517037687)
          ·
            refine ⟨3378691143760850275556531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252460762507233517037687 3378691143760850275556531)
            ·
              refine ⟨5068036715641275413334797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3378691143760850275556531 5068036715641275413334797)
              ·
                refine ⟨1900513768365478280000549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5068036715641275413334797 1900513768365478280000549)
                ·
                  refine ⟨356346331568527177500103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1900513768365478280000549 356346331568527177500103)
                  ·
                    rfl

theorem cell22_3122919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 4].length) (baseStart_3122919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122919 prefixEnd_3122919 := by exact prefixLift 3122919
  have htrace : WordTrace (prefixWord ++ tailWord_3122919) baseStart_3122919 baseEnd_3122919 := by
    simpa [prefixWord, tailWord_3122919, baseEnd_3122919] using wordTrace_append hprefix tailTrace_3122919
  have hstable : (prefixWord ++ tailWord_3122919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122919).length < 2 ^ (prefixWord ++ tailWord_3122919).sum := by decide
  have hdescent : baseEnd_3122919 < baseStart_3122919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122932 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3122932 : Nat := 118140960795 + 3122932 * 2 ^ 59
def prefixEnd_3122932 : Nat := 4983230072969 + 3 ^ 40 * 3122932 * 2
def baseEnd_3122932 : Nat := 1069043444871253831925269

theorem tailTrace_3122932 : CollatzResearch.WordTrace tailWord_3122932 prefixEnd_3122932 1069043444871253831925269 := by
  unfold tailWord_3122932
  simp only [CollatzResearch.WordTrace]
  refine ⟨56951343761079096584101525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75935125014772128778802033 56951343761079096584101525)
  ·
    refine ⟨2669594238800582652379759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56951343761079096584101525 2669594238800582652379759)
    ·
      refine ⟨4004391358200873978569639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2669594238800582652379759 4004391358200873978569639)
      ·
        refine ⟨6006587037301310967854459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4004391358200873978569639 6006587037301310967854459)
        ·
          refine ⟨9009880555951966451781689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6006587037301310967854459 9009880555951966451781689)
          ·
            refine ⟨6757410416963974838836267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9009880555951966451781689 6757410416963974838836267)
            ·
              refine ⟨10136115625445962258254401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6757410416963974838836267 10136115625445962258254401)
              ·
                refine ⟨7602086719084471693690801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10136115625445962258254401 7602086719084471693690801)
                ·
                  refine ⟨5701565039313353770268101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7602086719084471693690801 5701565039313353770268101)
                  ·
                    refine ⟨1069043444871253831925269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5701565039313353770268101 1069043444871253831925269)
                    ·
                      rfl

theorem cell22_3122932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3122932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122932 prefixEnd_3122932 := by exact prefixLift 3122932
  have htrace : WordTrace (prefixWord ++ tailWord_3122932) baseStart_3122932 baseEnd_3122932 := by
    simpa [prefixWord, tailWord_3122932, baseEnd_3122932] using wordTrace_append hprefix tailTrace_3122932
  have hstable : (prefixWord ++ tailWord_3122932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122932).length < 2 ^ (prefixWord ++ tailWord_3122932).sum := by decide
  have hdescent : baseEnd_3122932 < baseStart_3122932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122945 : List Nat := [1, 2, 4, 1, 1, 1, 2, 6, 1, 3]
def baseStart_3122945 : Nat := 118140960795 + 3122945 * 2 ^ 59
def prefixEnd_3122945 : Nat := 4983230072969 + 3 ^ 40 * 3122945 * 2
def baseEnd_3122945 : Nat := 1069047895036926131350229

theorem tailTrace_3122945 : CollatzResearch.WordTrace tailWord_3122945 prefixEnd_3122945 1069047895036926131350229 := by
  unfold tailWord_3122945
  simp only [CollatzResearch.WordTrace]
  refine ⟨113903161671111096388426289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75935441114074064258950859 113903161671111096388426289)
  ·
    refine ⟨85427371253333322291319717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113903161671111096388426289 85427371253333322291319717)
    ·
      refine ⟨16017632109999997929622447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85427371253333322291319717 16017632109999997929622447)
      ·
        refine ⟨24026448164999996894433671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16017632109999997929622447 24026448164999996894433671)
        ·
          refine ⟨36039672247499995341650507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24026448164999996894433671 36039672247499995341650507)
          ·
            refine ⟨54059508371249993012475761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36039672247499995341650507 54059508371249993012475761)
            ·
              refine ⟨40544631278437494759356821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54059508371249993012475761 40544631278437494759356821)
              ·
                refine ⟨1900529591176757566844851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40544631278437494759356821 1900529591176757566844851)
                ·
                  refine ⟨2850794386765136350267277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1900529591176757566844851 2850794386765136350267277)
                  ·
                    refine ⟨1069047895036926131350229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2850794386765136350267277 1069047895036926131350229)
                    ·
                      rfl

theorem cell22_3122945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_3122945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122945 prefixEnd_3122945 := by exact prefixLift 3122945
  have htrace : WordTrace (prefixWord ++ tailWord_3122945) baseStart_3122945 baseEnd_3122945 := by
    simpa [prefixWord, tailWord_3122945, baseEnd_3122945] using wordTrace_append hprefix tailTrace_3122945
  have hstable : (prefixWord ++ tailWord_3122945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122945).length < 2 ^ (prefixWord ++ tailWord_3122945).sum := by decide
  have hdescent : baseEnd_3122945 < baseStart_3122945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122956 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 2, 5]
def baseStart_3122956 : Nat := 118140960795 + 3122956 * 2 ^ 59
def prefixEnd_3122956 : Nat := 4983230072969 + 3 ^ 40 * 3122956 * 2
def baseEnd_3122956 : Nat := 1069051660561725769325195

theorem tailTrace_3122956 : CollatzResearch.WordTrace tailWord_3122956 prefixEnd_3122956 1069051660561725769325195 := by
  unfold tailWord_3122956
  simp only [CollatzResearch.WordTrace]
  refine ⟨56951781437035622633538361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75935708582714163511384481 56951781437035622633538361)
  ·
    refine ⟨42713836077776716975153771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56951781437035622633538361 42713836077776716975153771)
    ·
      refine ⟨64070754116665075462730657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42713836077776716975153771 64070754116665075462730657)
      ·
        refine ⟨48053065587498806597047993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64070754116665075462730657 48053065587498806597047993)
        ·
          refine ⟨36039799190624104947785995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48053065587498806597047993 36039799190624104947785995)
          ·
            refine ⟨54059698785936157421678993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36039799190624104947785995 54059698785936157421678993)
            ·
              refine ⟨40544774089452118066259245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54059698785936157421678993 40544774089452118066259245)
              ·
                refine ⟨15204290283544544274847217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40544774089452118066259245 15204290283544544274847217)
                ·
                  refine ⟨11403217712658408206135413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15204290283544544274847217 11403217712658408206135413)
                  ·
                    refine ⟨1069051660561725769325195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11403217712658408206135413 1069051660561725769325195)
                    ·
                      rfl

theorem cell22_3122956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_3122956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122956 prefixEnd_3122956 := by exact prefixLift 3122956
  have htrace : WordTrace (prefixWord ++ tailWord_3122956) baseStart_3122956 baseEnd_3122956 := by
    simpa [prefixWord, tailWord_3122956, baseEnd_3122956] using wordTrace_append hprefix tailTrace_3122956
  have hstable : (prefixWord ++ tailWord_3122956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122956).length < 2 ^ (prefixWord ++ tailWord_3122956).sum := by decide
  have hdescent : baseEnd_3122956 < baseStart_3122956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122971 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 3, 4]
def baseStart_3122971 : Nat := 118140960795 + 3122971 * 2 ^ 59
def prefixEnd_3122971 : Nat := 4983230072969 + 3 ^ 40 * 3122971 * 2
def baseEnd_3122971 : Nat := 1069056795368270730200149

theorem tailTrace_3122971 : CollatzResearch.WordTrace tailWord_3122971 prefixEnd_3122971 1069056795368270730200149 := by
  unfold tailWord_3122971
  simp only [CollatzResearch.WordTrace]
  refine ⟨113904109969016902828872767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75936073312677935219248511 113904109969016902828872767)
  ·
    refine ⟨170856164953525354243309151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113904109969016902828872767 170856164953525354243309151)
    ·
      refine ⟨256284247430288031364963727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170856164953525354243309151 256284247430288031364963727)
      ·
        refine ⟨384426371145432047047445591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256284247430288031364963727 384426371145432047047445591)
        ·
          refine ⟨576639556718148070571168387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384426371145432047047445591 576639556718148070571168387)
          ·
            refine ⟨864959335077222105856752581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576639556718148070571168387 864959335077222105856752581)
            ·
              refine ⟨162179875326979144848141109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 864959335077222105856752581 162179875326979144848141109)
              ·
                refine ⟨15204363311904294829513229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162179875326979144848141109 15204363311904294829513229)
                ·
                  refine ⟨5701636241964110561067461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15204363311904294829513229 5701636241964110561067461)
                  ·
                    refine ⟨1069056795368270730200149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5701636241964110561067461 1069056795368270730200149)
                    ·
                      rfl

theorem cell22_3122971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 4].length) (baseStart_3122971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122971 prefixEnd_3122971 := by exact prefixLift 3122971
  have htrace : WordTrace (prefixWord ++ tailWord_3122971) baseStart_3122971 baseEnd_3122971 := by
    simpa [prefixWord, tailWord_3122971, baseEnd_3122971] using wordTrace_append hprefix tailTrace_3122971
  have hstable : (prefixWord ++ tailWord_3122971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122971).length < 2 ^ (prefixWord ++ tailWord_3122971).sum := by decide
  have hdescent : baseEnd_3122971 < baseStart_3122971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122996 : List Nat := [2, 5, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_3122996 : Nat := 118140960795 + 3122996 * 2 ^ 59
def prefixEnd_3122996 : Nat := 4983230072969 + 3 ^ 40 * 3122996 * 2
def baseEnd_3122996 : Nat := 1069065353379178998325073

theorem tailTrace_3122996 : CollatzResearch.WordTrace tailWord_3122996 prefixEnd_3122996 1069065353379178998325073 := by
  unfold tailWord_3122996
  simp only [CollatzResearch.WordTrace]
  refine ⟨56952510896963166049266421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75936681195950888065688561 56952510896963166049266421)
  ·
    refine ⟨5339297896590296817118727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56952510896963166049266421 5339297896590296817118727)
    ·
      refine ⟨8008946844885445225678091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5339297896590296817118727 8008946844885445225678091)
      ·
        refine ⟨12013420267328167838517137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8008946844885445225678091 12013420267328167838517137)
        ·
          refine ⟨9010065200496125878887853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12013420267328167838517137 9010065200496125878887853)
          ·
            refine ⟨3378774450186047204582945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9010065200496125878887853 3378774450186047204582945)
            ·
              refine ⟨2534080837639535403437209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3378774450186047204582945 2534080837639535403437209)
              ·
                refine ⟨1900560628229651552577907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2534080837639535403437209 1900560628229651552577907)
                ·
                  refine ⟨2850840942344477328866861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1900560628229651552577907 2850840942344477328866861)
                  ·
                    refine ⟨1069065353379178998325073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2850840942344477328866861 1069065353379178998325073)
                    ·
                      rfl

theorem cell22_3122996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_3122996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3122996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3122996 prefixEnd_3122996 := by exact prefixLift 3122996
  have htrace : WordTrace (prefixWord ++ tailWord_3122996) baseStart_3122996 baseEnd_3122996 := by
    simpa [prefixWord, tailWord_3122996, baseEnd_3122996] using wordTrace_append hprefix tailTrace_3122996
  have hstable : (prefixWord ++ tailWord_3122996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122996).length < 2 ^ (prefixWord ++ tailWord_3122996).sum := by decide
  have hdescent : baseEnd_3122996 < baseStart_3122996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123018 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 1, 5]
def baseStart_3123018 : Nat := 118140960795 + 3123018 * 2 ^ 59
def prefixEnd_3123018 : Nat := 4983230072969 + 3 ^ 40 * 3123018 * 2
def baseEnd_3123018 : Nat := 1069072884428778274275005

theorem tailTrace_3123018 : CollatzResearch.WordTrace tailWord_3123018 prefixEnd_3123018 1069072884428778274275005 := by
  unfold tailWord_3123018
  simp only [CollatzResearch.WordTrace]
  refine ⟨28476456049961657463958427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75937216133231086570555805 28476456049961657463958427)
  ·
    refine ⟨42714684074942486195937641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28476456049961657463958427 42714684074942486195937641)
    ·
      refine ⟨32036013056206864646953231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42714684074942486195937641 32036013056206864646953231)
      ·
        refine ⟨48054019584310296970429847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32036013056206864646953231 48054019584310296970429847)
        ·
          refine ⟨72081029376465445455644771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48054019584310296970429847 72081029376465445455644771)
          ·
            refine ⟨108121544064698168183467157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72081029376465445455644771 108121544064698168183467157)
            ·
              refine ⟨5068197378032726633600023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108121544064698168183467157 5068197378032726633600023)
              ·
                refine ⟨7602296067049089950400035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5068197378032726633600023 7602296067049089950400035)
                ·
                  refine ⟨11403444100573634925600053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7602296067049089950400035 11403444100573634925600053)
                  ·
                    refine ⟨1069072884428778274275005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11403444100573634925600053 1069072884428778274275005)
                    ·
                      rfl

theorem cell22_3123018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_3123018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123018 prefixEnd_3123018 := by exact prefixLift 3123018
  have htrace : WordTrace (prefixWord ++ tailWord_3123018) baseStart_3123018 baseEnd_3123018 := by
    simpa [prefixWord, tailWord_3123018, baseEnd_3123018] using wordTrace_append hprefix tailTrace_3123018
  have hstable : (prefixWord ++ tailWord_3123018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123018).length < 2 ^ (prefixWord ++ tailWord_3123018).sum := by decide
  have hdescent : baseEnd_3123018 < baseStart_3123018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123052 : List Nat := [2, 2, 1, 1, 4, 4, 1, 2, 2, 3]
def baseStart_3123052 : Nat := 118140960795 + 3123052 * 2 ^ 59
def prefixEnd_3123052 : Nat := 4983230072969 + 3 ^ 40 * 3123052 * 2
def baseEnd_3123052 : Nat := 1069084523323613518924901

theorem tailTrace_3123052 : CollatzResearch.WordTrace tailWord_3123052 prefixEnd_3123052 1069084523323613518924901 := by
  unfold tailWord_3123052
  simp only [CollatzResearch.WordTrace]
  refine ⟨56953532140861726831285705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75938042854482302441714273 56953532140861726831285705)
  ·
    refine ⟨42715149105646295123464279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56953532140861726831285705 42715149105646295123464279)
    ·
      refine ⟨64072723658469442685196419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42715149105646295123464279 64072723658469442685196419)
      ·
        refine ⟨96109085487704164027794629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64072723658469442685196419 96109085487704164027794629)
        ·
          refine ⟨18020453528944530755211493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96109085487704164027794629 18020453528944530755211493)
          ·
            refine ⟨3378835036677099516602155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18020453528944530755211493 3378835036677099516602155)
            ·
              refine ⟨5068252555015649274903233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3378835036677099516602155 5068252555015649274903233)
              ·
                refine ⟨3801189416261736956177425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5068252555015649274903233 3801189416261736956177425)
                ·
                  refine ⟨2850892062196302717133069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3801189416261736956177425 2850892062196302717133069)
                  ·
                    refine ⟨1069084523323613518924901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2850892062196302717133069 1069084523323613518924901)
                    ·
                      rfl

theorem cell22_3123052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_3123052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123052 prefixEnd_3123052 := by exact prefixLift 3123052
  have htrace : WordTrace (prefixWord ++ tailWord_3123052) baseStart_3123052 baseEnd_3123052 := by
    simpa [prefixWord, tailWord_3123052, baseEnd_3123052] using wordTrace_append hprefix tailTrace_3123052
  have hstable : (prefixWord ++ tailWord_3123052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123052).length < 2 ^ (prefixWord ++ tailWord_3123052).sum := by decide
  have hdescent : baseEnd_3123052 < baseStart_3123052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123082 : List Nat := [3, 1, 2, 4, 2, 2, 2, 6]
def baseStart_3123082 : Nat := 118140960795 + 3123082 * 2 ^ 59
def prefixEnd_3123082 : Nat := 4983230072969 + 3 ^ 40 * 3123082 * 2
def baseEnd_3123082 : Nat := 118788310326300382297201

theorem tailTrace_3123082 : CollatzResearch.WordTrace tailWord_3123082 prefixEnd_3123082 118788310326300382297201 := by
  unfold tailWord_3123082
  simp only [CollatzResearch.WordTrace]
  refine ⟨28477039617903692196540875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75938772314409845857442333 28477039617903692196540875)
  ·
    refine ⟨42715559426855538294811313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28477039617903692196540875 42715559426855538294811313)
    ·
      refine ⟨32036669570141653721108485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42715559426855538294811313 32036669570141653721108485)
      ·
        refine ⟨6006875544401560072707841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32036669570141653721108485 6006875544401560072707841)
        ·
          refine ⟨4505156658301170054530881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6006875544401560072707841 4505156658301170054530881)
          ·
            refine ⟨3378867493725877540898161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4505156658301170054530881 3378867493725877540898161)
            ·
              refine ⟨2534150620294408155673621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3378867493725877540898161 2534150620294408155673621)
              ·
                refine ⟨118788310326300382297201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2534150620294408155673621 118788310326300382297201)
                ·
                  rfl

theorem cell22_3123082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 6].length) (baseStart_3123082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123082 prefixEnd_3123082 := by exact prefixLift 3123082
  have htrace : WordTrace (prefixWord ++ tailWord_3123082) baseStart_3123082 baseEnd_3123082 := by
    simpa [prefixWord, tailWord_3123082, baseEnd_3123082] using wordTrace_append hprefix tailTrace_3123082
  have hstable : (prefixWord ++ tailWord_3123082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123082).length < 2 ^ (prefixWord ++ tailWord_3123082).sum := by decide
  have hdescent : baseEnd_3123082 < baseStart_3123082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123097 : List Nat := [1, 2, 1, 2, 1, 3, 5, 3, 1, 3]
def baseStart_3123097 : Nat := 118140960795 + 3123097 * 2 ^ 59
def prefixEnd_3123097 : Nat := 4983230072969 + 3 ^ 40 * 3123097 * 2
def baseEnd_3123097 : Nat := 1069099927743248401549763

theorem tailTrace_3123097 : CollatzResearch.WordTrace tailWord_3123097 prefixEnd_3123097 1069099927743248401549763 := by
  unfold tailWord_3123097
  simp only [CollatzResearch.WordTrace]
  refine ⟨113908705566560426347959545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75939137044373617565306363 113908705566560426347959545)
  ·
    refine ⟨85431529174920319760969659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113908705566560426347959545 85431529174920319760969659)
    ·
      refine ⟨128147293762380479641454489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85431529174920319760969659 128147293762380479641454489)
      ·
        refine ⟨96110470321785359731090867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128147293762380479641454489 96110470321785359731090867)
        ·
          refine ⟨144165705482678039596636301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96110470321785359731090867 144165705482678039596636301)
          ·
            refine ⟨54062139556004264848738613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144165705482678039596636301 54062139556004264848738613)
            ·
              refine ⟨5068325583375399829569245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54062139556004264848738613 5068325583375399829569245)
              ·
                refine ⟨1900622093765774936088467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5068325583375399829569245 1900622093765774936088467)
                ·
                  refine ⟨2850933140648662404132701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1900622093765774936088467 2850933140648662404132701)
                  ·
                    refine ⟨1069099927743248401549763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2850933140648662404132701 1069099927743248401549763)
                    ·
                      rfl

theorem cell22_3123097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 1, 3].length) (baseStart_3123097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123097 prefixEnd_3123097 := by exact prefixLift 3123097
  have htrace : WordTrace (prefixWord ++ tailWord_3123097) baseStart_3123097 baseEnd_3123097 := by
    simpa [prefixWord, tailWord_3123097, baseEnd_3123097] using wordTrace_append hprefix tailTrace_3123097
  have hstable : (prefixWord ++ tailWord_3123097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123097).length < 2 ^ (prefixWord ++ tailWord_3123097).sum := by decide
  have hdescent : baseEnd_3123097 < baseStart_3123097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123123 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 3, 4]
def baseStart_3123123 : Nat := 118140960795 + 3123123 * 2 ^ 59
def prefixEnd_3123123 : Nat := 4983230072969 + 3 ^ 40 * 3123123 * 2
def baseEnd_3123123 : Nat := 1069108828074593000399683

theorem tailTrace_3123123 : CollatzResearch.WordTrace tailWord_3123123 prefixEnd_3123123 1069108828074593000399683 := by
  unfold tailWord_3123123
  simp only [CollatzResearch.WordTrace]
  refine ⟨113909653864466232788406023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75939769242977488525604015 113909653864466232788406023)
  ·
    refine ⟨170864480796699349182609035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113909653864466232788406023 170864480796699349182609035)
    ·
      refine ⟨256296721195049023773913553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170864480796699349182609035 256296721195049023773913553)
      ·
        refine ⟨192222540896286767830435165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256296721195049023773913553 192222540896286767830435165)
        ·
          refine ⟨72083452836107537936413187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192222540896286767830435165 72083452836107537936413187)
          ·
            refine ⟨108125179254161306904619781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72083452836107537936413187 108125179254161306904619781)
            ·
              refine ⟨20273471110155245044616209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108125179254161306904619781 20273471110155245044616209)
              ·
                refine ⟨15205103332616433783462157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20273471110155245044616209 15205103332616433783462157)
                ·
                  refine ⟨5701913749731162668798309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15205103332616433783462157 5701913749731162668798309)
                  ·
                    refine ⟨1069108828074593000399683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5701913749731162668798309 1069108828074593000399683)
                    ·
                      rfl

theorem cell22_3123123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 4].length) (baseStart_3123123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123123 prefixEnd_3123123 := by exact prefixLift 3123123
  have htrace : WordTrace (prefixWord ++ tailWord_3123123) baseStart_3123123 baseEnd_3123123 := by
    simpa [prefixWord, tailWord_3123123, baseEnd_3123123] using wordTrace_append hprefix tailTrace_3123123
  have hstable : (prefixWord ++ tailWord_3123123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123123).length < 2 ^ (prefixWord ++ tailWord_3123123).sum := by decide
  have hdescent : baseEnd_3123123 < baseStart_3123123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123221 : List Nat := [1, 3, 2, 1, 6, 1, 1, 2, 2, 3]
def baseStart_3123221 : Nat := 118140960795 + 3123221 * 2 ^ 59
def prefixEnd_3123221 : Nat := 4983230072969 + 3 ^ 40 * 3123221 * 2
def baseEnd_3123221 : Nat := 1069142375477353411449383

theorem tailTrace_3123221 : CollatzResearch.WordTrace tailWord_3123221 prefixEnd_3123221 1069142375477353411449383 := by
  unfold tailWord_3123221
  simp only [CollatzResearch.WordTrace]
  refine ⟨113913228218111195525473517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75942152145407463683649011 113913228218111195525473517)
  ·
    refine ⟨42717460581791698322052569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113913228218111195525473517 42717460581791698322052569)
    ·
      refine ⟨32038095436343773741539427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42717460581791698322052569 32038095436343773741539427)
      ·
        refine ⟨48057143154515660612309141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32038095436343773741539427 48057143154515660612309141)
        ·
          refine ⟨2252678585367921591201991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48057143154515660612309141 2252678585367921591201991)
          ·
            refine ⟨3379017878051882386802987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252678585367921591201991 3379017878051882386802987)
            ·
              refine ⟨5068526817077823580204481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379017878051882386802987 5068526817077823580204481)
              ·
                refine ⟨3801395112808367685153361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5068526817077823580204481 3801395112808367685153361)
                ·
                  refine ⟨2851046334606275763865021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3801395112808367685153361 2851046334606275763865021)
                  ·
                    refine ⟨1069142375477353411449383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2851046334606275763865021 1069142375477353411449383)
                    ·
                      rfl

theorem cell22_3123221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_3123221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123221 prefixEnd_3123221 := by exact prefixLift 3123221
  have htrace : WordTrace (prefixWord ++ tailWord_3123221) baseStart_3123221 baseEnd_3123221 := by
    simpa [prefixWord, tailWord_3123221, baseEnd_3123221] using wordTrace_append hprefix tailTrace_3123221
  have hstable : (prefixWord ++ tailWord_3123221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123221).length < 2 ^ (prefixWord ++ tailWord_3123221).sum := by decide
  have hdescent : baseEnd_3123221 < baseStart_3123221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123243 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 1, 7]
def baseStart_3123243 : Nat := 118140960795 + 3123243 * 2 ^ 59
def prefixEnd_3123243 : Nat := 4983230072969 + 3 ^ 40 * 3123243 * 2
def baseEnd_3123243 : Nat := 1069149906526952687399315

theorem tailTrace_3123243 : CollatzResearch.WordTrace tailWord_3123243 prefixEnd_3123243 1069149906526952687399315 := by
  unfold tailWord_3123243
  simp only [CollatzResearch.WordTrace]
  refine ⟨113914030624031493282774383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75942687082687662188516255 113914030624031493282774383)
  ·
    refine ⟨170871045936047239924161575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113914030624031493282774383 170871045936047239924161575)
    ·
      refine ⟨256306568904070859886242363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170871045936047239924161575 256306568904070859886242363)
      ·
        refine ⟨384459853356106289829363545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256306568904070859886242363 384459853356106289829363545)
        ·
          refine ⟨288344890017079717372022659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384459853356106289829363545 288344890017079717372022659)
          ·
            refine ⟨432517335025619576058033989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288344890017079717372022659 432517335025619576058033989)
            ·
              refine ⟨81097000317303670510881373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 432517335025619576058033989 81097000317303670510881373)
              ·
                refine ⟨30411375118988876441580515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81097000317303670510881373 30411375118988876441580515)
                ·
                  refine ⟨45617062678483314662370773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30411375118988876441580515 45617062678483314662370773)
                  ·
                    refine ⟨1069149906526952687399315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45617062678483314662370773 1069149906526952687399315)
                    ·
                      rfl

theorem cell22_3123243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 7].length) (baseStart_3123243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123243 prefixEnd_3123243 := by exact prefixLift 3123243
  have htrace : WordTrace (prefixWord ++ tailWord_3123243) baseStart_3123243 baseEnd_3123243 := by
    simpa [prefixWord, tailWord_3123243, baseEnd_3123243] using wordTrace_append hprefix tailTrace_3123243
  have hstable : (prefixWord ++ tailWord_3123243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123243).length < 2 ^ (prefixWord ++ tailWord_3123243).sum := by decide
  have hdescent : baseEnd_3123243 < baseStart_3123243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123305 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 1, 5]
def baseStart_3123305 : Nat := 118140960795 + 3123305 * 2 ^ 59
def prefixEnd_3123305 : Nat := 4983230072969 + 3 ^ 40 * 3123305 * 2
def baseEnd_3123305 : Nat := 1069171130394005192349125

theorem tailTrace_3123305 : CollatzResearch.WordTrace tailWord_3123305 prefixEnd_3123305 1069171130394005192349125 := by
  unfold tailWord_3123305
  simp only [CollatzResearch.WordTrace]
  refine ⟨113916291949806877871531369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75944194633204585247687579 113916291949806877871531369)
  ·
    refine ⟨85437218962355158403648527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113916291949806877871531369 85437218962355158403648527)
    ·
      refine ⟨128155828443532737605472791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85437218962355158403648527 128155828443532737605472791)
      ·
        refine ⟨192233742665299106408209187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128155828443532737605472791 192233742665299106408209187)
        ·
          refine ⟨288350613997948659612313781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192233742665299106408209187 288350613997948659612313781)
          ·
            refine ⟨27032870062307686838654417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 288350613997948659612313781 27032870062307686838654417)
            ·
              refine ⟨20274652546730765128990813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27032870062307686838654417 20274652546730765128990813)
              ·
                refine ⟨7602994705024036923371555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20274652546730765128990813 7602994705024036923371555)
                ·
                  refine ⟨11404492057536055385057333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7602994705024036923371555 11404492057536055385057333)
                  ·
                    refine ⟨1069171130394005192349125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11404492057536055385057333 1069171130394005192349125)
                    ·
                      rfl

theorem cell22_3123305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_3123305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123305 prefixEnd_3123305 := by exact prefixLift 3123305
  have htrace : WordTrace (prefixWord ++ tailWord_3123305) baseStart_3123305 baseEnd_3123305 := by
    simpa [prefixWord, tailWord_3123305, baseEnd_3123305] using wordTrace_append hprefix tailTrace_3123305
  have hstable : (prefixWord ++ tailWord_3123305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123305).length < 2 ^ (prefixWord ++ tailWord_3123305).sum := by decide
  have hdescent : baseEnd_3123305 < baseStart_3123305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123365 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 2, 6]
def baseStart_3123365 : Nat := 118140960795 + 3123365 * 2 ^ 59
def prefixEnd_3123365 : Nat := 4983230072969 + 3 ^ 40 * 3123365 * 2
def baseEnd_3123365 : Nat := 1069191669620185035848941

theorem tailTrace_3123365 : CollatzResearch.WordTrace tailWord_3123365 prefixEnd_3123365 1069191669620185035848941 := by
  unfold tailWord_3123365
  simp only [CollatzResearch.WordTrace]
  refine ⟨113918480329589508118715549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75945653553059672079143699 113918480329589508118715549)
  ·
    refine ⟨42719430123596065544518331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113918480329589508118715549 42719430123596065544518331)
    ·
      refine ⟨64079145185394098316777497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42719430123596065544518331 64079145185394098316777497)
      ·
        refine ⟨48059358889045573737583123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64079145185394098316777497 48059358889045573737583123)
        ·
          refine ⟨72089038333568360606374685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48059358889045573737583123 72089038333568360606374685)
          ·
            refine ⟨27033389375088135227390507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72089038333568360606374685 27033389375088135227390507)
            ·
              refine ⟨40550084062632202841085761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27033389375088135227390507 40550084062632202841085761)
              ·
                refine ⟨30412563046974152130814321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40550084062632202841085761 30412563046974152130814321)
                ·
                  refine ⟨22809422285230614098110741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30412563046974152130814321 22809422285230614098110741)
                  ·
                    refine ⟨1069191669620185035848941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22809422285230614098110741 1069191669620185035848941)
                    ·
                      rfl

theorem cell22_3123365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_3123365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123365 prefixEnd_3123365 := by exact prefixLift 3123365
  have htrace : WordTrace (prefixWord ++ tailWord_3123365) baseStart_3123365 baseEnd_3123365 := by
    simpa [prefixWord, tailWord_3123365, baseEnd_3123365] using wordTrace_append hprefix tailTrace_3123365
  have hstable : (prefixWord ++ tailWord_3123365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123365).length < 2 ^ (prefixWord ++ tailWord_3123365).sum := by decide
  have hdescent : baseEnd_3123365 < baseStart_3123365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123397 : List Nat := [1, 3, 1, 1, 1, 1, 7, 2, 5]
def baseStart_3123397 : Nat := 118140960795 + 3123397 * 2 ^ 59
def prefixEnd_3123397 : Nat := 4983230072969 + 3 ^ 40 * 3123397 * 2
def baseEnd_3123397 : Nat := 356400874624715873016281

theorem tailTrace_3123397 : CollatzResearch.WordTrace tailWord_3123397 prefixEnd_3123397 356400874624715873016281 := by
  unfold tailWord_3123397
  simp only [CollatzResearch.WordTrace]
  refine ⟨113919647465473577583880445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75946431643649051722586963 113919647465473577583880445)
  ·
    refine ⟨42719867799552591593955167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113919647465473577583880445 42719867799552591593955167)
    ·
      refine ⟨64079801699328887390932751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42719867799552591593955167 64079801699328887390932751)
      ·
        refine ⟨96119702548993331086399127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64079801699328887390932751 96119702548993331086399127)
        ·
          refine ⟨144179553823489996629598691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96119702548993331086399127 144179553823489996629598691)
          ·
            refine ⟨216269330735234994944398037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144179553823489996629598691 216269330735234994944398037)
            ·
              refine ⟨5068812439107070194009329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 216269330735234994944398037 5068812439107070194009329)
              ·
                refine ⟨3801609329330302645506997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5068812439107070194009329 3801609329330302645506997)
                ·
                  refine ⟨356400874624715873016281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3801609329330302645506997 356400874624715873016281)
                  ·
                    rfl

theorem cell22_3123397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_3123397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123397 prefixEnd_3123397 := by exact prefixLift 3123397
  have htrace : WordTrace (prefixWord ++ tailWord_3123397) baseStart_3123397 baseEnd_3123397 := by
    simpa [prefixWord, tailWord_3123397, baseEnd_3123397] using wordTrace_append hprefix tailTrace_3123397
  have hstable : (prefixWord ++ tailWord_3123397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123397).length < 2 ^ (prefixWord ++ tailWord_3123397).sum := by decide
  have hdescent : baseEnd_3123397 < baseStart_3123397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123487 : List Nat := [1, 1, 2, 4, 3, 1, 2, 8]
def baseStart_3123487 : Nat := 118140960795 + 3123487 * 2 ^ 59
def prefixEnd_3123487 : Nat := 4983230072969 + 3 ^ 40 * 3123487 * 2
def baseEnd_3123487 : Nat := 118803714745935264922063

theorem tailTrace_3123487 : CollatzResearch.WordTrace tailWord_3123487 prefixEnd_3123487 118803714745935264922063 := by
  unfold tailWord_3123487
  simp only [CollatzResearch.WordTrace]
  refine ⟨113922930035147522954656715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75948620023431681969771143 113922930035147522954656715)
  ·
    refine ⟨170884395052721284431985073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113922930035147522954656715 170884395052721284431985073)
    ·
      refine ⟨128163296289540963323988805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170884395052721284431985073 128163296289540963323988805)
      ·
        refine ⟨24030618054288930623247901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128163296289540963323988805 24030618054288930623247901)
        ·
          refine ⟨9011481770358348983717963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24030618054288930623247901 9011481770358348983717963)
          ·
            refine ⟨13517222655537523475576945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9011481770358348983717963 13517222655537523475576945)
            ·
              refine ⟨10137916991653142606682709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13517222655537523475576945 10137916991653142606682709)
              ·
                refine ⟨118803714745935264922063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10137916991653142606682709 118803714745935264922063)
                ·
                  rfl

theorem cell22_3123487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 8].length) (baseStart_3123487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123487 prefixEnd_3123487 := by exact prefixLift 3123487
  have htrace : WordTrace (prefixWord ++ tailWord_3123487) baseStart_3123487 baseEnd_3123487 := by
    simpa [prefixWord, tailWord_3123487, baseEnd_3123487] using wordTrace_append hprefix tailTrace_3123487
  have hstable : (prefixWord ++ tailWord_3123487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123487).length < 2 ^ (prefixWord ++ tailWord_3123487).sum := by decide
  have hdescent : baseEnd_3123487 < baseStart_3123487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123508 : List Nat := [2, 5, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_3123508 : Nat := 118140960795 + 3123508 * 2 ^ 59
def prefixEnd_3123508 : Nat := 4983230072969 + 3 ^ 40 * 3123508 * 2
def baseEnd_3123508 : Nat := 1069240621442580329523503

theorem tailTrace_3123508 : CollatzResearch.WordTrace tailWord_3123508 prefixEnd_3123508 1069240621442580329523503 := by
  unfold tailWord_3123508
  simp only [CollatzResearch.WordTrace]
  refine ⟨56961847984035721770585589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75949130645380962360780785 56961847984035721770585589)
  ·
    refine ⟨5340173248503348915992399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56961847984035721770585589 5340173248503348915992399)
    ·
      refine ⟨8010259872755023373988599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5340173248503348915992399 8010259872755023373988599)
      ·
        refine ⟨12015389809132535060982899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8010259872755023373988599 12015389809132535060982899)
        ·
          refine ⟨18023084713698802591474349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12015389809132535060982899 18023084713698802591474349)
          ·
            refine ⟨6758656767637050971802881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18023084713698802591474349 6758656767637050971802881)
            ·
              refine ⟨5068992575727788228852161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6758656767637050971802881 5068992575727788228852161)
              ·
                refine ⟨3801744431795841171639121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5068992575727788228852161 3801744431795841171639121)
                ·
                  refine ⟨2851308323846880878729341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3801744431795841171639121 2851308323846880878729341)
                  ·
                    refine ⟨1069240621442580329523503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2851308323846880878729341 1069240621442580329523503)
                    ·
                      rfl

theorem cell22_3123508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_3123508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123508 prefixEnd_3123508 := by exact prefixLift 3123508
  have htrace : WordTrace (prefixWord ++ tailWord_3123508) baseStart_3123508 baseEnd_3123508 := by
    simpa [prefixWord, tailWord_3123508, baseEnd_3123508] using wordTrace_append hprefix tailTrace_3123508
  have hstable : (prefixWord ++ tailWord_3123508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123508).length < 2 ^ (prefixWord ++ tailWord_3123508).sum := by decide
  have hdescent : baseEnd_3123508 < baseStart_3123508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123519 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 3, 3]
def baseStart_3123519 : Nat := 118140960795 + 3123519 * 2 ^ 59
def prefixEnd_3123519 : Nat := 4983230072969 + 3 ^ 40 * 3123519 * 2
def baseEnd_3123519 : Nat := 1069244386967379967498469

theorem tailTrace_3123519 : CollatzResearch.WordTrace tailWord_3123519 prefixEnd_3123519 1069244386967379967498469 := by
  unfold tailWord_3123519
  simp only [CollatzResearch.WordTrace]
  refine ⟨113924097171031592419821611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75949398114021061613214407 113924097171031592419821611)
  ·
    refine ⟨170886145756547388629732417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113924097171031592419821611 170886145756547388629732417)
    ·
      refine ⟨128164609317410541472299313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170886145756547388629732417 128164609317410541472299313)
      ·
        refine ⟨96123456988057906104224485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128164609317410541472299313 96123456988057906104224485)
        ·
          refine ⟨18023148185260857394542091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96123456988057906104224485 18023148185260857394542091)
          ·
            refine ⟨27034722277891286091813137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18023148185260857394542091 27034722277891286091813137)
            ·
              refine ⟨20276041708418464568859853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27034722277891286091813137 20276041708418464568859853)
              ·
                refine ⟨7603515640656924213322445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20276041708418464568859853 7603515640656924213322445)
                ·
                  refine ⟨2851318365246346579995917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7603515640656924213322445 2851318365246346579995917)
                  ·
                    refine ⟨1069244386967379967498469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2851318365246346579995917 1069244386967379967498469)
                    ·
                      rfl

theorem cell22_3123519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 3].length) (baseStart_3123519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123519 prefixEnd_3123519 := by exact prefixLift 3123519
  have htrace : WordTrace (prefixWord ++ tailWord_3123519) baseStart_3123519 baseEnd_3123519 := by
    simpa [prefixWord, tailWord_3123519, baseEnd_3123519] using wordTrace_append hprefix tailTrace_3123519
  have hstable : (prefixWord ++ tailWord_3123519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123519).length < 2 ^ (prefixWord ++ tailWord_3123519).sum := by decide
  have hdescent : baseEnd_3123519 < baseStart_3123519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123521 : List Nat := [1, 2, 5, 2, 2, 2, 1, 7]
def baseStart_3123521 : Nat := 118140960795 + 3123521 * 2 ^ 59
def prefixEnd_3123521 : Nat := 4983230072969 + 3 ^ 40 * 3123521 * 2
def baseEnd_3123521 : Nat := 118805007956472514327607

theorem tailTrace_3123521 : CollatzResearch.WordTrace tailWord_3123521 prefixEnd_3123521 118805007956472514327607 := by
  unfold tailWord_3123521
  simp only [CollatzResearch.WordTrace]
  refine ⟨113924170117024346761394417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75949446744682897840929611 113924170117024346761394417)
  ·
    refine ⟨85443127587768260071045813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113924170117024346761394417 85443127587768260071045813)
    ·
      refine ⟨8010293211353274381660545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85443127587768260071045813 8010293211353274381660545)
      ·
        refine ⟨6007719908514955786245409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8010293211353274381660545 6007719908514955786245409)
        ·
          refine ⟨4505789931386216839684057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6007719908514955786245409 4505789931386216839684057)
          ·
            refine ⟨3379342448539662629763043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4505789931386216839684057 3379342448539662629763043)
            ·
              refine ⟨5069013672809493944644565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379342448539662629763043 5069013672809493944644565)
              ·
                refine ⟨118805007956472514327607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5069013672809493944644565 118805007956472514327607)
                ·
                  rfl

theorem cell22_3123521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 7].length) (baseStart_3123521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123521 prefixEnd_3123521 := by exact prefixLift 3123521
  have htrace : WordTrace (prefixWord ++ tailWord_3123521) baseStart_3123521 baseEnd_3123521 := by
    simpa [prefixWord, tailWord_3123521, baseEnd_3123521] using wordTrace_append hprefix tailTrace_3123521
  have hstable : (prefixWord ++ tailWord_3123521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123521).length < 2 ^ (prefixWord ++ tailWord_3123521).sum := by decide
  have hdescent : baseEnd_3123521 < baseStart_3123521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123596 : List Nat := [2, 2, 1, 2, 1, 5, 2, 2, 1, 4]
def baseStart_3123596 : Nat := 118140960795 + 3123596 * 2 ^ 59
def prefixEnd_3123596 : Nat := 4983230072969 + 3 ^ 40 * 3123596 * 2
def baseEnd_3123596 : Nat := 1069270745640977433323233

theorem tailTrace_3123596 : CollatzResearch.WordTrace tailWord_3123596 prefixEnd_3123596 1069270745640977433323233 := by
  unfold tailWord_3123596
  simp only [CollatzResearch.WordTrace]
  refine ⟨56963452795876317285187321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75951270394501756380249761 56963452795876317285187321)
  ·
    refine ⟨42722589596907237963890491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56963452795876317285187321 42722589596907237963890491)
    ·
      refine ⟨64083884395360856945835737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42722589596907237963890491 64083884395360856945835737)
      ·
        refine ⟨48062913296520642709376803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64083884395360856945835737 48062913296520642709376803)
        ·
          refine ⟨72094369944780964064065205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48062913296520642709376803 72094369944780964064065205)
          ·
            refine ⟨6758847182323215381006113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72094369944780964064065205 6758847182323215381006113)
            ·
              refine ⟨5069135386742411535754585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6758847182323215381006113 5069135386742411535754585)
              ·
                refine ⟨3801851540056808651815939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5069135386742411535754585 3801851540056808651815939)
                ·
                  refine ⟨5702777310085212977723909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801851540056808651815939 5702777310085212977723909)
                  ·
                    refine ⟨1069270745640977433323233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5702777310085212977723909 1069270745640977433323233)
                    ·
                      rfl

theorem cell22_3123596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_3123596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123596 prefixEnd_3123596 := by exact prefixLift 3123596
  have htrace : WordTrace (prefixWord ++ tailWord_3123596) baseStart_3123596 baseEnd_3123596 := by
    simpa [prefixWord, tailWord_3123596, baseEnd_3123596] using wordTrace_append hprefix tailTrace_3123596
  have hstable : (prefixWord ++ tailWord_3123596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123596).length < 2 ^ (prefixWord ++ tailWord_3123596).sum := by decide
  have hdescent : baseEnd_3123596 < baseStart_3123596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123609 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 6, 3]
def baseStart_3123609 : Nat := 118140960795 + 3123609 * 2 ^ 59
def prefixEnd_3123609 : Nat := 4983230072969 + 3 ^ 40 * 3123609 * 2
def baseEnd_3123609 : Nat := 1069275195806649732748193

theorem tailTrace_3123609 : CollatzResearch.WordTrace tailWord_3123609 prefixEnd_3123609 1069275195806649732748193 := by
  unfold tailWord_3123609
  simp only [CollatzResearch.WordTrace]
  refine ⟨113927379740705537790597881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75951586493803691860398587 113927379740705537790597881)
  ·
    refine ⟨85445534805529153342948411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113927379740705537790597881 85445534805529153342948411)
    ·
      refine ⟨128168302208293730014422617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85445534805529153342948411 128168302208293730014422617)
      ·
        refine ⟨96126226656220297510816963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128168302208293730014422617 96126226656220297510816963)
        ·
          refine ⟨144189339984330446266225445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96126226656220297510816963 144189339984330446266225445)
          ·
            refine ⟨27035501247061958674917271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144189339984330446266225445 27035501247061958674917271)
            ·
              refine ⟨40553251870592938012375907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27035501247061958674917271 40553251870592938012375907)
              ·
                refine ⟨60829877805889407018563861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40553251870592938012375907 60829877805889407018563861)
                ·
                  refine ⟨2851400522151065953995181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60829877805889407018563861 2851400522151065953995181)
                  ·
                    refine ⟨1069275195806649732748193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2851400522151065953995181 1069275195806649732748193)
                    ·
                      rfl

theorem cell22_3123609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 3].length) (baseStart_3123609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123609 prefixEnd_3123609 := by exact prefixLift 3123609
  have htrace : WordTrace (prefixWord ++ tailWord_3123609) baseStart_3123609 baseEnd_3123609 := by
    simpa [prefixWord, tailWord_3123609, baseEnd_3123609] using wordTrace_append hprefix tailTrace_3123609
  have hstable : (prefixWord ++ tailWord_3123609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123609).length < 2 ^ (prefixWord ++ tailWord_3123609).sum := by decide
  have hdescent : baseEnd_3123609 < baseStart_3123609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123639 : List Nat := [1, 1, 3, 1, 3, 4, 2, 7]
def baseStart_3123639 : Nat := 118140960795 + 3123639 * 2 ^ 59
def prefixEnd_3123639 : Nat := 4983230072969 + 3 ^ 40 * 3123639 * 2
def baseEnd_3123639 : Nat := 118809496157748850499789

theorem tailTrace_3123639 : CollatzResearch.WordTrace tailWord_3123639 prefixEnd_3123639 118809496157748850499789 := by
  unfold tailWord_3123639
  simp only [CollatzResearch.WordTrace]
  refine ⟨113928473930596852914189971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75952315953731235276126647 113928473930596852914189971)
  ·
    refine ⟨170892710895895279371284957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113928473930596852914189971 170892710895895279371284957)
    ·
      refine ⟨64084766585960729764231859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170892710895895279371284957 64084766585960729764231859)
      ·
        refine ⟨96127149878941094646347789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64084766585960729764231859 96127149878941094646347789)
        ·
          refine ⟨36047681204602910492380421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96127149878941094646347789 36047681204602910492380421)
          ·
            refine ⟨6758940225863045717321329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36047681204602910492380421 6758940225863045717321329)
            ·
              refine ⟨5069205169397284287990997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6758940225863045717321329 5069205169397284287990997)
              ·
                refine ⟨118809496157748850499789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5069205169397284287990997 118809496157748850499789)
                ·
                  rfl

theorem cell22_3123639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 7].length) (baseStart_3123639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123639 prefixEnd_3123639 := by exact prefixLift 3123639
  have htrace : WordTrace (prefixWord ++ tailWord_3123639) baseStart_3123639 baseEnd_3123639 := by
    simpa [prefixWord, tailWord_3123639, baseEnd_3123639] using wordTrace_append hprefix tailTrace_3123639
  have hstable : (prefixWord ++ tailWord_3123639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123639).length < 2 ^ (prefixWord ++ tailWord_3123639).sum := by decide
  have hdescent : baseEnd_3123639 < baseStart_3123639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123699 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 2, 5]
def baseStart_3123699 : Nat := 118140960795 + 3123699 * 2 ^ 59
def prefixEnd_3123699 : Nat := 4983230072969 + 3 ^ 40 * 3123699 * 2
def baseEnd_3123699 : Nat := 1069306004645919497997917

theorem tailTrace_3123699 : CollatzResearch.WordTrace tailWord_3123699 prefixEnd_3123699 1069306004645919497997917 := by
  unfold tailWord_3123699
  simp only [CollatzResearch.WordTrace]
  refine ⟨113930662310379483161374151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75953774873586322107582767 113930662310379483161374151)
  ·
    refine ⟨170895993465569224742061227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113930662310379483161374151 170895993465569224742061227)
    ·
      refine ⟨256343990198353837113091841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170895993465569224742061227 256343990198353837113091841)
      ·
        refine ⟨192257992648765377834818881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256343990198353837113091841 192257992648765377834818881)
        ·
          refine ⟨144193494486574033376114161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192257992648765377834818881 144193494486574033376114161)
          ·
            refine ⟨108145120864930525032085621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144193494486574033376114161 108145120864930525032085621)
            ·
              refine ⟨10138605081087236721758027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108145120864930525032085621 10138605081087236721758027)
              ·
                refine ⟨15207907621630855082637041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10138605081087236721758027 15207907621630855082637041)
                ·
                  refine ⟨11405930716223141311977781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15207907621630855082637041 11405930716223141311977781)
                  ·
                    refine ⟨1069306004645919497997917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11405930716223141311977781 1069306004645919497997917)
                    ·
                      rfl

theorem cell22_3123699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 5].length) (baseStart_3123699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123699 prefixEnd_3123699 := by exact prefixLift 3123699
  have htrace : WordTrace (prefixWord ++ tailWord_3123699) baseStart_3123699 baseEnd_3123699 := by
    simpa [prefixWord, tailWord_3123699, baseEnd_3123699] using wordTrace_append hprefix tailTrace_3123699
  have hstable : (prefixWord ++ tailWord_3123699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123699).length < 2 ^ (prefixWord ++ tailWord_3123699).sum := by decide
  have hdescent : baseEnd_3123699 < baseStart_3123699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123731 : List Nat := [1, 1, 1, 2, 1, 5, 3, 3, 1, 4]
def baseStart_3123731 : Nat := 118140960795 + 3123731 * 2 ^ 59
def prefixEnd_3123731 : Nat := 4983230072969 + 3 ^ 40 * 3123731 * 2
def baseEnd_3123731 : Nat := 1069316958899882081197819

theorem tailTrace_3123731 : CollatzResearch.WordTrace tailWord_3123731 prefixEnd_3123731 1069316958899882081197819 := by
  unfold tailWord_3123731
  simp only [CollatzResearch.WordTrace]
  refine ⟨113931829446263552626539047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75954552964175701751026031 113931829446263552626539047)
  ·
    refine ⟨170897744169395328939808571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113931829446263552626539047 170897744169395328939808571)
    ·
      refine ⟨256346616254092993409712857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170897744169395328939808571 256346616254092993409712857)
      ·
        refine ⟨192259962190569745057284643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256346616254092993409712857 192259962190569745057284643)
        ·
          refine ⟨288389943285854617585926965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192259962190569745057284643 288389943285854617585926965)
          ·
            refine ⟨27036557183048870398680653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 288389943285854617585926965 27036557183048870398680653)
            ·
              refine ⟨10138708943643326399505245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27036557183048870398680653 10138708943643326399505245)
              ·
                refine ⟨3802015853866247399814467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10138708943643326399505245 3802015853866247399814467)
                ·
                  refine ⟨5703023780799371099721701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802015853866247399814467 5703023780799371099721701)
                  ·
                    refine ⟨1069316958899882081197819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5703023780799371099721701 1069316958899882081197819)
                    ·
                      rfl

theorem cell22_3123731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 4].length) (baseStart_3123731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123731 prefixEnd_3123731 := by exact prefixLift 3123731
  have htrace : WordTrace (prefixWord ++ tailWord_3123731) baseStart_3123731 baseEnd_3123731 := by
    simpa [prefixWord, tailWord_3123731, baseEnd_3123731] using wordTrace_append hprefix tailTrace_3123731
  have hstable : (prefixWord ++ tailWord_3123731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123731).length < 2 ^ (prefixWord ++ tailWord_3123731).sum := by decide
  have hdescent : baseEnd_3123731 < baseStart_3123731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123735 : List Nat := [1, 1, 3, 6, 1, 2, 1, 2, 5]
def baseStart_3123735 : Nat := 118140960795 + 3123735 * 2 ^ 59
def prefixEnd_3123735 : Nat := 4983230072969 + 3 ^ 40 * 3123735 * 2
def baseEnd_3123735 : Nat := 356439442727209134699269

theorem tailTrace_3123735 : CollatzResearch.WordTrace tailWord_3123735 prefixEnd_3123735 356439442727209134699269 := by
  unfold tailWord_3123735
  simp only [CollatzResearch.WordTrace]
  refine ⟨113931975338249061309684659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75954650225499374206456439 113931975338249061309684659)
  ·
    refine ⟨170897963007373591964526989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113931975338249061309684659 170897963007373591964526989)
    ·
      refine ⟨64086736127765096986697621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170897963007373591964526989 64086736127765096986697621)
      ·
        refine ⟨3004065755988988921251451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64086736127765096986697621 3004065755988988921251451)
        ·
          refine ⟨4506098633983483381877177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3004065755988988921251451 4506098633983483381877177)
          ·
            refine ⟨3379573975487612536407883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4506098633983483381877177 3379573975487612536407883)
            ·
              refine ⟨5069360963231418804611825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379573975487612536407883 5069360963231418804611825)
              ·
                refine ⟨3802020722423564103458869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5069360963231418804611825 3802020722423564103458869)
                ·
                  refine ⟨356439442727209134699269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3802020722423564103458869 356439442727209134699269)
                  ·
                    rfl

theorem cell22_3123735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 5].length) (baseStart_3123735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123735 prefixEnd_3123735 := by exact prefixLift 3123735
  have htrace : WordTrace (prefixWord ++ tailWord_3123735) baseStart_3123735 baseEnd_3123735 := by
    simpa [prefixWord, tailWord_3123735, baseEnd_3123735] using wordTrace_append hprefix tailTrace_3123735
  have hstable : (prefixWord ++ tailWord_3123735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123735).length < 2 ^ (prefixWord ++ tailWord_3123735).sum := by decide
  have hdescent : baseEnd_3123735 < baseStart_3123735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123761 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 1, 5]
def baseStart_3123761 : Nat := 118140960795 + 3123761 * 2 ^ 59
def prefixEnd_3123761 : Nat := 4983230072969 + 3 ^ 40 * 3123761 * 2
def baseEnd_3123761 : Nat := 1069327228512972002947727

theorem tailTrace_3123761 : CollatzResearch.WordTrace tailWord_3123761 prefixEnd_3123761 1069327228512972002947727 := by
  unfold tailWord_3123761
  simp only [CollatzResearch.WordTrace]
  refine ⟨113932923636154867750131137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75955282424103245166754091 113932923636154867750131137)
  ·
    refine ⟨85449692727116150812598353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113932923636154867750131137 85449692727116150812598353)
    ·
      refine ⟨64087269545337113109448765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85449692727116150812598353 64087269545337113109448765)
      ·
        refine ⟨24032726079501417416043287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64087269545337113109448765 24032726079501417416043287)
        ·
          refine ⟨36049089119252126124064931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24032726079501417416043287 36049089119252126124064931)
          ·
            refine ⟨54073633678878189186097397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36049089119252126124064931 54073633678878189186097397)
            ·
              refine ⟨5069403157394830236196631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54073633678878189186097397 5069403157394830236196631)
              ·
                refine ⟨7604104736092245354294947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5069403157394830236196631 7604104736092245354294947)
                ·
                  refine ⟨11406157104138368031442421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7604104736092245354294947 11406157104138368031442421)
                  ·
                    refine ⟨1069327228512972002947727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11406157104138368031442421 1069327228512972002947727)
                    ·
                      rfl

theorem cell22_3123761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_3123761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123761 prefixEnd_3123761 := by exact prefixLift 3123761
  have htrace : WordTrace (prefixWord ++ tailWord_3123761) baseStart_3123761 baseEnd_3123761 := by
    simpa [prefixWord, tailWord_3123761, baseEnd_3123761] using wordTrace_append hprefix tailTrace_3123761
  have hstable : (prefixWord ++ tailWord_3123761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123761).length < 2 ^ (prefixWord ++ tailWord_3123761).sum := by decide
  have hdescent : baseEnd_3123761 < baseStart_3123761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123819 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 9]
def baseStart_3123819 : Nat := 118140960795 + 3123819 * 2 ^ 59
def prefixEnd_3123819 : Nat := 4983230072969 + 3 ^ 40 * 3123819 * 2
def baseEnd_3123819 : Nat := 356449027699426394999183

theorem tailTrace_3123819 : CollatzResearch.WordTrace tailWord_3123819 prefixEnd_3123819 356449027699426394999183 := by
  unfold tailWord_3123819
  simp only [CollatzResearch.WordTrace]
  refine ⟨113935039069944743655742511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75956692713296495770495007 113935039069944743655742511)
  ·
    refine ⟨170902558604917115483613767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113935039069944743655742511 170902558604917115483613767)
    ·
      refine ⟨256353837907375673225420651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170902558604917115483613767 256353837907375673225420651)
      ·
        refine ⟨384530756861063509838130977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256353837907375673225420651 384530756861063509838130977)
        ·
          refine ⟨288398067645797632378598233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384530756861063509838130977 288398067645797632378598233)
          ·
            refine ⟨216298550734348224283948675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288398067645797632378598233 216298550734348224283948675)
            ·
              refine ⟨324447826101522336425923013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216298550734348224283948675 324447826101522336425923013)
              ·
                refine ⟨60833967394035438079860565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324447826101522336425923013 60833967394035438079860565)
                ·
                  refine ⟨356449027699426394999183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60833967394035438079860565 356449027699426394999183)
                  ·
                    rfl

theorem cell22_3123819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 9].length) (baseStart_3123819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123819 prefixEnd_3123819 := by exact prefixLift 3123819
  have htrace : WordTrace (prefixWord ++ tailWord_3123819) baseStart_3123819 baseEnd_3123819 := by
    simpa [prefixWord, tailWord_3123819, baseEnd_3123819] using wordTrace_append hprefix tailTrace_3123819
  have hstable : (prefixWord ++ tailWord_3123819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123819).length < 2 ^ (prefixWord ++ tailWord_3123819).sum := by decide
  have hdescent : baseEnd_3123819 < baseStart_3123819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123842 : List Nat := [3, 4, 3, 1, 2, 9]
def baseStart_3123842 : Nat := 118140960795 + 3123842 * 2 ^ 59
def prefixEnd_3123842 : Nat := 4983230072969 + 3 ^ 40 * 3123842 * 2
def baseEnd_3123842 : Nat := 13201913042818701131759

theorem tailTrace_3123842 : CollatzResearch.WordTrace tailWord_3123842 prefixEnd_3123842 13201913042818701131759 := by
  unfold tailWord_3123842
  simp only [CollatzResearch.WordTrace]
  refine ⟨28483969487215354645957445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75957251965907612389219853 28483969487215354645957445)
  ·
    refine ⟨5340744278852878996117021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28483969487215354645957445 5340744278852878996117021)
    ·
      refine ⟨2002779104569829623543883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5340744278852878996117021 2002779104569829623543883)
      ·
        refine ⟨3004168656854744435315825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2002779104569829623543883 3004168656854744435315825)
        ·
          refine ⟨2253126492641058326486869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3004168656854744435315825 2253126492641058326486869)
          ·
            refine ⟨13201913042818701131759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2253126492641058326486869 13201913042818701131759)
            ·
              rfl

theorem cell22_3123842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 9].length) (baseStart_3123842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123842 prefixEnd_3123842 := by exact prefixLift 3123842
  have htrace : WordTrace (prefixWord ++ tailWord_3123842) baseStart_3123842 baseEnd_3123842 := by
    simpa [prefixWord, tailWord_3123842, baseEnd_3123842] using wordTrace_append hprefix tailTrace_3123842
  have hstable : (prefixWord ++ tailWord_3123842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123842).length < 2 ^ (prefixWord ++ tailWord_3123842).sum := by decide
  have hdescent : baseEnd_3123842 < baseStart_3123842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123868 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 2, 5]
def baseStart_3123868 : Nat := 118140960795 + 3123868 * 2 ^ 59
def prefixEnd_3123868 : Nat := 4983230072969 + 3 ^ 40 * 3123868 * 2
def baseEnd_3123868 : Nat := 1069363856799659390522399

theorem tailTrace_3123868 : CollatzResearch.WordTrace tailWord_3123868 prefixEnd_3123868 1069363856799659390522399 := by
  unfold tailWord_3123868
  simp only [CollatzResearch.WordTrace]
  refine ⟨56968413123383612512138129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75957884164511483349517505 56968413123383612512138129)
  ·
    refine ⟨42726309842537709384103597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56968413123383612512138129 42726309842537709384103597)
    ·
      refine ⟨16022366190951641019038849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42726309842537709384103597 16022366190951641019038849)
      ·
        refine ⟨12016774643213730764279137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16022366190951641019038849 12016774643213730764279137)
        ·
          refine ⟨9012580982410298073209353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12016774643213730764279137 9012580982410298073209353)
          ·
            refine ⟨6759435736807723554907015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9012580982410298073209353 6759435736807723554907015)
            ·
              refine ⟨10139153605211585332360523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6759435736807723554907015 10139153605211585332360523)
              ·
                refine ⟨15208730407817377998540785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10139153605211585332360523 15208730407817377998540785)
                ·
                  refine ⟨11406547805863033498905589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15208730407817377998540785 11406547805863033498905589)
                  ·
                    refine ⟨1069363856799659390522399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11406547805863033498905589 1069363856799659390522399)
                    ·
                      rfl

theorem cell22_3123868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_3123868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3123868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3123868 prefixEnd_3123868 := by exact prefixLift 3123868
  have htrace : WordTrace (prefixWord ++ tailWord_3123868) baseStart_3123868 baseEnd_3123868 := by
    simpa [prefixWord, tailWord_3123868, baseEnd_3123868] using wordTrace_append hprefix tailTrace_3123868
  have hstable : (prefixWord ++ tailWord_3123868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123868).length < 2 ^ (prefixWord ++ tailWord_3123868).sum := by decide
  have hdescent : baseEnd_3123868 < baseStart_3123868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124026 : List Nat := [3, 1, 1, 1, 6, 2, 2, 2, 1, 3]
def baseStart_3124026 : Nat := 118140960795 + 3124026 * 2 ^ 59
def prefixEnd_3124026 : Nat := 4983230072969 + 3 ^ 40 * 3124026 * 2
def baseEnd_3124026 : Nat := 1069417943428599645071915

theorem tailTrace_3124026 : CollatzResearch.WordTrace tailWord_3124026 prefixEnd_3124026 1069417943428599645071915 := by
  unfold tailWord_3124026
  simp only [CollatzResearch.WordTrace]
  refine ⟨28485647245048704502131983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75961725986796545339018621 28485647245048704502131983)
  ·
    refine ⟨42728470867573056753197975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28485647245048704502131983 42728470867573056753197975)
    ·
      refine ⟨64092706301359585129796963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42728470867573056753197975 64092706301359585129796963)
      ·
        refine ⟨96139059452039377694695445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64092706301359585129796963 96139059452039377694695445)
        ·
          refine ⟨4506518411814345829438849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96139059452039377694695445 4506518411814345829438849)
          ·
            refine ⟨3379888808860759372079137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4506518411814345829438849 3379888808860759372079137)
            ·
              refine ⟨2534916606645569529059353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3379888808860759372079137 2534916606645569529059353)
              ·
                refine ⟨1901187454984177146794515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2534916606645569529059353 1901187454984177146794515)
                ·
                  refine ⟨2851781182476265720191773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901187454984177146794515 2851781182476265720191773)
                  ·
                    refine ⟨1069417943428599645071915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2851781182476265720191773 1069417943428599645071915)
                    ·
                      rfl

theorem cell22_3124026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_3124026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124026 prefixEnd_3124026 := by exact prefixLift 3124026
  have htrace : WordTrace (prefixWord ++ tailWord_3124026) baseStart_3124026 baseEnd_3124026 := by
    simpa [prefixWord, tailWord_3124026, baseEnd_3124026] using wordTrace_append hprefix tailTrace_3124026
  have hstable : (prefixWord ++ tailWord_3124026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124026).length < 2 ^ (prefixWord ++ tailWord_3124026).sum := by decide
  have hdescent : baseEnd_3124026 < baseStart_3124026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124048 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 1, 5]
def baseStart_3124048 : Nat := 118140960795 + 3124048 * 2 ^ 59
def prefixEnd_3124048 : Nat := 4983230072969 + 3 ^ 40 * 3124048 * 2
def baseEnd_3124048 : Nat := 1069425474478198921021847

theorem tailTrace_3124048 : CollatzResearch.WordTrace tailWord_3124048 prefixEnd_3124048 1069425474478198921021847 := by
  unfold tailWord_3124048
  simp only [CollatzResearch.WordTrace]
  refine ⟨56971695693057557882914399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75962260924076743843885865 56971695693057557882914399)
  ·
    refine ⟨85457543539586336824371599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56971695693057557882914399 85457543539586336824371599)
    ·
      refine ⟨128186315309379505236557399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85457543539586336824371599 128186315309379505236557399)
      ·
        refine ⟨192279472964069257854836099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128186315309379505236557399 192279472964069257854836099)
        ·
          refine ⟨288419209446103886782254149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192279472964069257854836099 288419209446103886782254149)
          ·
            refine ⟨54078601771144478771672653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 288419209446103886782254149 54078601771144478771672653)
            ·
              refine ⟨20279475664179179539377245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54078601771144478771672653 20279475664179179539377245)
              ·
                refine ⟨7604803374067192327266467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20279475664179179539377245 7604803374067192327266467)
                ·
                  refine ⟨11407205061100788490899701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7604803374067192327266467 11407205061100788490899701)
                  ·
                    refine ⟨1069425474478198921021847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11407205061100788490899701 1069425474478198921021847)
                    ·
                      rfl

theorem cell22_3124048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_3124048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124048 prefixEnd_3124048 := by exact prefixLift 3124048
  have htrace : WordTrace (prefixWord ++ tailWord_3124048) baseStart_3124048 baseEnd_3124048 := by
    simpa [prefixWord, tailWord_3124048, baseEnd_3124048] using wordTrace_append hprefix tailTrace_3124048
  have hstable : (prefixWord ++ tailWord_3124048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124048).length < 2 ^ (prefixWord ++ tailWord_3124048).sum := by decide
  have hdescent : baseEnd_3124048 < baseStart_3124048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124063 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 1, 6]
def baseStart_3124063 : Nat := 118140960795 + 3124063 * 2 ^ 59
def prefixEnd_3124063 : Nat := 4983230072969 + 3 ^ 40 * 3124063 * 2
def baseEnd_3124063 : Nat := 1069430609284743881896801

theorem tailTrace_3124063 : CollatzResearch.WordTrace tailWord_3124063 prefixEnd_3124063 1069430609284743881896801 := by
  unfold tailWord_3124063
  simp only [CollatzResearch.WordTrace]
  refine ⟨113943938481060773327624843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75962625654040515551749895 113943938481060773327624843)
  ·
    refine ⟨170915907721591159991437265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113943938481060773327624843 170915907721591159991437265)
    ·
      refine ⟨128186930791193369993577949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170915907721591159991437265 128186930791193369993577949)
      ·
        refine ⟨48070099046697513747591731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128186930791193369993577949 48070099046697513747591731)
        ·
          refine ⟨72105148570046270621387597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48070099046697513747591731 72105148570046270621387597)
          ·
            refine ⟨27039430713767351483020349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72105148570046270621387597 27039430713767351483020349)
            ·
              refine ⟨10139786517662756806132631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27039430713767351483020349 10139786517662756806132631)
              ·
                refine ⟨15209679776494135209198947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10139786517662756806132631 15209679776494135209198947)
                ·
                  refine ⟨22814519664741202813798421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15209679776494135209198947 22814519664741202813798421)
                  ·
                    refine ⟨1069430609284743881896801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22814519664741202813798421 1069430609284743881896801)
                    ·
                      rfl

theorem cell22_3124063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_3124063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124063 prefixEnd_3124063 := by exact prefixLift 3124063
  have htrace : WordTrace (prefixWord ++ tailWord_3124063) baseStart_3124063 baseEnd_3124063 := by
    simpa [prefixWord, tailWord_3124063, baseEnd_3124063] using wordTrace_append hprefix tailTrace_3124063
  have hstable : (prefixWord ++ tailWord_3124063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124063).length < 2 ^ (prefixWord ++ tailWord_3124063).sum := by decide
  have hdescent : baseEnd_3124063 < baseStart_3124063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124067 : List Nat := [1, 1, 1, 5, 3, 2, 2, 3, 4]
def baseStart_3124067 : Nat := 118140960795 + 3124067 * 2 ^ 59
def prefixEnd_3124067 : Nat := 4983230072969 + 3 ^ 40 * 3124067 * 2
def baseEnd_3124067 : Nat := 356477326188829734932263

theorem tailTrace_3124067 : CollatzResearch.WordTrace tailWord_3124067 prefixEnd_3124067 356477326188829734932263 := by
  unfold tailWord_3124067
  simp only [CollatzResearch.WordTrace]
  refine ⟨113944084373046282010770455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75962722915364188007180303 113944084373046282010770455)
  ·
    refine ⟨170916126559569423016155683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113944084373046282010770455 170916126559569423016155683)
    ·
      refine ⟨256374189839354134524233525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170916126559569423016155683 256374189839354134524233525)
      ·
        refine ⟨24035080297439450111646893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 256374189839354134524233525 24035080297439450111646893)
        ·
          refine ⟨9013155111539793791867585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24035080297439450111646893 9013155111539793791867585)
          ·
            refine ⟨6759866333654845343900689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9013155111539793791867585 6759866333654845343900689)
            ·
              refine ⟨5069899750241134007925517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6759866333654845343900689 5069899750241134007925517)
              ·
                refine ⟨1901212406340425252972069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5069899750241134007925517 1901212406340425252972069)
                ·
                  refine ⟨356477326188829734932263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1901212406340425252972069 356477326188829734932263)
                  ·
                    rfl

theorem cell22_3124067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 4].length) (baseStart_3124067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124067 prefixEnd_3124067 := by exact prefixLift 3124067
  have htrace : WordTrace (prefixWord ++ tailWord_3124067) baseStart_3124067 baseEnd_3124067 := by
    simpa [prefixWord, tailWord_3124067, baseEnd_3124067] using wordTrace_append hprefix tailTrace_3124067
  have hstable : (prefixWord ++ tailWord_3124067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124067).length < 2 ^ (prefixWord ++ tailWord_3124067).sum := by decide
  have hdescent : baseEnd_3124067 < baseStart_3124067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124082 : List Nat := [3, 2, 1, 2, 1, 1, 5, 2, 2, 3]
def baseStart_3124082 : Nat := 118140960795 + 3124082 * 2 ^ 59
def prefixEnd_3124082 : Nat := 4983230072969 + 3 ^ 40 * 3124082 * 2
def baseEnd_3124082 : Nat := 1069437113373034165671743

theorem tailTrace_3124082 : CollatzResearch.WordTrace tailWord_3124082 prefixEnd_3124082 1069437113373034165671743 := by
  unfold tailWord_3124082
  simp only [CollatzResearch.WordTrace]
  refine ⟨28486157866997984893141625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75963087645327959715044333 28486157866997984893141625)
  ·
    refine ⟨21364618400248488669856219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28486157866997984893141625 21364618400248488669856219)
    ·
      refine ⟨32046927600372733004784329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21364618400248488669856219 32046927600372733004784329)
      ·
        refine ⟨24035195700279549753588247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32046927600372733004784329 24035195700279549753588247)
        ·
          refine ⟨36052793550419324630382371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24035195700279549753588247 36052793550419324630382371)
          ·
            refine ⟨54079190325628986945573557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36052793550419324630382371 54079190325628986945573557)
            ·
              refine ⟨5069924093027717526147521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54079190325628986945573557 5069924093027717526147521)
              ·
                refine ⟨3802443069770788144610641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5069924093027717526147521 3802443069770788144610641)
                ·
                  refine ⟨2851832302328091108457981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3802443069770788144610641 2851832302328091108457981)
                  ·
                    refine ⟨1069437113373034165671743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2851832302328091108457981 1069437113373034165671743)
                    ·
                      rfl

theorem cell22_3124082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_3124082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124082 prefixEnd_3124082 := by exact prefixLift 3124082
  have htrace : WordTrace (prefixWord ++ tailWord_3124082) baseStart_3124082 baseEnd_3124082 := by
    simpa [prefixWord, tailWord_3124082, baseEnd_3124082] using wordTrace_append hprefix tailTrace_3124082
  have hstable : (prefixWord ++ tailWord_3124082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124082).length < 2 ^ (prefixWord ++ tailWord_3124082).sum := by decide
  have hdescent : baseEnd_3124082 < baseStart_3124082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124108 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 2, 6]
def baseStart_3124108 : Nat := 118140960795 + 3124108 * 2 ^ 59
def prefixEnd_3124108 : Nat := 4983230072969 + 3 ^ 40 * 3124108 * 2
def baseEnd_3124108 : Nat := 1069446013704378764521663

theorem tailTrace_3124108 : CollatzResearch.WordTrace tailWord_3124108 prefixEnd_3124108 1069446013704378764521663 := by
  unfold tailWord_3124108
  simp only [CollatzResearch.WordTrace]
  refine ⟨56972789882948873006506489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75963719843931830675341985 56972789882948873006506489)
  ·
    refine ⟨42729592412211654754879867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56972789882948873006506489 42729592412211654754879867)
    ·
      refine ⟨64094388618317482132319801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42729592412211654754879867 64094388618317482132319801)
      ·
        refine ⟨48070791463738111599239851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64094388618317482132319801 48070791463738111599239851)
        ·
          refine ⟨72106187195607167398859777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48070791463738111599239851 72106187195607167398859777)
          ·
            refine ⟨54079640396705375549144833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72106187195607167398859777 54079640396705375549144833)
            ·
              refine ⟨40559730297529031661858625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54079640396705375549144833 40559730297529031661858625)
              ·
                refine ⟨30419797723146773746393969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40559730297529031661858625 30419797723146773746393969)
                ·
                  refine ⟨22814848292360080309795477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30419797723146773746393969 22814848292360080309795477)
                  ·
                    refine ⟨1069446013704378764521663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22814848292360080309795477 1069446013704378764521663)
                    ·
                      rfl

theorem cell22_3124108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_3124108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124108 prefixEnd_3124108 := by exact prefixLift 3124108
  have htrace : WordTrace (prefixWord ++ tailWord_3124108) baseStart_3124108 baseEnd_3124108 := by
    simpa [prefixWord, tailWord_3124108, baseEnd_3124108] using wordTrace_append hprefix tailTrace_3124108
  have hstable : (prefixWord ++ tailWord_3124108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124108).length < 2 ^ (prefixWord ++ tailWord_3124108).sum := by decide
  have hdescent : baseEnd_3124108 < baseStart_3124108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124118 : List Nat := [5, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3124118 : Nat := 118140960795 + 3124118 * 2 ^ 59
def prefixEnd_3124118 : Nat := 4983230072969 + 3 ^ 40 * 3124118 * 2
def baseEnd_3124118 : Nat := 356483145636247357257211

theorem tailTrace_3124118 : CollatzResearch.WordTrace tailWord_3124118 prefixEnd_3124118 356483145636247357257211 := by
  unfold tailWord_3124118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7121621530991344857554813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75963962997241011813918005 7121621530991344857554813)
  ·
    refine ⟨2670608074121754321583055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7121621530991344857554813 2670608074121754321583055)
    ·
      refine ⟨4005912111182631482374583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2670608074121754321583055 4005912111182631482374583)
      ·
        refine ⟨6008868166773947223561875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4005912111182631482374583 6008868166773947223561875)
        ·
          refine ⟨9013302250160920835342813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6008868166773947223561875 9013302250160920835342813)
          ·
            refine ⟨3379988343810345313253555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9013302250160920835342813 3379988343810345313253555)
            ·
              refine ⟨5069982515715517969880333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379988343810345313253555 5069982515715517969880333)
              ·
                refine ⟨1901243443393319238705125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5069982515715517969880333 1901243443393319238705125)
                ·
                  refine ⟨356483145636247357257211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1901243443393319238705125 356483145636247357257211)
                  ·
                    rfl

theorem cell22_3124118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3124118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124118 prefixEnd_3124118 := by exact prefixLift 3124118
  have htrace : WordTrace (prefixWord ++ tailWord_3124118) baseStart_3124118 baseEnd_3124118 := by
    simpa [prefixWord, tailWord_3124118, baseEnd_3124118] using wordTrace_append hprefix tailTrace_3124118
  have hstable : (prefixWord ++ tailWord_3124118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124118).length < 2 ^ (prefixWord ++ tailWord_3124118).sum := by decide
  have hdescent : baseEnd_3124118 < baseStart_3124118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124157 : List Nat := [1, 4, 1, 2, 4, 1, 1, 3, 5]
def baseStart_3124157 : Nat := 118140960795 + 3124157 * 2 ^ 59
def prefixEnd_3124157 : Nat := 4983230072969 + 3 ^ 40 * 3124157 * 2
def baseEnd_3124157 : Nat := 356487595801919656682171

theorem tailTrace_3124157 : CollatzResearch.WordTrace tailWord_3124157 prefixEnd_3124157 356487595801919656682171 := by
  unfold tailWord_3124157
  simp only [CollatzResearch.WordTrace]
  refine ⟨113947366942720227381546725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75964911295146818254364483 113947366942720227381546725)
  ·
    refine ⟨21365131301760042634040011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113947366942720227381546725 21365131301760042634040011)
    ·
      refine ⟨32047696952640063951060017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21365131301760042634040011 32047696952640063951060017)
      ·
        refine ⟨24035772714480047963295013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32047696952640063951060017 24035772714480047963295013)
        ·
          refine ⟨4506707383965008993117815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24035772714480047963295013 4506707383965008993117815)
          ·
            refine ⟨6760061075947513489676723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4506707383965008993117815 6760061075947513489676723)
            ·
              refine ⟨10140091613921270234515085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760061075947513489676723 10140091613921270234515085)
              ·
                refine ⟨3802534355220476337943157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10140091613921270234515085 3802534355220476337943157)
                ·
                  refine ⟨356487595801919656682171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3802534355220476337943157 356487595801919656682171)
                  ·
                    rfl

theorem cell22_3124157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_3124157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124157 prefixEnd_3124157 := by exact prefixLift 3124157
  have htrace : WordTrace (prefixWord ++ tailWord_3124157) baseStart_3124157 baseEnd_3124157 := by
    simpa [prefixWord, tailWord_3124157, baseEnd_3124157] using wordTrace_append hprefix tailTrace_3124157
  have hstable : (prefixWord ++ tailWord_3124157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124157).length < 2 ^ (prefixWord ++ tailWord_3124157).sum := by decide
  have hdescent : baseEnd_3124157 < baseStart_3124157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124217 : List Nat := [1, 2, 1, 3, 1, 3, 1, 5, 2, 3]
def baseStart_3124217 : Nat := 118140960795 + 3124217 * 2 ^ 59
def prefixEnd_3124217 : Nat := 4983230072969 + 3 ^ 40 * 3124217 * 2
def baseEnd_3124217 : Nat := 1069483326631938813546329

theorem tailTrace_3124217 : CollatzResearch.WordTrace tailWord_3124217 prefixEnd_3124217 1069483326631938813546329 := by
  unfold tailWord_3124217
  simp only [CollatzResearch.WordTrace]
  refine ⟨113949555322502857628730905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75966370215001905085820603 113949555322502857628730905)
  ·
    refine ⟨85462166491877143221548179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113949555322502857628730905 85462166491877143221548179)
    ·
      refine ⟨128193249737815714832322269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85462166491877143221548179 128193249737815714832322269)
      ·
        refine ⟨48072468651680893062120851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128193249737815714832322269 48072468651680893062120851)
        ·
          refine ⟨72108702977521339593181277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48072468651680893062120851 72108702977521339593181277)
          ·
            refine ⟨27040763616570502347442979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72108702977521339593181277 27040763616570502347442979)
            ·
              refine ⟨40561145424855753521164469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27040763616570502347442979 40561145424855753521164469)
              ·
                refine ⟨3802607383580226892609169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40561145424855753521164469 3802607383580226892609169)
                ·
                  refine ⟨2851955537685170169456877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3802607383580226892609169 2851955537685170169456877)
                  ·
                    refine ⟨1069483326631938813546329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2851955537685170169456877 1069483326631938813546329)
                    ·
                      rfl

theorem cell22_3124217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 3].length) (baseStart_3124217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124217 prefixEnd_3124217 := by exact prefixLift 3124217
  have htrace : WordTrace (prefixWord ++ tailWord_3124217) baseStart_3124217 baseEnd_3124217 := by
    simpa [prefixWord, tailWord_3124217, baseEnd_3124217] using wordTrace_append hprefix tailTrace_3124217
  have hstable : (prefixWord ++ tailWord_3124217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124217).length < 2 ^ (prefixWord ++ tailWord_3124217).sum := by decide
  have hdescent : baseEnd_3124217 < baseStart_3124217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124232 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 2, 4]
def baseStart_3124232 : Nat := 118140960795 + 3124232 * 2 ^ 59
def prefixEnd_3124232 : Nat := 4983230072969 + 3 ^ 40 * 3124232 * 2
def baseEnd_3124232 : Nat := 1069488461438483774421283

theorem tailTrace_3124232 : CollatzResearch.WordTrace tailWord_3124232 prefixEnd_3124232 1069488461438483774421283 := by
  unfold tailWord_3124232
  simp only [CollatzResearch.WordTrace]
  refine ⟨56975051208724257595263475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75966734944965676793684633 56975051208724257595263475)
  ·
    refine ⟨85462576813086386392895213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56975051208724257595263475 85462576813086386392895213)
    ·
      refine ⟨32048466304907394897335705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85462576813086386392895213 32048466304907394897335705)
      ·
        refine ⟨24036349728680546173001779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32048466304907394897335705 24036349728680546173001779)
        ·
          refine ⟨36054524593020819259502669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24036349728680546173001779 36054524593020819259502669)
          ·
            refine ⟨13520446722382807222313501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36054524593020819259502669 13520446722382807222313501)
            ·
              refine ⟨5070167520893552708367563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13520446722382807222313501 5070167520893552708367563)
              ·
                refine ⟨7605251281340329062551345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5070167520893552708367563 7605251281340329062551345)
                ·
                  refine ⟨5703938461005246796913509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7605251281340329062551345 5703938461005246796913509)
                  ·
                    refine ⟨1069488461438483774421283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5703938461005246796913509 1069488461438483774421283)
                    ·
                      rfl

theorem cell22_3124232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_3124232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124232 prefixEnd_3124232 := by exact prefixLift 3124232
  have htrace : WordTrace (prefixWord ++ tailWord_3124232) baseStart_3124232 baseEnd_3124232 := by
    simpa [prefixWord, tailWord_3124232, baseEnd_3124232] using wordTrace_append hprefix tailTrace_3124232
  have hstable : (prefixWord ++ tailWord_3124232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124232).length < 2 ^ (prefixWord ++ tailWord_3124232).sum := by decide
  have hdescent : baseEnd_3124232 < baseStart_3124232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124352 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 6, 3]
def baseStart_3124352 : Nat := 118140960795 + 3124352 * 2 ^ 59
def prefixEnd_3124352 : Nat := 4983230072969 + 3 ^ 40 * 3124352 * 2
def baseEnd_3124352 : Nat := 1069529539890843461420915

theorem tailTrace_3124352 : CollatzResearch.WordTrace tailWord_3124352 prefixEnd_3124352 1069529539890843461420915 := by
  unfold tailWord_3124352
  simp only [CollatzResearch.WordTrace]
  refine ⟨56977239588506887842447655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75969652784675850456596873 56977239588506887842447655)
  ·
    refine ⟨85465859382760331763671483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56977239588506887842447655 85465859382760331763671483)
    ·
      refine ⟨128198789074140497645507225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85465859382760331763671483 128198789074140497645507225)
      ·
        refine ⟨96149091805605373234130419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128198789074140497645507225 96149091805605373234130419)
        ·
          refine ⟨144223637708408059851195629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96149091805605373234130419 144223637708408059851195629)
          ·
            refine ⟨54083864140653022444198361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144223637708408059851195629 54083864140653022444198361)
            ·
              refine ⟨40562898105489766833148771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54083864140653022444198361 40562898105489766833148771)
              ·
                refine ⟨60844347158234650249723157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40562898105489766833148771 60844347158234650249723157)
                ·
                  refine ⟨2852078773042249230455773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60844347158234650249723157 2852078773042249230455773)
                  ·
                    refine ⟨1069529539890843461420915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2852078773042249230455773 1069529539890843461420915)
                    ·
                      rfl

theorem cell22_3124352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 6, 3].length) (baseStart_3124352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124352 prefixEnd_3124352 := by exact prefixLift 3124352
  have htrace : WordTrace (prefixWord ++ tailWord_3124352) baseStart_3124352 baseEnd_3124352 := by
    simpa [prefixWord, tailWord_3124352, baseEnd_3124352] using wordTrace_append hprefix tailTrace_3124352
  have hstable : (prefixWord ++ tailWord_3124352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124352).length < 2 ^ (prefixWord ++ tailWord_3124352).sum := by decide
  have hdescent : baseEnd_3124352 < baseStart_3124352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124356 : List Nat := [2, 3, 2, 1, 2, 3, 3, 1, 1, 4]
def baseStart_3124356 : Nat := 118140960795 + 3124356 * 2 ^ 59
def prefixEnd_3124356 : Nat := 4983230072969 + 3 ^ 40 * 3124356 * 2
def baseEnd_3124356 : Nat := 1069530909172588784320903

theorem tailTrace_3124356 : CollatzResearch.WordTrace tailWord_3124356 prefixEnd_3124356 1069530909172588784320903 := by
  unfold tailWord_3124356
  simp only [CollatzResearch.WordTrace]
  refine ⟨56977312534499642184020461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75969750045999522912027281 56977312534499642184020461)
  ·
    refine ⟨21366492200437365819007673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56977312534499642184020461 21366492200437365819007673)
    ·
      refine ⟨16024869150328024364255755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21366492200437365819007673 16024869150328024364255755)
      ·
        refine ⟨24037303725492036546383633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16024869150328024364255755 24037303725492036546383633)
        ·
          refine ⟨18027977794119027409787725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24037303725492036546383633 18027977794119027409787725)
          ·
            refine ⟨6760491672794635278670397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18027977794119027409787725 6760491672794635278670397)
            ·
              refine ⟨2535184377297988229501399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6760491672794635278670397 2535184377297988229501399)
              ·
                refine ⟨3802776565946982344252099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535184377297988229501399 3802776565946982344252099)
                ·
                  refine ⟨5704164848920473516378149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802776565946982344252099 5704164848920473516378149)
                  ·
                    refine ⟨1069530909172588784320903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5704164848920473516378149 1069530909172588784320903)
                    ·
                      rfl

theorem cell22_3124356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_3124356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124356 prefixEnd_3124356 := by exact prefixLift 3124356
  have htrace : WordTrace (prefixWord ++ tailWord_3124356) baseStart_3124356 baseEnd_3124356 := by
    simpa [prefixWord, tailWord_3124356, baseEnd_3124356] using wordTrace_append hprefix tailTrace_3124356
  have hstable : (prefixWord ++ tailWord_3124356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124356).length < 2 ^ (prefixWord ++ tailWord_3124356).sum := by decide
  have hdescent : baseEnd_3124356 < baseStart_3124356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124386 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_3124386 : Nat := 118140960795 + 3124386 * 2 ^ 59
def prefixEnd_3124386 : Nat := 4983230072969 + 3 ^ 40 * 3124386 * 2
def baseEnd_3124386 : Nat := 1069541178785678706070811

theorem tailTrace_3124386 : CollatzResearch.WordTrace tailWord_3124386 prefixEnd_3124386 1069541178785678706070811 := by
  unfold tailWord_3124386
  simp only [CollatzResearch.WordTrace]
  refine ⟨28488929814722649872908253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75970479505927066327755341 28488929814722649872908253)
  ·
    refine ⟨10683348680520993702340595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28488929814722649872908253 10683348680520993702340595)
    ·
      refine ⟨16025023020781490553510893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10683348680520993702340595 16025023020781490553510893)
      ·
        refine ⟨6009383632793058957566585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16025023020781490553510893 6009383632793058957566585)
        ·
          refine ⟨4507037724594794218174939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6009383632793058957566585 4507037724594794218174939)
          ·
            refine ⟨6760556586892191327262409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4507037724594794218174939 6760556586892191327262409)
            ·
              refine ⟨5070417440169143495446807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6760556586892191327262409 5070417440169143495446807)
              ·
                refine ⟨7605626160253715243170211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5070417440169143495446807 7605626160253715243170211)
                ·
                  refine ⟨11408439240380572864755317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7605626160253715243170211 11408439240380572864755317)
                  ·
                    refine ⟨1069541178785678706070811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11408439240380572864755317 1069541178785678706070811)
                    ·
                      rfl

theorem cell22_3124386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_3124386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124386 prefixEnd_3124386 := by exact prefixLift 3124386
  have htrace : WordTrace (prefixWord ++ tailWord_3124386) baseStart_3124386 baseEnd_3124386 := by
    simpa [prefixWord, tailWord_3124386, baseEnd_3124386] using wordTrace_append hprefix tailTrace_3124386
  have hstable : (prefixWord ++ tailWord_3124386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124386).length < 2 ^ (prefixWord ++ tailWord_3124386).sum := by decide
  have hdescent : baseEnd_3124386 < baseStart_3124386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124401 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 2, 4]
def baseStart_3124401 : Nat := 118140960795 + 3124401 * 2 ^ 59
def prefixEnd_3124401 : Nat := 4983230072969 + 3 ^ 40 * 3124401 * 2
def baseEnd_3124401 : Nat := 1069546313592223666945765

theorem tailTrace_3124401 : CollatzResearch.WordTrace tailWord_3124401 prefixEnd_3124401 1069546313592223666945765 := by
  unfold tailWord_3124401
  simp only [CollatzResearch.WordTrace]
  refine ⟨113956266353836257053429057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75970844235890838035619371 113956266353836257053429057)
  ·
    refine ⟨85467199765377192790071793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113956266353836257053429057 85467199765377192790071793)
    ·
      refine ⟨64100399824032894592553845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85467199765377192790071793 64100399824032894592553845)
      ·
        refine ⟨6009412483503083868051923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64100399824032894592553845 6009412483503083868051923)
        ·
          refine ⟨9014118725254625802077885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6009412483503083868051923 9014118725254625802077885)
          ·
            refine ⟨3380294521970484675779207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9014118725254625802077885 3380294521970484675779207)
            ·
              refine ⟨5070441782955727013668811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3380294521970484675779207 5070441782955727013668811)
              ·
                refine ⟨7605662674433590520503217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5070441782955727013668811 7605662674433590520503217)
                ·
                  refine ⟨5704247005825192890377413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7605662674433590520503217 5704247005825192890377413)
                  ·
                    refine ⟨1069546313592223666945765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5704247005825192890377413 1069546313592223666945765)
                    ·
                      rfl

theorem cell22_3124401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_3124401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124401 prefixEnd_3124401 := by exact prefixLift 3124401
  have htrace : WordTrace (prefixWord ++ tailWord_3124401) baseStart_3124401 baseEnd_3124401 := by
    simpa [prefixWord, tailWord_3124401, baseEnd_3124401] using wordTrace_append hprefix tailTrace_3124401
  have hstable : (prefixWord ++ tailWord_3124401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124401).length < 2 ^ (prefixWord ++ tailWord_3124401).sum := by decide
  have hdescent : baseEnd_3124401 < baseStart_3124401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124420 : List Nat := [2, 3, 3, 1, 4, 1, 1, 2, 2, 3]
def baseStart_3124420 : Nat := 118140960795 + 3124420 * 2 ^ 59
def prefixEnd_3124420 : Nat := 4983230072969 + 3 ^ 40 * 3124420 * 2
def baseEnd_3124420 : Nat := 1069552817680513950720707

theorem tailTrace_3124420 : CollatzResearch.WordTrace tailWord_3124420 prefixEnd_3124420 1069552817680513950720707 := by
  unfold tailWord_3124420
  simp only [CollatzResearch.WordTrace]
  refine ⟨56978479670383711649185357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75971306227178282198913809 56978479670383711649185357)
  ·
    refine ⟨21366929876393891868444509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56978479670383711649185357 21366929876393891868444509)
    ·
      refine ⟨8012598703647709450666691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21366929876393891868444509 8012598703647709450666691)
      ·
        refine ⟨12018898055471564176000037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8012598703647709450666691 12018898055471564176000037)
        ·
          refine ⟨2253543385400918283000007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12018898055471564176000037 2253543385400918283000007)
          ·
            refine ⟨3380315078101377424500011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2253543385400918283000007 3380315078101377424500011)
            ·
              refine ⟨5070472617152066136750017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3380315078101377424500011 5070472617152066136750017)
              ·
                refine ⟨3802854462864049602562513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5070472617152066136750017 3802854462864049602562513)
                ·
                  refine ⟨2852140847148037201921885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3802854462864049602562513 2852140847148037201921885)
                  ·
                    refine ⟨1069552817680513950720707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2852140847148037201921885 1069552817680513950720707)
                    ·
                      rfl

theorem cell22_3124420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_3124420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124420 prefixEnd_3124420 := by exact prefixLift 3124420
  have htrace : WordTrace (prefixWord ++ tailWord_3124420) baseStart_3124420 baseEnd_3124420 := by
    simpa [prefixWord, tailWord_3124420, baseEnd_3124420] using wordTrace_append hprefix tailTrace_3124420
  have hstable : (prefixWord ++ tailWord_3124420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124420).length < 2 ^ (prefixWord ++ tailWord_3124420).sum := by decide
  have hdescent : baseEnd_3124420 < baseStart_3124420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124427 : List Nat := [1, 1, 1, 1, 3, 2, 2, 6, 5]
def baseStart_3124427 : Nat := 118140960795 + 3124427 * 2 ^ 59
def prefixEnd_3124427 : Nat := 4983230072969 + 3 ^ 40 * 3124427 * 2
def baseEnd_3124427 : Nat := 356518404641189421931895

theorem tailTrace_3124427 : CollatzResearch.WordTrace tailWord_3124427 prefixEnd_3124427 356518404641189421931895 := by
  unfold tailWord_3124427
  simp only [CollatzResearch.WordTrace]
  refine ⟨113957214651742063493875535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75971476434494708995917023 113957214651742063493875535)
  ·
    refine ⟨170935821977613095240813303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113957214651742063493875535 170935821977613095240813303)
    ·
      refine ⟨256403732966419642861219955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170935821977613095240813303 256403732966419642861219955)
      ·
        refine ⟨384605599449629464291829933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256403732966419642861219955 384605599449629464291829933)
        ·
          refine ⟨144227099793611049109436225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384605599449629464291829933 144227099793611049109436225)
          ·
            refine ⟨108170324845208286832077169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144227099793611049109436225 108170324845208286832077169)
            ·
              refine ⟨81127743633906215124057877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108170324845208286832077169 81127743633906215124057877)
              ·
                refine ⟨3802862982839353833940213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81127743633906215124057877 3802862982839353833940213)
                ·
                  refine ⟨356518404641189421931895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3802862982839353833940213 356518404641189421931895)
                  ·
                    rfl

theorem cell22_3124427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 5].length) (baseStart_3124427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124427 prefixEnd_3124427 := by exact prefixLift 3124427
  have htrace : WordTrace (prefixWord ++ tailWord_3124427) baseStart_3124427 baseEnd_3124427 := by
    simpa [prefixWord, tailWord_3124427, baseEnd_3124427] using wordTrace_append hprefix tailTrace_3124427
  have hstable : (prefixWord ++ tailWord_3124427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124427).length < 2 ^ (prefixWord ++ tailWord_3124427).sum := by decide
  have hdescent : baseEnd_3124427 < baseStart_3124427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124474 : List Nat := [3, 1, 1, 1, 1, 4, 1, 5, 1, 4]
def baseStart_3124474 : Nat := 118140960795 + 3124474 * 2 ^ 59
def prefixEnd_3124474 : Nat := 4983230072969 + 3 ^ 40 * 3124474 * 2
def baseEnd_3124474 : Nat := 1069571302984075809870541

theorem tailTrace_3124474 : CollatzResearch.WordTrace tailWord_3124474 prefixEnd_3124474 1069571302984075809870541 := by
  unfold tailWord_3124474
  simp only [CollatzResearch.WordTrace]
  refine ⟨28489732220642947630209119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75972619255047860347224317 28489732220642947630209119)
  ·
    refine ⟨42734598330964421445313679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28489732220642947630209119 42734598330964421445313679)
    ·
      refine ⟨64101897496446632167970519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42734598330964421445313679 64101897496446632167970519)
      ·
        refine ⟨96152846244669948251955779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64101897496446632167970519 96152846244669948251955779)
        ·
          refine ⟨144229269367004922377933669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96152846244669948251955779 144229269367004922377933669)
          ·
            refine ⟨27042988006313422945862563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144229269367004922377933669 27042988006313422945862563)
            ·
              refine ⟨40564482009470134418793845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27042988006313422945862563 40564482009470134418793845)
              ·
                refine ⟨3802920188387825101761923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40564482009470134418793845 3802920188387825101761923)
                ·
                  refine ⟨5704380282581737652642885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802920188387825101761923 5704380282581737652642885)
                  ·
                    refine ⟨1069571302984075809870541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5704380282581737652642885 1069571302984075809870541)
                    ·
                      rfl

theorem cell22_3124474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_3124474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124474 prefixEnd_3124474 := by exact prefixLift 3124474
  have htrace : WordTrace (prefixWord ++ tailWord_3124474) baseStart_3124474 baseEnd_3124474 := by
    simpa [prefixWord, tailWord_3124474, baseEnd_3124474] using wordTrace_append hprefix tailTrace_3124474
  have hstable : (prefixWord ++ tailWord_3124474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124474).length < 2 ^ (prefixWord ++ tailWord_3124474).sum := by decide
  have hdescent : baseEnd_3124474 < baseStart_3124474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124482 : List Nat := [3, 4, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_3124482 : Nat := 118140960795 + 3124482 * 2 ^ 59
def prefixEnd_3124482 : Nat := 4983230072969 + 3 ^ 40 * 3124482 * 2
def baseEnd_3124482 : Nat := 1069574041547566455670517

theorem tailTrace_3124482 : CollatzResearch.WordTrace tailWord_3124482 prefixEnd_3124482 1069574041547566455670517 := by
  unfold tailWord_3124482
  simp only [CollatzResearch.WordTrace]
  refine ⟨28489805166635701971781925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75972813777695205258085133 28489805166635701971781925)
  ·
    refine ⟨5341838468744194119709111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28489805166635701971781925 5341838468744194119709111)
    ·
      refine ⟨8012757703116291179563667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5341838468744194119709111 8012757703116291179563667)
      ·
        refine ⟨12019136554674436769345501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8012757703116291179563667 12019136554674436769345501)
        ·
          refine ⟨4507176208002913788504563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12019136554674436769345501 4507176208002913788504563)
          ·
            refine ⟨6760764312004370682756845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4507176208002913788504563 6760764312004370682756845)
            ·
              refine ⟨2535286617001639006033817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6760764312004370682756845 2535286617001639006033817)
              ·
                refine ⟨1901464962751229254525363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2535286617001639006033817 1901464962751229254525363)
                ·
                  refine ⟨2852197444126843881788045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901464962751229254525363 2852197444126843881788045)
                  ·
                    refine ⟨1069574041547566455670517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2852197444126843881788045 1069574041547566455670517)
                    ·
                      rfl

theorem cell22_3124482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_3124482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124482 prefixEnd_3124482 := by exact prefixLift 3124482
  have htrace : WordTrace (prefixWord ++ tailWord_3124482) baseStart_3124482 baseEnd_3124482 := by
    simpa [prefixWord, tailWord_3124482, baseEnd_3124482] using wordTrace_append hprefix tailTrace_3124482
  have hstable : (prefixWord ++ tailWord_3124482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124482).length < 2 ^ (prefixWord ++ tailWord_3124482).sum := by decide
  have hdescent : baseEnd_3124482 < baseStart_3124482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124525 : List Nat := [1, 5, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_3124525 : Nat := 118140960795 + 3124525 * 2 ^ 59
def prefixEnd_3124525 : Nat := 4983230072969 + 3 ^ 40 * 3124525 * 2
def baseEnd_3124525 : Nat := 1069588761326328676845385

theorem tailTrace_3124525 : CollatzResearch.WordTrace tailWord_3124525 prefixEnd_3124525 1069588761326328676845385 := by
  unfold tailWord_3124525
  simp only [CollatzResearch.WordTrace]
  refine ⟨113960789005387026230943029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75973859336924684153962019 113960789005387026230943029)
  ·
    refine ⟨10683823969255033709150909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113960789005387026230943029 10683823969255033709150909)
    ·
      refine ⟨4006433988470637640931591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10683823969255033709150909 4006433988470637640931591)
      ·
        refine ⟨6009650982705956461397387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4006433988470637640931591 6009650982705956461397387)
        ·
          refine ⟨9014476474058934692096081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6009650982705956461397387 9014476474058934692096081)
          ·
            refine ⟨6760857355544201019072061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9014476474058934692096081 6760857355544201019072061)
            ·
              refine ⟨2535321508329075382152023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6760857355544201019072061 2535321508329075382152023)
              ·
                refine ⟨3802982262493613073228035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535321508329075382152023 3802982262493613073228035)
                ·
                  refine ⟨5704473393740419609842053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802982262493613073228035 5704473393740419609842053)
                  ·
                    refine ⟨1069588761326328676845385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5704473393740419609842053 1069588761326328676845385)
                    ·
                      rfl

theorem cell22_3124525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_3124525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124525 prefixEnd_3124525 := by exact prefixLift 3124525
  have htrace : WordTrace (prefixWord ++ tailWord_3124525) baseStart_3124525 baseEnd_3124525 := by
    simpa [prefixWord, tailWord_3124525, baseEnd_3124525] using wordTrace_append hprefix tailTrace_3124525
  have hstable : (prefixWord ++ tailWord_3124525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124525).length < 2 ^ (prefixWord ++ tailWord_3124525).sum := by decide
  have hdescent : baseEnd_3124525 < baseStart_3124525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124549 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 7, 3]
def baseStart_3124549 : Nat := 118140960795 + 3124549 * 2 ^ 59
def prefixEnd_3124549 : Nat := 4983230072969 + 3 ^ 40 * 3124549 * 2
def baseEnd_3124549 : Nat := 1069596977016800614245311

theorem tailTrace_3124549 : CollatzResearch.WordTrace tailWord_3124549 prefixEnd_3124549 1069596977016800614245311 := by
  unfold tailWord_3124549
  simp only [CollatzResearch.WordTrace]
  refine ⟨113961664357300078329816701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75974442904866718886544467 113961664357300078329816701)
  ·
    refine ⟨42735624133987529373681263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113961664357300078329816701 42735624133987529373681263)
    ·
      refine ⟨64103436200981294060521895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42735624133987529373681263 64103436200981294060521895)
      ·
        refine ⟨96155154301471941090782843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64103436200981294060521895 96155154301471941090782843)
        ·
          refine ⟨144232731452207911636174265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96155154301471941090782843 144232731452207911636174265)
          ·
            refine ⟨108174548589155933727130699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144232731452207911636174265 108174548589155933727130699)
            ·
              refine ⟨162261822883733900590696049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108174548589155933727130699 162261822883733900590696049)
              ·
                refine ⟨121696367162800425443022037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162261822883733900590696049 121696367162800425443022037)
                ·
                  refine ⟨2852258605378134971320829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 121696367162800425443022037 2852258605378134971320829)
                  ·
                    refine ⟨1069596977016800614245311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2852258605378134971320829 1069596977016800614245311)
                    ·
                      rfl

theorem cell22_3124549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_3124549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124549 prefixEnd_3124549 := by exact prefixLift 3124549
  have htrace : WordTrace (prefixWord ++ tailWord_3124549) baseStart_3124549 baseEnd_3124549 := by
    simpa [prefixWord, tailWord_3124549, baseEnd_3124549] using wordTrace_append hprefix tailTrace_3124549
  have hstable : (prefixWord ++ tailWord_3124549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124549).length < 2 ^ (prefixWord ++ tailWord_3124549).sum := by decide
  have hdescent : baseEnd_3124549 < baseStart_3124549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124564 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_3124564 : Nat := 118140960795 + 3124564 * 2 ^ 59
def prefixEnd_3124564 : Nat := 4983230072969 + 3 ^ 40 * 3124564 * 2
def baseEnd_3124564 : Nat := 1069602111823345575120265

theorem tailTrace_3124564 : CollatzResearch.WordTrace tailWord_3124564 prefixEnd_3124564 1069602111823345575120265 := by
  unfold tailWord_3124564
  simp only [CollatzResearch.WordTrace]
  refine ⟨56981105726122867945806373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75974807634830490594408497 56981105726122867945806373)
  ·
    refine ⟨10683957323648037739838695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56981105726122867945806373 10683957323648037739838695)
    ·
      refine ⟨16025935985472056609758043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10683957323648037739838695 16025935985472056609758043)
      ·
        refine ⟨24038903978208084914637065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16025935985472056609758043 24038903978208084914637065)
        ·
          refine ⟨18029177983656063685977799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24038903978208084914637065 18029177983656063685977799)
          ·
            refine ⟨27043766975484095528966699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18029177983656063685977799 27043766975484095528966699)
            ·
              refine ⟨40565650463226143293450049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27043766975484095528966699 40565650463226143293450049)
              ·
                refine ⟨30424237847419607470087537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40565650463226143293450049 30424237847419607470087537)
                ·
                  refine ⟨22818178385564705602565653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30424237847419607470087537 22818178385564705602565653)
                  ·
                    refine ⟨1069602111823345575120265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22818178385564705602565653 1069602111823345575120265)
                    ·
                      rfl

theorem cell22_3124564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_3124564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124564 prefixEnd_3124564 := by exact prefixLift 3124564
  have htrace : WordTrace (prefixWord ++ tailWord_3124564) baseStart_3124564 baseEnd_3124564 := by
    simpa [prefixWord, tailWord_3124564, baseEnd_3124564] using wordTrace_append hprefix tailTrace_3124564
  have hstable : (prefixWord ++ tailWord_3124564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124564).length < 2 ^ (prefixWord ++ tailWord_3124564).sum := by decide
  have hdescent : baseEnd_3124564 < baseStart_3124564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124594 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_3124594 : Nat := 118140960795 + 3124594 * 2 ^ 59
def prefixEnd_3124594 : Nat := 4983230072969 + 3 ^ 40 * 3124594 * 2
def baseEnd_3124594 : Nat := 1069612381436435496870173

theorem tailTrace_3124594 : CollatzResearch.WordTrace tailWord_3124594 prefixEnd_3124594 1069612381436435496870173 := by
  unfold tailWord_3124594
  simp only [CollatzResearch.WordTrace]
  refine ⟨28490826410534262753801209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75975537094758034010136557 28490826410534262753801209)
  ·
    refine ⟨21368119807900697065350907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28490826410534262753801209 21368119807900697065350907)
    ·
      refine ⟨32052179711851045598026361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21368119807900697065350907 32052179711851045598026361)
      ·
        refine ⟨24039134783888284198519771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32052179711851045598026361 24039134783888284198519771)
        ·
          refine ⟨36058702175832426297779657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24039134783888284198519771 36058702175832426297779657)
          ·
            refine ⟨27044026631874319723334743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36058702175832426297779657 27044026631874319723334743)
            ·
              refine ⟨40566039947811479585002115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27044026631874319723334743 40566039947811479585002115)
              ·
                refine ⟨60849059921717219377503173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40566039947811479585002115 60849059921717219377503173)
                ·
                  refine ⟨11409198735321978633281845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60849059921717219377503173 11409198735321978633281845)
                  ·
                    refine ⟨1069612381436435496870173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11409198735321978633281845 1069612381436435496870173)
                    ·
                      rfl

theorem cell22_3124594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_3124594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124594 prefixEnd_3124594 := by exact prefixLift 3124594
  have htrace : WordTrace (prefixWord ++ tailWord_3124594) baseStart_3124594 baseEnd_3124594 := by
    simpa [prefixWord, tailWord_3124594, baseEnd_3124594] using wordTrace_append hprefix tailTrace_3124594
  have hstable : (prefixWord ++ tailWord_3124594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124594).length < 2 ^ (prefixWord ++ tailWord_3124594).sum := by decide
  have hdescent : baseEnd_3124594 < baseStart_3124594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124718 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 3, 3]
def baseStart_3124718 : Nat := 118140960795 + 3124718 * 2 ^ 59
def prefixEnd_3124718 : Nat := 4983230072969 + 3 ^ 40 * 3124718 * 2
def baseEnd_3124718 : Nat := 1069654829170540506769793

theorem tailTrace_3124718 : CollatzResearch.WordTrace tailWord_3124718 prefixEnd_3124718 1069654829170540506769793 := by
  unfold tailWord_3124718
  simp only [CollatzResearch.WordTrace]
  refine ⟨14245978536710977524089851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75978552195791880128479205 14245978536710977524089851)
  ·
    refine ⟨21368967805066466286134777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14245978536710977524089851 21368967805066466286134777)
    ·
      refine ⟨16026725853799849714601083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21368967805066466286134777 16026725853799849714601083)
      ·
        refine ⟨24040088780699774571901625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16026725853799849714601083 24040088780699774571901625)
        ·
          refine ⟨18030066585524830928926219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24040088780699774571901625 18030066585524830928926219)
          ·
            refine ⟨27045099878287246393389329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18030066585524830928926219 27045099878287246393389329)
            ·
              refine ⟨20283824908715434795041997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27045099878287246393389329 20283824908715434795041997)
              ·
                refine ⟨7606434340768288048140749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20283824908715434795041997 7606434340768288048140749)
                ·
                  refine ⟨2852412877788108018052781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7606434340768288048140749 2852412877788108018052781)
                  ·
                    refine ⟨1069654829170540506769793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2852412877788108018052781 1069654829170540506769793)
                    ·
                      rfl

theorem cell22_3124718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_3124718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124718 prefixEnd_3124718 := by exact prefixLift 3124718
  have htrace : WordTrace (prefixWord ++ tailWord_3124718) baseStart_3124718 baseEnd_3124718 := by
    simpa [prefixWord, tailWord_3124718, baseEnd_3124718] using wordTrace_append hprefix tailTrace_3124718
  have hstable : (prefixWord ++ tailWord_3124718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124718).length < 2 ^ (prefixWord ++ tailWord_3124718).sum := by decide
  have hdescent : baseEnd_3124718 < baseStart_3124718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124823 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 2, 4]
def baseStart_3124823 : Nat := 118140960795 + 3124823 * 2 ^ 59
def prefixEnd_3124823 : Nat := 4983230072969 + 3 ^ 40 * 3124823 * 2
def baseEnd_3124823 : Nat := 1069690772816355232894471

theorem tailTrace_3124823 : CollatzResearch.WordTrace tailWord_3124823 prefixEnd_3124823 1069690772816355232894471 := by
  unfold tailWord_3124823
  simp only [CollatzResearch.WordTrace]
  refine ⟨113971657958307423125291123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75981105305538282083527415 113971657958307423125291123)
  ·
    refine ⟨170957486937461134687936685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113971657958307423125291123 170957486937461134687936685)
    ·
      refine ⟨64109057601547925507976257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170957486937461134687936685 64109057601547925507976257)
      ·
        refine ⟨48081793201160944130982193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64109057601547925507976257 48081793201160944130982193)
        ·
          refine ⟨36061344900870708098236645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48081793201160944130982193 36061344900870708098236645)
          ·
            refine ⟨6761502168913257768419371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36061344900870708098236645 6761502168913257768419371)
            ·
              refine ⟨10142253253369886652629057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6761502168913257768419371 10142253253369886652629057)
              ·
                refine ⟨7606689940027414989471793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10142253253369886652629057 7606689940027414989471793)
                ·
                  refine ⟨5705017455020561242103845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7606689940027414989471793 5705017455020561242103845)
                  ·
                    refine ⟨1069690772816355232894471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5705017455020561242103845 1069690772816355232894471)
                    ·
                      rfl

theorem cell22_3124823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_3124823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124823 prefixEnd_3124823 := by exact prefixLift 3124823
  have htrace : WordTrace (prefixWord ++ tailWord_3124823) baseStart_3124823 baseEnd_3124823 := by
    simpa [prefixWord, tailWord_3124823, baseEnd_3124823] using wordTrace_append hprefix tailTrace_3124823
  have hstable : (prefixWord ++ tailWord_3124823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124823).length < 2 ^ (prefixWord ++ tailWord_3124823).sum := by decide
  have hdescent : baseEnd_3124823 < baseStart_3124823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124842 : List Nat := [3, 1, 3, 2, 1, 2, 4, 1, 2, 3]
def baseStart_3124842 : Nat := 118140960795 + 3124842 * 2 ^ 59
def prefixEnd_3124842 : Nat := 4983230072969 + 3 ^ 40 * 3124842 * 2
def baseEnd_3124842 : Nat := 1069697276904645516669413

theorem tailTrace_3124842 : CollatzResearch.WordTrace tailWord_3124842 prefixEnd_3124842 1069697276904645516669413 := by
  unfold tailWord_3124842
  simp only [CollatzResearch.WordTrace]
  refine ⟨28493087736309647342558195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75981567296825726246821853 28493087736309647342558195)
  ·
    refine ⟨42739631604464471013837293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28493087736309647342558195 42739631604464471013837293)
    ·
      refine ⟨16027361851674176630188985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42739631604464471013837293 16027361851674176630188985)
      ·
        refine ⟨12020521388755632472641739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16027361851674176630188985 12020521388755632472641739)
        ·
          refine ⟨18030782083133448708962609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12020521388755632472641739 18030782083133448708962609)
          ·
            refine ⟨13523086562350086531721957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18030782083133448708962609 13523086562350086531721957)
            ·
              refine ⟨2535578730440641224697867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13523086562350086531721957 2535578730440641224697867)
              ·
                refine ⟨3803368095660961837046801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535578730440641224697867 3803368095660961837046801)
                ·
                  refine ⟨2852526071745721377785101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3803368095660961837046801 2852526071745721377785101)
                  ·
                    refine ⟨1069697276904645516669413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2852526071745721377785101 1069697276904645516669413)
                    ·
                      rfl

theorem cell22_3124842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_3124842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124842 prefixEnd_3124842 := by exact prefixLift 3124842
  have htrace : WordTrace (prefixWord ++ tailWord_3124842) baseStart_3124842 baseEnd_3124842 := by
    simpa [prefixWord, tailWord_3124842, baseEnd_3124842] using wordTrace_append hprefix tailTrace_3124842
  have hstable : (prefixWord ++ tailWord_3124842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124842).length < 2 ^ (prefixWord ++ tailWord_3124842).sum := by decide
  have hdescent : baseEnd_3124842 < baseStart_3124842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124887 : List Nat := [1, 1, 3, 3, 2, 3, 1, 4, 1, 3]
def baseStart_3124887 : Nat := 118140960795 + 3124887 * 2 ^ 59
def prefixEnd_3124887 : Nat := 4983230072969 + 3 ^ 40 * 3124887 * 2
def baseEnd_3124887 : Nat := 1069712681324280399294275

theorem tailTrace_3124887 : CollatzResearch.WordTrace tailWord_3124887 prefixEnd_3124887 1069712681324280399294275 := by
  unfold tailWord_3124887
  simp only [CollatzResearch.WordTrace]
  refine ⟨113973992230075562055620915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75982661486717041370413943 113973992230075562055620915)
  ·
    refine ⟨170960988345113343083431373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113973992230075562055620915 170960988345113343083431373)
    ·
      refine ⟨64110370629417503656286765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170960988345113343083431373 64110370629417503656286765)
      ·
        refine ⟨24041388986031563871107537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64110370629417503656286765 24041388986031563871107537)
        ·
          refine ⟨18031041739523672903330653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24041388986031563871107537 18031041739523672903330653)
          ·
            refine ⟨6761640652321377338748995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18031041739523672903330653 6761640652321377338748995)
            ·
              refine ⟨10142460978482066008123493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6761640652321377338748995 10142460978482066008123493)
              ·
                refine ⟨1901711433465387376523155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10142460978482066008123493 1901711433465387376523155)
                ·
                  refine ⟨2852567150198081064784733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901711433465387376523155 2852567150198081064784733)
                  ·
                    refine ⟨1069712681324280399294275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2852567150198081064784733 1069712681324280399294275)
                    ·
                      rfl

theorem cell22_3124887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_3124887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124887 prefixEnd_3124887 := by exact prefixLift 3124887
  have htrace : WordTrace (prefixWord ++ tailWord_3124887) baseStart_3124887 baseEnd_3124887 := by
    simpa [prefixWord, tailWord_3124887, baseEnd_3124887] using wordTrace_append hprefix tailTrace_3124887
  have hstable : (prefixWord ++ tailWord_3124887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124887).length < 2 ^ (prefixWord ++ tailWord_3124887).sum := by decide
  have hdescent : baseEnd_3124887 < baseStart_3124887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124934 : List Nat := [6, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_3124934 : Nat := 118140960795 + 3124934 * 2 ^ 59
def prefixEnd_3124934 : Nat := 4983230072969 + 3 ^ 40 * 3124934 * 2
def baseEnd_3124934 : Nat := 356576256794929314456377

theorem tailTrace_3124934 : CollatzResearch.WordTrace tailWord_3124934 prefixEnd_3124934 356576256794929314456377 := by
  unfold tailWord_3124934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3561740826903290283830683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75983804307270192721721237 3561740826903290283830683)
  ·
    refine ⟨5342611240354935425746025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3561740826903290283830683 5342611240354935425746025)
    ·
      refine ⟨4006958430266201569309519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5342611240354935425746025 4006958430266201569309519)
      ·
        refine ⟨6010437645399302353964279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4006958430266201569309519 6010437645399302353964279)
        ·
          refine ⟨9015656468098953530946419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6010437645399302353964279 9015656468098953530946419)
          ·
            refine ⟨13523484702148430296419629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9015656468098953530946419 13523484702148430296419629)
            ·
              refine ⟨5071306763305661361157361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13523484702148430296419629 5071306763305661361157361)
              ·
                refine ⟨3803480072479246020868021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5071306763305661361157361 3803480072479246020868021)
                ·
                  refine ⟨356576256794929314456377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3803480072479246020868021 356576256794929314456377)
                  ·
                    rfl

theorem cell22_3124934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_3124934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124934 prefixEnd_3124934 := by exact prefixLift 3124934
  have htrace : WordTrace (prefixWord ++ tailWord_3124934) baseStart_3124934 baseEnd_3124934 := by
    simpa [prefixWord, tailWord_3124934, baseEnd_3124934] using wordTrace_append hprefix tailTrace_3124934
  have hstable : (prefixWord ++ tailWord_3124934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124934).length < 2 ^ (prefixWord ++ tailWord_3124934).sum := by decide
  have hdescent : baseEnd_3124934 < baseStart_3124934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124945 : List Nat := [1, 2, 2, 1, 2, 4, 2, 4, 4]
def baseStart_3124945 : Nat := 118140960795 + 3124945 * 2 ^ 59
def prefixEnd_3124945 : Nat := 4983230072969 + 3 ^ 40 * 3124945 * 2
def baseEnd_3124945 : Nat := 356577511969862527114699

theorem tailTrace_3124945 : CollatzResearch.WordTrace tailWord_3124945 prefixEnd_3124945 356577511969862527114699 := by
  unfold tailWord_3124945
  simp only [CollatzResearch.WordTrace]
  refine ⟨113976107663865437961232289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75984071775910291974154859 113976107663865437961232289)
  ·
    refine ⟨85482080747899078470924217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113976107663865437961232289 85482080747899078470924217)
    ·
      refine ⟨64111560560924308853193163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85482080747899078470924217 64111560560924308853193163)
      ·
        refine ⟨96167340841386463279789745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64111560560924308853193163 96167340841386463279789745)
        ·
          refine ⟨72125505631039847459842309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96167340841386463279789745 72125505631039847459842309)
          ·
            refine ⟨13523532305819971398720433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72125505631039847459842309 13523532305819971398720433)
            ·
              refine ⟨10142649229364978549040325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13523532305819971398720433 10142649229364978549040325)
              ·
                refine ⟨1901746730505933477945061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10142649229364978549040325 1901746730505933477945061)
                ·
                  refine ⟨356577511969862527114699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1901746730505933477945061 356577511969862527114699)
                  ·
                    rfl

theorem cell22_3124945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 4].length) (baseStart_3124945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124945 prefixEnd_3124945 := by exact prefixLift 3124945
  have htrace : WordTrace (prefixWord ++ tailWord_3124945) baseStart_3124945 baseEnd_3124945 := by
    simpa [prefixWord, tailWord_3124945, baseEnd_3124945] using wordTrace_append hprefix tailTrace_3124945
  have hstable : (prefixWord ++ tailWord_3124945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124945).length < 2 ^ (prefixWord ++ tailWord_3124945).sum := by decide
  have hdescent : baseEnd_3124945 < baseStart_3124945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124960 : List Nat := [2, 1, 1, 3, 1, 2, 2, 5, 2, 3]
def baseStart_3124960 : Nat := 118140960795 + 3124960 * 2 ^ 59
def prefixEnd_3124960 : Nat := 4983230072969 + 3 ^ 40 * 3124960 * 2
def baseEnd_3124960 : Nat := 1069737670716132542219051

theorem tailTrace_3124960 : CollatzResearch.WordTrace tailWord_3124960 prefixEnd_3124960 1069737670716132542219051 := by
  unfold tailWord_3124960
  simp only [CollatzResearch.WordTrace]
  refine ⟨56988327379405547761514167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75984436505874063682018889 56988327379405547761514167)
  ·
    refine ⟨85482491069108321642271251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56988327379405547761514167 85482491069108321642271251)
    ·
      refine ⟨128223736603662482463406877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85482491069108321642271251 128223736603662482463406877)
      ·
        refine ⟨48083901226373430923777579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128223736603662482463406877 48083901226373430923777579)
        ·
          refine ⟨72125851839560146385666369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48083901226373430923777579 72125851839560146385666369)
          ·
            refine ⟨54094388879670109789249777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72125851839560146385666369 54094388879670109789249777)
            ·
              refine ⟨40570791659752582341937333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54094388879670109789249777 40570791659752582341937333)
              ·
                refine ⟨3803511718101804594556625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40570791659752582341937333 3803511718101804594556625)
                ·
                  refine ⟨2852633788576353445917469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3803511718101804594556625 2852633788576353445917469)
                  ·
                    refine ⟨1069737670716132542219051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2852633788576353445917469 1069737670716132542219051)
                    ·
                      rfl

theorem cell22_3124960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 2, 3].length) (baseStart_3124960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3124960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3124960 prefixEnd_3124960 := by exact prefixLift 3124960
  have htrace : WordTrace (prefixWord ++ tailWord_3124960) baseStart_3124960 baseEnd_3124960 := by
    simpa [prefixWord, tailWord_3124960, baseEnd_3124960] using wordTrace_append hprefix tailTrace_3124960
  have hstable : (prefixWord ++ tailWord_3124960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124960).length < 2 ^ (prefixWord ++ tailWord_3124960).sum := by decide
  have hdescent : baseEnd_3124960 < baseStart_3124960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125095 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3125095 : Nat := 118140960795 + 3125095 * 2 ^ 59
def prefixEnd_3125095 : Nat := 4983230072969 + 3 ^ 40 * 3125095 * 2
def baseEnd_3125095 : Nat := 1069783883975037190093637

theorem tailTrace_3125095 : CollatzResearch.WordTrace tailWord_3125095 prefixEnd_3125095 1069783883975037190093637 := by
  unfold tailWord_3125095
  simp only [CollatzResearch.WordTrace]
  refine ⟨113981578613322013579192739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75987719075548009052795159 113981578613322013579192739)
  ·
    refine ⟨170972367919983020368789109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113981578613322013579192739 170972367919983020368789109)
    ·
      refine ⟨16028659492498408159573979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170972367919983020368789109 16028659492498408159573979)
      ·
        refine ⟨24042989238747612239360969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16028659492498408159573979 24042989238747612239360969)
        ·
          refine ⟨18032241929060709179520727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24042989238747612239360969 18032241929060709179520727)
          ·
            refine ⟨27048362893591063769281091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18032241929060709179520727 27048362893591063769281091)
            ·
              refine ⟨40572544340386595653921637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27048362893591063769281091 40572544340386595653921637)
              ·
                refine ⟨7607352063822486685110307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40572544340386595653921637 7607352063822486685110307)
                ·
                  refine ⟨11411028095733730027665461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7607352063822486685110307 11411028095733730027665461)
                  ·
                    refine ⟨1069783883975037190093637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11411028095733730027665461 1069783883975037190093637)
                    ·
                      rfl

theorem cell22_3125095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3125095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125095 prefixEnd_3125095 := by exact prefixLift 3125095
  have htrace : WordTrace (prefixWord ++ tailWord_3125095) baseStart_3125095 baseEnd_3125095 := by
    simpa [prefixWord, tailWord_3125095, baseEnd_3125095] using wordTrace_append hprefix tailTrace_3125095
  have hstable : (prefixWord ++ tailWord_3125095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125095).length < 2 ^ (prefixWord ++ tailWord_3125095).sum := by decide
  have hdescent : baseEnd_3125095 < baseStart_3125095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125129 : List Nat := [1, 2, 1, 1, 5, 1, 5, 1, 2, 3]
def baseStart_3125129 : Nat := 118140960795 + 3125129 * 2 ^ 59
def prefixEnd_3125129 : Nat := 4983230072969 + 3 ^ 40 * 3125129 * 2
def baseEnd_3125129 : Nat := 1069795522869872434743533

theorem tailTrace_3125129 : CollatzResearch.WordTrace tailWord_3125129 prefixEnd_3125129 1069795522869872434743533 := by
  unfold tailWord_3125129
  simp only [CollatzResearch.WordTrace]
  refine ⟨113982818695198837385930441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75988545796799224923953627 113982818695198837385930441)
  ·
    refine ⟨85487114021399128039447831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113982818695198837385930441 85487114021399128039447831)
    ·
      refine ⟨128230671032098692059171747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85487114021399128039447831 128230671032098692059171747)
      ·
        refine ⟨192346006548148038088757621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128230671032098692059171747 192346006548148038088757621)
        ·
          refine ⟨18032438113888878570821027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192346006548148038088757621 18032438113888878570821027)
          ·
            refine ⟨27048657170833317856231541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18032438113888878570821027 27048657170833317856231541)
            ·
              refine ⟨2535811609765623549021707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27048657170833317856231541 2535811609765623549021707)
              ·
                refine ⟨3803717414648435323532561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535811609765623549021707 3803717414648435323532561)
                ·
                  refine ⟨2852788060986326492649421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3803717414648435323532561 2852788060986326492649421)
                  ·
                    refine ⟨1069795522869872434743533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2852788060986326492649421 1069795522869872434743533)
                    ·
                      rfl

theorem cell22_3125129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 2, 3].length) (baseStart_3125129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125129 prefixEnd_3125129 := by exact prefixLift 3125129
  have htrace : WordTrace (prefixWord ++ tailWord_3125129) baseStart_3125129 baseEnd_3125129 := by
    simpa [prefixWord, tailWord_3125129, baseEnd_3125129] using wordTrace_append hprefix tailTrace_3125129
  have hstable : (prefixWord ++ tailWord_3125129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125129).length < 2 ^ (prefixWord ++ tailWord_3125129).sum := by decide
  have hdescent : baseEnd_3125129 < baseStart_3125129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125180 : List Nat := [2, 2, 2, 5, 2, 1, 2, 1, 2, 3]
def baseStart_3125180 : Nat := 118140960795 + 3125180 * 2 ^ 59
def prefixEnd_3125180 : Nat := 4983230072969 + 3 ^ 40 * 3125180 * 2
def baseEnd_3125180 : Nat := 1069812981212125301718377

theorem tailTrace_3125180 : CollatzResearch.WordTrace tailWord_3125180 prefixEnd_3125180 1069812981212125301718377 := by
  unfold tailWord_3125180
  simp only [CollatzResearch.WordTrace]
  refine ⟨56992339409007036548018497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75989785878676048730691329 56992339409007036548018497)
  ·
    refine ⟨42744254556755277411013873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56992339409007036548018497 42744254556755277411013873)
    ·
      refine ⟨32058190917566458058260405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42744254556755277411013873 32058190917566458058260405)
      ·
        refine ⟨3005455398521855442961913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32058190917566458058260405 3005455398521855442961913)
        ·
          refine ⟨2254091548891391582221435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3005455398521855442961913 2254091548891391582221435)
          ·
            refine ⟨3381137323337087373332153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254091548891391582221435 3381137323337087373332153)
            ·
              refine ⟨2535852992502815529999115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3381137323337087373332153 2535852992502815529999115)
              ·
                refine ⟨3803779488754223294998673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535852992502815529999115 3803779488754223294998673)
                ·
                  refine ⟨2852834616565667471249005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3803779488754223294998673 2852834616565667471249005)
                  ·
                    refine ⟨1069812981212125301718377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2852834616565667471249005 1069812981212125301718377)
                    ·
                      rfl

theorem cell22_3125180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_3125180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125180 prefixEnd_3125180 := by exact prefixLift 3125180
  have htrace : WordTrace (prefixWord ++ tailWord_3125180) baseStart_3125180 baseEnd_3125180 := by
    simpa [prefixWord, tailWord_3125180, baseEnd_3125180] using wordTrace_append hprefix tailTrace_3125180
  have hstable : (prefixWord ++ tailWord_3125180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125180).length < 2 ^ (prefixWord ++ tailWord_3125180).sum := by decide
  have hdescent : baseEnd_3125180 < baseStart_3125180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125217 : List Nat := [1, 2, 3, 1, 2, 1, 2, 5, 1, 4]
def baseStart_3125217 : Nat := 118140960795 + 3125217 * 2 ^ 59
def prefixEnd_3125217 : Nat := 4983230072969 + 3 ^ 40 * 3125217 * 2
def baseEnd_3125217 : Nat := 1069825647068269538543263

theorem tailTrace_3125217 : CollatzResearch.WordTrace tailWord_3125217 prefixEnd_3125217 1069825647068269538543263 := by
  unfold tailWord_3125217
  simp only [CollatzResearch.WordTrace]
  refine ⟨113986028318880028415133905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75990685545920018943422603 113986028318880028415133905)
  ·
    refine ⟨85489521239160021311350429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113986028318880028415133905 85489521239160021311350429)
    ·
      refine ⟨32058570464685007991756411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85489521239160021311350429 32058570464685007991756411)
      ·
        refine ⟨48087855697027511987634617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32058570464685007991756411 48087855697027511987634617)
        ·
          refine ⟨36065891772770633990725963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48087855697027511987634617 36065891772770633990725963)
          ·
            refine ⟨54098837659155950986088945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36065891772770633990725963 54098837659155950986088945)
            ·
              refine ⟨40574128244366963239566709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54098837659155950986088945 40574128244366963239566709)
              ·
                refine ⟨3803824522909402803709379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40574128244366963239566709 3803824522909402803709379)
                ·
                  refine ⟨5705736784364104205564069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3803824522909402803709379 5705736784364104205564069)
                  ·
                    refine ⟨1069825647068269538543263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5705736784364104205564069 1069825647068269538543263)
                    ·
                      rfl

theorem cell22_3125217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_3125217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125217 prefixEnd_3125217 := by exact prefixLift 3125217
  have htrace : WordTrace (prefixWord ++ tailWord_3125217) baseStart_3125217 baseEnd_3125217 := by
    simpa [prefixWord, tailWord_3125217, baseEnd_3125217] using wordTrace_append hprefix tailTrace_3125217
  have hstable : (prefixWord ++ tailWord_3125217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125217).length < 2 ^ (prefixWord ++ tailWord_3125217).sum := by decide
  have hdescent : baseEnd_3125217 < baseStart_3125217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125262 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_3125262 : Nat := 118140960795 + 3125262 * 2 ^ 59
def prefixEnd_3125262 : Nat := 4983230072969 + 3 ^ 40 * 3125262 * 2
def baseEnd_3125262 : Nat := 1069841051487904421168125

theorem tailTrace_3125262 : CollatzResearch.WordTrace tailWord_3125262 prefixEnd_3125262 1069841051487904421168125 := by
  unfold tailWord_3125262
  simp only [CollatzResearch.WordTrace]
  refine ⟨14248458700464625137565255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75991779735811334067014693 14248458700464625137565255)
  ·
    refine ⟨21372688050696937706347883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14248458700464625137565255 21372688050696937706347883)
    ·
      refine ⟨32059032076045406559521825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21372688050696937706347883 32059032076045406559521825)
      ·
        refine ⟨24044274057034054919641369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32059032076045406559521825 24044274057034054919641369)
        ·
          refine ⟨18033205542775541189731027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24044274057034054919641369 18033205542775541189731027)
          ·
            refine ⟨27049808314163311784596541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18033205542775541189731027 27049808314163311784596541)
            ·
              refine ⟨10143678117811241919223703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27049808314163311784596541 10143678117811241919223703)
              ·
                refine ⟨15215517176716862878835555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10143678117811241919223703 15215517176716862878835555)
                ·
                  refine ⟨22823275765075294318253333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15215517176716862878835555 22823275765075294318253333)
                  ·
                    refine ⟨1069841051487904421168125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22823275765075294318253333 1069841051487904421168125)
                    ·
                      rfl

theorem cell22_3125262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_3125262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125262 prefixEnd_3125262 := by exact prefixLift 3125262
  have htrace : WordTrace (prefixWord ++ tailWord_3125262) baseStart_3125262 baseEnd_3125262 := by
    simpa [prefixWord, tailWord_3125262, baseEnd_3125262] using wordTrace_append hprefix tailTrace_3125262
  have hstable : (prefixWord ++ tailWord_3125262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125262).length < 2 ^ (prefixWord ++ tailWord_3125262).sum := by decide
  have hdescent : baseEnd_3125262 < baseStart_3125262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125268 : List Nat := [2, 4, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_3125268 : Nat := 118140960795 + 3125268 * 2 ^ 59
def prefixEnd_3125268 : Nat := 4983230072969 + 3 ^ 40 * 3125268 * 2
def baseEnd_3125268 : Nat := 1069843105410522405518107

theorem tailTrace_3125268 : CollatzResearch.WordTrace tailWord_3125268 prefixEnd_3125268 1069843105410522405518107 := by
  unfold tailWord_3125268
  simp only [CollatzResearch.WordTrace]
  refine ⟨56993944220847632062620229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75991925627796842750160305 56993944220847632062620229)
  ·
    refine ⟨10686364541408931011741293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56993944220847632062620229 10686364541408931011741293)
    ·
      refine ⟨4007386703028349129402985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10686364541408931011741293 4007386703028349129402985)
      ·
        refine ⟨3005540027271261847052239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4007386703028349129402985 3005540027271261847052239)
        ·
          refine ⟨4508310040906892770578359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3005540027271261847052239 4508310040906892770578359)
          ·
            refine ⟨6762465061360339155867539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508310040906892770578359 6762465061360339155867539)
            ·
              refine ⟨10143697592040508733801309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6762465061360339155867539 10143697592040508733801309)
              ·
                refine ⟨3803886597015190775175491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10143697592040508733801309 3803886597015190775175491)
                ·
                  refine ⟨5705829895522786162763237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3803886597015190775175491 5705829895522786162763237)
                  ·
                    refine ⟨1069843105410522405518107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5705829895522786162763237 1069843105410522405518107)
                    ·
                      rfl

theorem cell22_3125268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_3125268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125268 prefixEnd_3125268 := by exact prefixLift 3125268
  have htrace : WordTrace (prefixWord ++ tailWord_3125268) baseStart_3125268 baseEnd_3125268 := by
    simpa [prefixWord, tailWord_3125268, baseEnd_3125268] using wordTrace_append hprefix tailTrace_3125268
  have hstable : (prefixWord ++ tailWord_3125268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125268).length < 2 ^ (prefixWord ++ tailWord_3125268).sum := by decide
  have hdescent : baseEnd_3125268 < baseStart_3125268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125277 : List Nat := [1, 4, 2, 2, 2, 2, 9]
def baseStart_3125277 : Nat := 118140960795 + 3125277 * 2 ^ 59
def prefixEnd_3125277 : Nat := 4983230072969 + 3 ^ 40 * 3125277 * 2
def baseEnd_3125277 : Nat := 39623932825720347483077

theorem tailTrace_3125277 : CollatzResearch.WordTrace tailWord_3125277 prefixEnd_3125277 39623932825720347483077 := by
  unfold tailWord_3125277
  simp only [CollatzResearch.WordTrace]
  refine ⟨113988216698662658662318085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75992144465775105774878723 113988216698662658662318085)
  ·
    refine ⟨21372790630999248499184641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113988216698662658662318085 21372790630999248499184641)
    ·
      refine ⟨16029592973249436374388481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21372790630999248499184641 16029592973249436374388481)
      ·
        refine ⟨12022194729937077280791361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16029592973249436374388481 12022194729937077280791361)
        ·
          refine ⟨9016646047452807960593521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12022194729937077280791361 9016646047452807960593521)
          ·
            refine ⟨6762484535589605970445141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9016646047452807960593521 6762484535589605970445141)
            ·
              refine ⟨39623932825720347483077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6762484535589605970445141 39623932825720347483077)
              ·
                rfl

theorem cell22_3125277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 9].length) (baseStart_3125277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125277 prefixEnd_3125277 := by exact prefixLift 3125277
  have htrace : WordTrace (prefixWord ++ tailWord_3125277) baseStart_3125277 baseEnd_3125277 := by
    simpa [prefixWord, tailWord_3125277, baseEnd_3125277] using wordTrace_append hprefix tailTrace_3125277
  have hstable : (prefixWord ++ tailWord_3125277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125277).length < 2 ^ (prefixWord ++ tailWord_3125277).sum := by decide
  have hdescent : baseEnd_3125277 < baseStart_3125277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125309 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 3, 3]
def baseStart_3125309 : Nat := 118140960795 + 3125309 * 2 ^ 59
def prefixEnd_3125309 : Nat := 4983230072969 + 3 ^ 40 * 3125309 * 2
def baseEnd_3125309 : Nat := 1069857140548411965242981

theorem tailTrace_3125309 : CollatzResearch.WordTrace tailWord_3125309 prefixEnd_3125309 1069857140548411965242981 := by
  unfold tailWord_3125309
  simp only [CollatzResearch.WordTrace]
  refine ⟨113989383834546728127482981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75992922556364485418321987 113989383834546728127482981)
  ·
    refine ⟨21373009468977511523903059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113989383834546728127482981 21373009468977511523903059)
    ·
      refine ⟨32059514203466267285854589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21373009468977511523903059 32059514203466267285854589)
      ·
        refine ⟨12022317826299850232195471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32059514203466267285854589 12022317826299850232195471)
        ·
          refine ⟨18033476739449775348293207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12022317826299850232195471 18033476739449775348293207)
          ·
            refine ⟨27050215109174663022439811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18033476739449775348293207 27050215109174663022439811)
            ·
              refine ⟨40575322663761994533659717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27050215109174663022439811 40575322663761994533659717)
              ·
                refine ⟨7607872999455373975061197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40575322663761994533659717 7607872999455373975061197)
                ·
                  refine ⟨2852952374795765240647949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7607872999455373975061197 2852952374795765240647949)
                  ·
                    refine ⟨1069857140548411965242981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2852952374795765240647949 1069857140548411965242981)
                    ·
                      rfl

theorem cell22_3125309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_3125309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125309 prefixEnd_3125309 := by exact prefixLift 3125309
  have htrace : WordTrace (prefixWord ++ tailWord_3125309) baseStart_3125309 baseEnd_3125309 := by
    simpa [prefixWord, tailWord_3125309, baseEnd_3125309] using wordTrace_append hprefix tailTrace_3125309
  have hstable : (prefixWord ++ tailWord_3125309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125309).length < 2 ^ (prefixWord ++ tailWord_3125309).sum := by decide
  have hdescent : baseEnd_3125309 < baseStart_3125309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125356 : List Nat := [2, 2, 1, 1, 3, 5, 2, 1, 5]
def baseStart_3125356 : Nat := 118140960795 + 3125356 * 2 ^ 59
def prefixEnd_3125356 : Nat := 4983230072969 + 3 ^ 40 * 3125356 * 2
def baseEnd_3125356 : Nat := 356624409869639836439279

theorem tailTrace_3125356 : CollatzResearch.WordTrace tailWord_3125356 prefixEnd_3125356 356624409869639836439279 := by
  unfold tailWord_3125356
  simp only [CollatzResearch.WordTrace]
  refine ⟨56995549032688227577221961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75994065376917636769629281 56995549032688227577221961)
  ·
    refine ⟨42746661774516170682916471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56995549032688227577221961 42746661774516170682916471)
    ·
      refine ⟨64119992661774256024374707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42746661774516170682916471 64119992661774256024374707)
      ·
        refine ⟨96179988992661384036562061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64119992661774256024374707 96179988992661384036562061)
        ·
          refine ⟨36067495872248019013710773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96179988992661384036562061 36067495872248019013710773)
          ·
            refine ⟨3381327738023251782535385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36067495872248019013710773 3381327738023251782535385)
            ·
              refine ⟨2535995803517438836901539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3381327738023251782535385 2535995803517438836901539)
              ·
                refine ⟨3803993705276158255352309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535995803517438836901539 3803993705276158255352309)
                ·
                  refine ⟨356624409869639836439279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3803993705276158255352309 356624409869639836439279)
                  ·
                    rfl

theorem cell22_3125356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_3125356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125356 prefixEnd_3125356 := by exact prefixLift 3125356
  have htrace : WordTrace (prefixWord ++ tailWord_3125356) baseStart_3125356 baseEnd_3125356 := by
    simpa [prefixWord, tailWord_3125356, baseEnd_3125356] using wordTrace_append hprefix tailTrace_3125356
  have hstable : (prefixWord ++ tailWord_3125356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125356).length < 2 ^ (prefixWord ++ tailWord_3125356).sum := by decide
  have hdescent : baseEnd_3125356 < baseStart_3125356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125369 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 3, 4]
def baseStart_3125369 : Nat := 118140960795 + 3125369 * 2 ^ 59
def prefixEnd_3125369 : Nat := 4983230072969 + 3 ^ 40 * 3125369 * 2
def baseEnd_3125369 : Nat := 1069877679774591808742797

theorem tailTrace_3125369 : CollatzResearch.WordTrace tailWord_3125369 prefixEnd_3125369 1069877679774591808742797 := by
  unfold tailWord_3125369
  simp only [CollatzResearch.WordTrace]
  refine ⟨113991572214329358374667161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75994381476219572249778107 113991572214329358374667161)
  ·
    refine ⟨85493679160747018781000371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113991572214329358374667161 85493679160747018781000371)
    ·
      refine ⟨128240518741120528171500557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85493679160747018781000371 128240518741120528171500557)
      ·
        refine ⟨48090194527920198064312709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128240518741120528171500557 48090194527920198064312709)
        ·
          refine ⟨9016911473985037137058633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48090194527920198064312709 9016911473985037137058633)
          ·
            refine ⟨6762683605488777852793975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9016911473985037137058633 6762683605488777852793975)
            ·
              refine ⟨10144025408233166779190963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6762683605488777852793975 10144025408233166779190963)
              ·
                refine ⟨15216038112349750168786445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10144025408233166779190963 15216038112349750168786445)
                ·
                  refine ⟨5706014292131156313294917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15216038112349750168786445 5706014292131156313294917)
                  ·
                    refine ⟨1069877679774591808742797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5706014292131156313294917 1069877679774591808742797)
                    ·
                      rfl

theorem cell22_3125369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_3125369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125369 prefixEnd_3125369 := by exact prefixLift 3125369
  have htrace : WordTrace (prefixWord ++ tailWord_3125369) baseStart_3125369 baseEnd_3125369 := by
    simpa [prefixWord, tailWord_3125369, baseEnd_3125369] using wordTrace_append hprefix tailTrace_3125369
  have hstable : (prefixWord ++ tailWord_3125369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125369).length < 2 ^ (prefixWord ++ tailWord_3125369).sum := by decide
  have hdescent : baseEnd_3125369 < baseStart_3125369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125431 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 2, 4]
def baseStart_3125431 : Nat := 118140960795 + 3125431 * 2 ^ 59
def prefixEnd_3125431 : Nat := 4983230072969 + 3 ^ 40 * 3125431 * 2
def baseEnd_3125431 : Nat := 1069898903641644313692607

theorem tailTrace_3125431 : CollatzResearch.WordTrace tailWord_3125431 prefixEnd_3125431 1069898903641644313692607 := by
  unfold tailWord_3125431
  simp only [CollatzResearch.WordTrace]
  refine ⟨113993833540104742963424147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75995889026736495308949431 113993833540104742963424147)
  ·
    refine ⟨170990750310157114445136221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113993833540104742963424147 170990750310157114445136221)
    ·
      refine ⟨64121531366308917916926083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170990750310157114445136221 64121531366308917916926083)
      ·
        refine ⟨96182297049463376875389125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64121531366308917916926083 96182297049463376875389125)
        ·
          refine ⟨18034180696774383164135461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96182297049463376875389125 18034180696774383164135461)
          ·
            refine ⟨3381408880645196843275399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18034180696774383164135461 3381408880645196843275399)
            ·
              refine ⟨5072113320967795264913099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3381408880645196843275399 5072113320967795264913099)
              ·
                refine ⟨7608169981451692897369649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5072113320967795264913099 7608169981451692897369649)
                ·
                  refine ⟨5706127486088769673027237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7608169981451692897369649 5706127486088769673027237)
                  ·
                    refine ⟨1069898903641644313692607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5706127486088769673027237 1069898903641644313692607)
                    ·
                      rfl

theorem cell22_3125431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_3125431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125431 prefixEnd_3125431 := by exact prefixLift 3125431
  have htrace : WordTrace (prefixWord ++ tailWord_3125431) baseStart_3125431 baseEnd_3125431 := by
    simpa [prefixWord, tailWord_3125431, baseEnd_3125431] using wordTrace_append hprefix tailTrace_3125431
  have hstable : (prefixWord ++ tailWord_3125431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125431).length < 2 ^ (prefixWord ++ tailWord_3125431).sum := by decide
  have hdescent : baseEnd_3125431 < baseStart_3125431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125538 : List Nat := [3, 3, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_3125538 : Nat := 118140960795 + 3125538 * 2 ^ 59
def prefixEnd_3125538 : Nat := 4983230072969 + 3 ^ 40 * 3125538 * 2
def baseEnd_3125538 : Nat := 1069935531928331701267279

theorem tailTrace_3125538 : CollatzResearch.WordTrace tailWord_3125538 prefixEnd_3125538 1069935531928331701267279 := by
  unfold tailWord_3125538
  simp only [CollatzResearch.WordTrace]
  refine ⟨28499434037679275059392317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75998490767144733491712845 28499434037679275059392317)
  ·
    refine ⟨10687287764129728147272119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28499434037679275059392317 10687287764129728147272119)
    ·
      refine ⟨16030931646194592220908179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10687287764129728147272119 16030931646194592220908179)
      ·
        refine ⟨24046397469291888331362269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16030931646194592220908179 24046397469291888331362269)
        ·
          refine ⟨9017399050984458124260851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24046397469291888331362269 9017399050984458124260851)
          ·
            refine ⟨13526098576476687186391277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9017399050984458124260851 13526098576476687186391277)
            ·
              refine ⟨5072286966178757694896729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13526098576476687186391277 5072286966178757694896729)
              ·
                refine ⟨3804215224634068271172547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5072286966178757694896729 3804215224634068271172547)
                ·
                  refine ⟨5706322836951102406758821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3804215224634068271172547 5706322836951102406758821)
                  ·
                    refine ⟨1069935531928331701267279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5706322836951102406758821 1069935531928331701267279)
                    ·
                      rfl

theorem cell22_3125538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_3125538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125538 prefixEnd_3125538 := by exact prefixLift 3125538
  have htrace : WordTrace (prefixWord ++ tailWord_3125538) baseStart_3125538 baseEnd_3125538 := by
    simpa [prefixWord, tailWord_3125538, baseEnd_3125538] using wordTrace_append hprefix tailTrace_3125538
  have hstable : (prefixWord ++ tailWord_3125538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125538).length < 2 ^ (prefixWord ++ tailWord_3125538).sum := by decide
  have hdescent : baseEnd_3125538 < baseStart_3125538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125594 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 4, 6]
def baseStart_3125594 : Nat := 118140960795 + 3125594 * 2 ^ 59
def prefixEnd_3125594 : Nat := 4983230072969 + 3 ^ 40 * 3125594 * 2
def baseEnd_3125594 : Nat := 1069954701872766221867107

theorem tailTrace_3125594 : CollatzResearch.WordTrace tailWord_3125594 prefixEnd_3125594 1069954701872766221867107 := by
  unfold tailWord_3125594
  simp only [CollatzResearch.WordTrace]
  refine ⟨28499944659628555450401959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75999852425676147867738557 28499944659628555450401959)
  ·
    refine ⟨42749916989442833175602939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28499944659628555450401959 42749916989442833175602939)
    ·
      refine ⟨64124875484164249763404409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42749916989442833175602939 64124875484164249763404409)
      ·
        refine ⟨48093656613123187322553307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64124875484164249763404409 48093656613123187322553307)
        ·
          refine ⟨72140484919684780983829961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48093656613123187322553307 72140484919684780983829961)
          ·
            refine ⟨54105363689763585737872471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72140484919684780983829961 54105363689763585737872471)
            ·
              refine ⟨81158045534645378606808707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54105363689763585737872471 81158045534645378606808707)
              ·
                refine ⟨121737068301968067910213061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81158045534645378606808707 121737068301968067910213061)
                ·
                  refine ⟨22825700306619012733164949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121737068301968067910213061 22825700306619012733164949)
                  ·
                    refine ⟨1069954701872766221867107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22825700306619012733164949 1069954701872766221867107)
                    ·
                      rfl

theorem cell22_3125594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_3125594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125594 prefixEnd_3125594 := by exact prefixLift 3125594
  have htrace : WordTrace (prefixWord ++ tailWord_3125594) baseStart_3125594 baseEnd_3125594 := by
    simpa [prefixWord, tailWord_3125594, baseEnd_3125594] using wordTrace_append hprefix tailTrace_3125594
  have hstable : (prefixWord ++ tailWord_3125594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125594).length < 2 ^ (prefixWord ++ tailWord_3125594).sum := by decide
  have hdescent : baseEnd_3125594 < baseStart_3125594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125600 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 2, 4]
def baseStart_3125600 : Nat := 118140960795 + 3125600 * 2 ^ 59
def prefixEnd_3125600 : Nat := 4983230072969 + 3 ^ 40 * 3125600 * 2
def baseEnd_3125600 : Nat := 1069956755795384206217089

theorem tailTrace_3125600 : CollatzResearch.WordTrace tailWord_3125600 prefixEnd_3125600 1069956755795384206217089 := by
  unfold tailWord_3125600
  simp only [CollatzResearch.WordTrace]
  refine ⟨56999998738246242413163127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75999998317661656550884169 56999998738246242413163127)
  ·
    refine ⟨85499998107369363619744691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56999998738246242413163127 85499998107369363619744691)
    ·
      refine ⟨128249997161054045429617037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85499998107369363619744691 128249997161054045429617037)
      ·
        refine ⟨48093748935395267036106389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128249997161054045429617037 48093748935395267036106389)
        ·
          refine ⟨2254394481346653142317487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48093748935395267036106389 2254394481346653142317487)
          ·
            refine ⟨3381591722019979713476231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254394481346653142317487 3381591722019979713476231)
            ·
              refine ⟨5072387583029969570214347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3381591722019979713476231 5072387583029969570214347)
              ·
                refine ⟨7608581374544954355321521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5072387583029969570214347 7608581374544954355321521)
                ·
                  refine ⟨5706436030908715766491141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7608581374544954355321521 5706436030908715766491141)
                  ·
                    refine ⟨1069956755795384206217089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5706436030908715766491141 1069956755795384206217089)
                    ·
                      rfl

theorem cell22_3125600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 2, 4].length) (baseStart_3125600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125600 prefixEnd_3125600 := by exact prefixLift 3125600
  have htrace : WordTrace (prefixWord ++ tailWord_3125600) baseStart_3125600 baseEnd_3125600 := by
    simpa [prefixWord, tailWord_3125600, baseEnd_3125600] using wordTrace_append hprefix tailTrace_3125600
  have hstable : (prefixWord ++ tailWord_3125600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125600).length < 2 ^ (prefixWord ++ tailWord_3125600).sum := by decide
  have hdescent : baseEnd_3125600 < baseStart_3125600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125609 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 7]
def baseStart_3125609 : Nat := 118140960795 + 3125609 * 2 ^ 59
def prefixEnd_3125609 : Nat := 4983230072969 + 3 ^ 40 * 3125609 * 2
def baseEnd_3125609 : Nat := 356653278893103727580687

theorem tailTrace_3125609 : CollatzResearch.WordTrace tailWord_3125609 prefixEnd_3125609 356653278893103727580687 := by
  unfold tailWord_3125609
  simp only [CollatzResearch.WordTrace]
  refine ⟨114000325733459879363403881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76000217155639919575602587 114000325733459879363403881)
  ·
    refine ⟨85500244300094909522552911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114000325733459879363403881 85500244300094909522552911)
    ·
      refine ⟨128250366450142364283829367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85500244300094909522552911 128250366450142364283829367)
      ·
        refine ⟨192375549675213546425744051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128250366450142364283829367 192375549675213546425744051)
        ·
          refine ⟨288563324512820319638616077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192375549675213546425744051 288563324512820319638616077)
          ·
            refine ⟨108211246692307619864481029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288563324512820319638616077 108211246692307619864481029)
            ·
              refine ⟨20289608754807678724590193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108211246692307619864481029 20289608754807678724590193)
              ·
                refine ⟨15217206566105759043442645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20289608754807678724590193 15217206566105759043442645)
                ·
                  refine ⟨356653278893103727580687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15217206566105759043442645 356653278893103727580687)
                  ·
                    rfl

theorem cell22_3125609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 7].length) (baseStart_3125609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125609 prefixEnd_3125609 := by exact prefixLift 3125609
  have htrace : WordTrace (prefixWord ++ tailWord_3125609) baseStart_3125609 baseEnd_3125609 := by
    simpa [prefixWord, tailWord_3125609, baseEnd_3125609] using wordTrace_append hprefix tailTrace_3125609
  have hstable : (prefixWord ++ tailWord_3125609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125609).length < 2 ^ (prefixWord ++ tailWord_3125609).sum := by decide
  have hdescent : baseEnd_3125609 < baseStart_3125609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125641 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 2, 5]
def baseStart_3125641 : Nat := 118140960795 + 3125641 * 2 ^ 59
def prefixEnd_3125641 : Nat := 4983230072969 + 3 ^ 40 * 3125641 * 2
def baseEnd_3125641 : Nat := 1069970790933273765941963

theorem tailTrace_3125641 : CollatzResearch.WordTrace tailWord_3125641 prefixEnd_3125641 1069970790933273765941963 := by
  unfold tailWord_3125641
  simp only [CollatzResearch.WordTrace]
  refine ⟨114001492869343948828568777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76000995246229299219045851 114001492869343948828568777)
  ·
    refine ⟨85501119652007961621426583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114001492869343948828568777 85501119652007961621426583)
    ·
      refine ⟨128251679478011942432139875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85501119652007961621426583 128251679478011942432139875)
      ·
        refine ⟨192377519217017913648209813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128251679478011942432139875 192377519217017913648209813)
        ·
          refine ⟨9017696213297714702259835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 192377519217017913648209813 9017696213297714702259835)
          ·
            refine ⟨13526544319946572053389753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9017696213297714702259835 13526544319946572053389753)
            ·
              refine ⟨10144908239959929040042315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13526544319946572053389753 10144908239959929040042315)
              ·
                refine ⟨15217362359939893560063473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10144908239959929040042315 15217362359939893560063473)
                ·
                  refine ⟨11413021769954920170047605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15217362359939893560063473 11413021769954920170047605)
                  ·
                    refine ⟨1069970790933273765941963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11413021769954920170047605 1069970790933273765941963)
                    ·
                      rfl

theorem cell22_3125641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_3125641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125641 prefixEnd_3125641 := by exact prefixLift 3125641
  have htrace : WordTrace (prefixWord ++ tailWord_3125641) baseStart_3125641 baseEnd_3125641 := by
    simpa [prefixWord, tailWord_3125641, baseEnd_3125641] using wordTrace_append hprefix tailTrace_3125641
  have hstable : (prefixWord ++ tailWord_3125641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125641).length < 2 ^ (prefixWord ++ tailWord_3125641).sum := by decide
  have hdescent : baseEnd_3125641 < baseStart_3125641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125643 : List Nat := [1, 1, 1, 1, 4, 5, 3, 1, 5]
def baseStart_3125643 : Nat := 118140960795 + 3125643 * 2 ^ 59
def prefixEnd_3125643 : Nat := 4983230072969 + 3 ^ 40 * 3125643 * 2
def baseEnd_3125643 : Nat := 356657158524715475797319

theorem tailTrace_3125643 : CollatzResearch.WordTrace tailWord_3125643 prefixEnd_3125643 356657158524715475797319 := by
  unfold tailWord_3125643
  simp only [CollatzResearch.WordTrace]
  refine ⟨114001565815336703170141583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76001043876891135446761055 114001565815336703170141583)
  ·
    refine ⟨171002348723005054755212375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114001565815336703170141583 171002348723005054755212375)
    ·
      refine ⟨256503523084507582132818563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171002348723005054755212375 256503523084507582132818563)
      ·
        refine ⟨384755284626761373199227845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256503523084507582132818563 384755284626761373199227845)
        ·
          refine ⟨72141615867517757474855221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384755284626761373199227845 72141615867517757474855221)
          ·
            refine ⟨6763276487579789763267677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72141615867517757474855221 6763276487579789763267677)
            ·
              refine ⟨2536228682842421161225379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6763276487579789763267677 2536228682842421161225379)
              ·
                refine ⟨3804343024263631741838069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2536228682842421161225379 3804343024263631741838069)
                ·
                  refine ⟨356657158524715475797319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3804343024263631741838069 356657158524715475797319)
                  ·
                    rfl

theorem cell22_3125643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 5].length) (baseStart_3125643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125643 prefixEnd_3125643 := by exact prefixLift 3125643
  have htrace : WordTrace (prefixWord ++ tailWord_3125643) baseStart_3125643 baseEnd_3125643 := by
    simpa [prefixWord, tailWord_3125643, baseEnd_3125643] using wordTrace_append hprefix tailTrace_3125643
  have hstable : (prefixWord ++ tailWord_3125643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125643).length < 2 ^ (prefixWord ++ tailWord_3125643).sum := by decide
  have hdescent : baseEnd_3125643 < baseStart_3125643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125733 : List Nat := [1, 3, 1, 5, 3, 9]
def baseStart_3125733 : Nat := 118140960795 + 3125733 * 2 ^ 59
def prefixEnd_3125733 : Nat := 4983230072969 + 3 ^ 40 * 3125733 * 2
def baseEnd_3125733 : Nat := 13209904745844644353601

theorem tailTrace_3125733 : CollatzResearch.WordTrace tailWord_3125733 prefixEnd_3125733 13209904745844644353601 := by
  unfold tailWord_3125733
  simp only [CollatzResearch.WordTrace]
  refine ⟨114004848385010648540917853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76003232256673765693945235 114004848385010648540917853)
  ·
    refine ⟨42751818144378993202844195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114004848385010648540917853 42751818144378993202844195)
    ·
      refine ⟨64127727216568489804266293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42751818144378993202844195 64127727216568489804266293)
      ·
        refine ⟨6011974426553295919149965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64127727216568489804266293 6011974426553295919149965)
        ·
          refine ⟨2254490409957485969681237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6011974426553295919149965 2254490409957485969681237)
          ·
            refine ⟨13209904745844644353601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2254490409957485969681237 13209904745844644353601)
            ·
              rfl

theorem cell22_3125733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 9].length) (baseStart_3125733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125733 prefixEnd_3125733 := by exact prefixLift 3125733
  have htrace : WordTrace (prefixWord ++ tailWord_3125733) baseStart_3125733 baseEnd_3125733 := by
    simpa [prefixWord, tailWord_3125733, baseEnd_3125733] using wordTrace_append hprefix tailTrace_3125733
  have hstable : (prefixWord ++ tailWord_3125733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125733).length < 2 ^ (prefixWord ++ tailWord_3125733).sum := by decide
  have hdescent : baseEnd_3125733 < baseStart_3125733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125795 : List Nat := [1, 1, 1, 4, 4, 3, 1, 2, 5]
def baseStart_3125795 : Nat := 118140960795 + 3125795 * 2 ^ 59
def prefixEnd_3125795 : Nat := 4983230072969 + 3 ^ 40 * 3125795 * 2
def baseEnd_3125795 : Nat := 356674502760156232530497

theorem tailTrace_3125795 : CollatzResearch.WordTrace tailWord_3125795 prefixEnd_3125795 356674502760156232530497 := by
  unfold tailWord_3125795
  simp only [CollatzResearch.WordTrace]
  refine ⟨114007109710786033129674839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76004739807190688753116559 114007109710786033129674839)
  ·
    refine ⟨171010664566179049694512259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114007109710786033129674839 171010664566179049694512259)
    ·
      refine ⟨256515996849268574541768389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171010664566179049694512259 256515996849268574541768389)
      ·
        refine ⟨48096749409237857726581573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256515996849268574541768389 48096749409237857726581573)
        ·
          refine ⟨9018140514232098323734045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48096749409237857726581573 9018140514232098323734045)
          ·
            refine ⟨3381802692837036871400267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9018140514232098323734045 3381802692837036871400267)
            ·
              refine ⟨5072704039255555307100401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3381802692837036871400267 5072704039255555307100401)
              ·
                refine ⟨3804528029441666480325301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5072704039255555307100401 3804528029441666480325301)
                ·
                  refine ⟨356674502760156232530497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3804528029441666480325301 356674502760156232530497)
                  ·
                    rfl

theorem cell22_3125795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 5].length) (baseStart_3125795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125795 prefixEnd_3125795 := by exact prefixLift 3125795
  have htrace : WordTrace (prefixWord ++ tailWord_3125795) baseStart_3125795 baseEnd_3125795 := by
    simpa [prefixWord, tailWord_3125795, baseEnd_3125795] using wordTrace_append hprefix tailTrace_3125795
  have hstable : (prefixWord ++ tailWord_3125795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125795).length < 2 ^ (prefixWord ++ tailWord_3125795).sum := by decide
  have hdescent : baseEnd_3125795 < baseStart_3125795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125799 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 3, 3]
def baseStart_3125799 : Nat := 118140960795 + 3125799 * 2 ^ 59
def prefixEnd_3125799 : Nat := 4983230072969 + 3 ^ 40 * 3125799 * 2
def baseEnd_3125799 : Nat := 1070024877562214020491479

theorem tailTrace_3125799 : CollatzResearch.WordTrace tailWord_3125799 prefixEnd_3125799 1070024877562214020491479 := by
  unfold tailWord_3125799
  simp only [CollatzResearch.WordTrace]
  refine ⟨114007255602771541812820451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76004837068514361208546967 114007255602771541812820451)
  ·
    refine ⟨171010883404157312719230677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114007255602771541812820451 171010883404157312719230677)
    ·
      refine ⟨4008067579784937016856969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 171010883404157312719230677 4008067579784937016856969)
      ·
        refine ⟨3006050684838702762642727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4008067579784937016856969 3006050684838702762642727)
        ·
          refine ⟨4509076027258054143964091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3006050684838702762642727 4509076027258054143964091)
          ·
            refine ⟨6763614040887081215946137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4509076027258054143964091 6763614040887081215946137)
            ·
              refine ⟨5072710530665310911959603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6763614040887081215946137 5072710530665310911959603)
              ·
                refine ⟨7609065795997966367939405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5072710530665310911959603 7609065795997966367939405)
                ·
                  refine ⟨2853399673499237387977277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7609065795997966367939405 2853399673499237387977277)
                  ·
                    refine ⟨1070024877562214020491479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2853399673499237387977277 1070024877562214020491479)
                    ·
                      rfl

theorem cell22_3125799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_3125799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125799 prefixEnd_3125799 := by exact prefixLift 3125799
  have htrace : WordTrace (prefixWord ++ tailWord_3125799) baseStart_3125799 baseEnd_3125799 := by
    simpa [prefixWord, tailWord_3125799, baseEnd_3125799] using wordTrace_append hprefix tailTrace_3125799
  have hstable : (prefixWord ++ tailWord_3125799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125799).length < 2 ^ (prefixWord ++ tailWord_3125799).sum := by decide
  have hdescent : baseEnd_3125799 < baseStart_3125799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125825 : List Nat := [1, 2, 5, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3125825 : Nat := 118140960795 + 3125825 * 2 ^ 59
def prefixEnd_3125825 : Nat := 4983230072969 + 3 ^ 40 * 3125825 * 2
def baseEnd_3125825 : Nat := 1070033777893558619341399

theorem tailTrace_3125825 : CollatzResearch.WordTrace tailWord_3125825 prefixEnd_3125825 1070033777893558619341399 := by
  unfold tailWord_3125825
  simp only [CollatzResearch.WordTrace]
  refine ⟨114008203900677348253266929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76005469267118232168844619 114008203900677348253266929)
  ·
    refine ⟨85506152925508011189950197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114008203900677348253266929 85506152925508011189950197)
    ·
      refine ⟨8016201836766376049057831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85506152925508011189950197 8016201836766376049057831)
      ·
        refine ⟨12024302755149564073586747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8016201836766376049057831 12024302755149564073586747)
        ·
          refine ⟨18036454132724346110380121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12024302755149564073586747 18036454132724346110380121)
          ·
            refine ⟨13527340599543259582785091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18036454132724346110380121 13527340599543259582785091)
            ·
              refine ⟨20291010899314889374177637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13527340599543259582785091 20291010899314889374177637)
              ·
                refine ⟨3804564543621541757658307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20291010899314889374177637 3804564543621541757658307)
                ·
                  refine ⟨5706846815432312636487461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3804564543621541757658307 5706846815432312636487461)
                  ·
                    refine ⟨1070033777893558619341399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5706846815432312636487461 1070033777893558619341399)
                    ·
                      rfl

theorem cell22_3125825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3125825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125825 prefixEnd_3125825 := by exact prefixLift 3125825
  have htrace : WordTrace (prefixWord ++ tailWord_3125825) baseStart_3125825 baseEnd_3125825 := by
    simpa [prefixWord, tailWord_3125825, baseEnd_3125825] using wordTrace_append hprefix tailTrace_3125825
  have hstable : (prefixWord ++ tailWord_3125825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125825).length < 2 ^ (prefixWord ++ tailWord_3125825).sum := by decide
  have hdescent : baseEnd_3125825 < baseStart_3125825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125838 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_3125838 : Nat := 118140960795 + 3125838 * 2 ^ 59
def prefixEnd_3125838 : Nat := 4983230072969 + 3 ^ 40 * 3125838 * 2
def baseEnd_3125838 : Nat := 1070038228059230918766359

theorem tailTrace_3125838 : CollatzResearch.WordTrace tailWord_3125838 prefixEnd_3125838 1070038228059230918766359 := by
  unfold tailWord_3125838
  simp only [CollatzResearch.WordTrace]
  refine ⟨14251084756203781434186271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76005785366420167648993445 14251084756203781434186271)
  ·
    refine ⟨21376627134305672151279407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14251084756203781434186271 21376627134305672151279407)
    ·
      refine ⟨32064940701458508226919111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21376627134305672151279407 32064940701458508226919111)
      ·
        refine ⟨48097411052187762340378667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32064940701458508226919111 48097411052187762340378667)
        ·
          refine ⟨72146116578281643510568001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48097411052187762340378667 72146116578281643510568001)
          ·
            refine ⟨54109587433711232632926001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72146116578281643510568001 54109587433711232632926001)
            ·
              refine ⟨40582190575283424474694501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54109587433711232632926001 40582190575283424474694501)
              ·
                refine ⟨7609160732865642089005219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40582190575283424474694501 7609160732865642089005219)
                ·
                  refine ⟨11413741099298463133507829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7609160732865642089005219 11413741099298463133507829)
                  ·
                    refine ⟨1070038228059230918766359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11413741099298463133507829 1070038228059230918766359)
                    ·
                      rfl

theorem cell22_3125838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_3125838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125838 prefixEnd_3125838 := by exact prefixLift 3125838
  have htrace : WordTrace (prefixWord ++ tailWord_3125838) baseStart_3125838 baseEnd_3125838 := by
    simpa [prefixWord, tailWord_3125838, baseEnd_3125838] using wordTrace_append hprefix tailTrace_3125838
  have hstable : (prefixWord ++ tailWord_3125838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125838).length < 2 ^ (prefixWord ++ tailWord_3125838).sum := by decide
  have hdescent : baseEnd_3125838 < baseStart_3125838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125857 : List Nat := [1, 2, 3, 1, 1, 5, 3, 2, 4]
def baseStart_3125857 : Nat := 118140960795 + 3125857 * 2 ^ 59
def prefixEnd_3125857 : Nat := 4983230072969 + 3 ^ 40 * 3125857 * 2
def baseEnd_3125857 : Nat := 356681577382507067513767

theorem tailTrace_3125857 : CollatzResearch.WordTrace tailWord_3125857 prefixEnd_3125857 356681577382507067513767 := by
  unfold tailWord_3125857
  simp only [CollatzResearch.WordTrace]
  refine ⟨114009371036561417718431825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76006247357707611812287883 114009371036561417718431825)
  ·
    refine ⟨85507028277421063288823869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114009371036561417718431825 85507028277421063288823869)
    ·
      refine ⟨32065135604032898733308951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85507028277421063288823869 32065135604032898733308951)
      ·
        refine ⟨48097703406049348099963427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32065135604032898733308951 48097703406049348099963427)
        ·
          refine ⟨72146555109074022149945141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48097703406049348099963427 72146555109074022149945141)
          ·
            refine ⟨6763739541475689576557357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72146555109074022149945141 6763739541475689576557357)
            ·
              refine ⟨2536402328053383591209009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6763739541475689576557357 2536402328053383591209009)
              ·
                refine ⟨1902301746040037693406757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2536402328053383591209009 1902301746040037693406757)
                ·
                  refine ⟨356681577382507067513767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1902301746040037693406757 356681577382507067513767)
                  ·
                    rfl

theorem cell22_3125857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 4].length) (baseStart_3125857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125857 prefixEnd_3125857 := by exact prefixLift 3125857
  have htrace : WordTrace (prefixWord ++ tailWord_3125857) baseStart_3125857 baseEnd_3125857 := by
    simpa [prefixWord, tailWord_3125857, baseEnd_3125857] using wordTrace_append hprefix tailTrace_3125857
  have hstable : (prefixWord ++ tailWord_3125857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125857).length < 2 ^ (prefixWord ++ tailWord_3125857).sum := by decide
  have hdescent : baseEnd_3125857 < baseStart_3125857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125872 : List Nat := [2, 1, 1, 1, 7, 1, 1, 3, 2, 3]
def baseStart_3125872 : Nat := 118140960795 + 3125872 * 2 ^ 59
def prefixEnd_3125872 : Nat := 4983230072969 + 3 ^ 40 * 3125872 * 2
def baseEnd_3125872 : Nat := 1070049866954066163416255

theorem tailTrace_3125872 : CollatzResearch.WordTrace tailWord_3125872 prefixEnd_3125872 1070049866954066163416255 := by
  unfold tailWord_3125872
  simp only [CollatzResearch.WordTrace]
  refine ⟨57004959065753537640113935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76006612087671383520151913 57004959065753537640113935)
  ·
    refine ⟨85507438598630306460170903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57004959065753537640113935 85507438598630306460170903)
    ·
      refine ⟨128261157897945459690256355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85507438598630306460170903 128261157897945459690256355)
      ·
        refine ⟨192391736846918189535384533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128261157897945459690256355 192391736846918189535384533)
        ·
          refine ⟨4509181332349645067235575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 192391736846918189535384533 4509181332349645067235575)
          ·
            refine ⟨6763771998524467600853363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4509181332349645067235575 6763771998524467600853363)
            ·
              refine ⟨10145657997786701401280045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6763771998524467600853363 10145657997786701401280045)
              ·
                refine ⟨3804621749170013025480017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10145657997786701401280045 3804621749170013025480017)
                ·
                  refine ⟨2853466311877509769110013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3804621749170013025480017 2853466311877509769110013)
                  ·
                    refine ⟨1070049866954066163416255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2853466311877509769110013 1070049866954066163416255)
                    ·
                      rfl

theorem cell22_3125872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 2, 3].length) (baseStart_3125872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125872 prefixEnd_3125872 := by exact prefixLift 3125872
  have htrace : WordTrace (prefixWord ++ tailWord_3125872) baseStart_3125872 baseEnd_3125872 := by
    simpa [prefixWord, tailWord_3125872, baseEnd_3125872] using wordTrace_append hprefix tailTrace_3125872
  have hstable : (prefixWord ++ tailWord_3125872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125872).length < 2 ^ (prefixWord ++ tailWord_3125872).sum := by decide
  have hdescent : baseEnd_3125872 < baseStart_3125872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125934 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 3, 3]
def baseStart_3125934 : Nat := 118140960795 + 3125934 * 2 ^ 59
def prefixEnd_3125934 : Nat := 4983230072969 + 3 ^ 40 * 3125934 * 2
def baseEnd_3125934 : Nat := 1070071090821118668366065

theorem tailTrace_3125934 : CollatzResearch.WordTrace tailWord_3125934 prefixEnd_3125934 1070071090821118668366065 := by
  unfold tailWord_3125934
  simp only [CollatzResearch.WordTrace]
  refine ⟨14251522432160307483623107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76008119638188306579323237 14251522432160307483623107)
  ·
    refine ⟨21377283648240461225434661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14251522432160307483623107 21377283648240461225434661)
    ·
      refine ⟨4008240684045086479768999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21377283648240461225434661 4008240684045086479768999)
      ·
        refine ⟨6012361026067629719653499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4008240684045086479768999 6012361026067629719653499)
        ·
          refine ⟨9018541539101444579480249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6012361026067629719653499 9018541539101444579480249)
          ·
            refine ⟨6763906154326083434610187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9018541539101444579480249 6763906154326083434610187)
            ·
              refine ⟨10145859231489125151915281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6763906154326083434610187 10145859231489125151915281)
              ·
                refine ⟨7609394423616843863936461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10145859231489125151915281 7609394423616843863936461)
                ·
                  refine ⟨2853522908856316448976173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7609394423616843863936461 2853522908856316448976173)
                  ·
                    refine ⟨1070071090821118668366065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2853522908856316448976173 1070071090821118668366065)
                    ·
                      rfl

theorem cell22_3125934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_3125934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125934 prefixEnd_3125934 := by exact prefixLift 3125934
  have htrace : WordTrace (prefixWord ++ tailWord_3125934) baseStart_3125934 baseEnd_3125934 := by
    simpa [prefixWord, tailWord_3125934, baseEnd_3125934] using wordTrace_append hprefix tailTrace_3125934
  have hstable : (prefixWord ++ tailWord_3125934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125934).length < 2 ^ (prefixWord ++ tailWord_3125934).sum := by decide
  have hdescent : baseEnd_3125934 < baseStart_3125934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125975 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 6]
def baseStart_3125975 : Nat := 118140960795 + 3125975 * 2 ^ 59
def prefixEnd_3125975 : Nat := 4983230072969 + 3 ^ 40 * 3125975 * 2
def baseEnd_3125975 : Nat := 356695041986336076030313

theorem tailTrace_3125975 : CollatzResearch.WordTrace tailWord_3125975 prefixEnd_3125975 356695041986336076030313 := by
  unfold tailWord_3125975
  simp only [CollatzResearch.WordTrace]
  refine ⟨114013674850133923871227379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76009116566755949247484919 114013674850133923871227379)
  ·
    refine ⟨171020512275200885806841069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114013674850133923871227379 171020512275200885806841069)
    ·
      refine ⟨64132692103200332177565401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171020512275200885806841069 64132692103200332177565401)
      ·
        refine ⟨48099519077400249133174051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64132692103200332177565401 48099519077400249133174051)
        ·
          refine ⟨72149278616100373699761077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48099519077400249133174051 72149278616100373699761077)
          ·
            refine ⟨6763994870259410034352601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72149278616100373699761077 6763994870259410034352601)
            ·
              refine ⟨5072996152694557525764451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6763994870259410034352601 5072996152694557525764451)
              ·
                refine ⟨7609494229041836288646677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5072996152694557525764451 7609494229041836288646677)
                ·
                  refine ⟨356695041986336076030313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7609494229041836288646677 356695041986336076030313)
                  ·
                    rfl

theorem cell22_3125975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 6].length) (baseStart_3125975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3125975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3125975 prefixEnd_3125975 := by exact prefixLift 3125975
  have htrace : WordTrace (prefixWord ++ tailWord_3125975) baseStart_3125975 baseEnd_3125975 := by
    simpa [prefixWord, tailWord_3125975, baseEnd_3125975] using wordTrace_append hprefix tailTrace_3125975
  have hstable : (prefixWord ++ tailWord_3125975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125975).length < 2 ^ (prefixWord ++ tailWord_3125975).sum := by decide
  have hdescent : baseEnd_3125975 < baseStart_3125975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126097 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 2, 5]
def baseStart_3126097 : Nat := 118140960795 + 3126097 * 2 ^ 59
def prefixEnd_3126097 : Nat := 4983230072969 + 3 ^ 40 * 3126097 * 2
def baseEnd_3126097 : Nat := 1070126889052240576540565

theorem tailTrace_3126097 : CollatzResearch.WordTrace tailWord_3126097 prefixEnd_3126097 1070126889052240576540565 := by
  unfold tailWord_3126097
  simp only [CollatzResearch.WordTrace]
  refine ⟨114018124555691938707168545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76012083037127959138112363 114018124555691938707168545)
  ·
    refine ⟨85513593416768954030376409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114018124555691938707168545 85513593416768954030376409)
    ·
      refine ⟨64135195062576715522782307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85513593416768954030376409 64135195062576715522782307)
      ·
        refine ⟨96202792593865073284173461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64135195062576715522782307 96202792593865073284173461)
        ·
          refine ⟨4509505902837425310195631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96202792593865073284173461 4509505902837425310195631)
          ·
            refine ⟨6764258854256137965293447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4509505902837425310195631 6764258854256137965293447)
            ·
              refine ⟨10146388281384206947940171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6764258854256137965293447 10146388281384206947940171)
              ·
                refine ⟨15219582422076310421910257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10146388281384206947940171 15219582422076310421910257)
                ·
                  refine ⟨11414686816557232816432693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15219582422076310421910257 11414686816557232816432693)
                  ·
                    refine ⟨1070126889052240576540565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11414686816557232816432693 1070126889052240576540565)
                    ·
                      rfl

theorem cell22_3126097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_3126097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126097 prefixEnd_3126097 := by exact prefixLift 3126097
  have htrace : WordTrace (prefixWord ++ tailWord_3126097) baseStart_3126097 baseEnd_3126097 := by
    simpa [prefixWord, tailWord_3126097, baseEnd_3126097] using wordTrace_append hprefix tailTrace_3126097
  have hstable : (prefixWord ++ tailWord_3126097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126097).length < 2 ^ (prefixWord ++ tailWord_3126097).sum := by decide
  have hdescent : baseEnd_3126097 < baseStart_3126097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126112 : List Nat := [2, 1, 1, 3, 3, 1, 2, 4, 1, 4]
def baseStart_3126112 : Nat := 118140960795 + 3126112 * 2 ^ 59
def prefixEnd_3126112 : Nat := 4983230072969 + 3 ^ 40 * 3126112 * 2
def baseEnd_3126112 : Nat := 1070132023858785537415519

theorem tailTrace_3126112 : CollatzResearch.WordTrace tailWord_3126112 prefixEnd_3126112 1070132023858785537415519 := by
  unfold tailWord_3126112
  simp only [CollatzResearch.WordTrace]
  refine ⟨57009335825318798134482295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76012447767091730845976393 57009335825318798134482295)
  ·
    refine ⟨85514003737978197201723443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57009335825318798134482295 85514003737978197201723443)
    ·
      refine ⟨128271005606967295802585165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85514003737978197201723443 128271005606967295802585165)
      ·
        refine ⟨48101627102612735925969437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128271005606967295802585165 48101627102612735925969437)
        ·
          refine ⟨18038110163479775972238539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48101627102612735925969437 18038110163479775972238539)
          ·
            refine ⟨27057165245219663958357809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18038110163479775972238539 27057165245219663958357809)
            ·
              refine ⟨20292873933914747968768357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27057165245219663958357809 20292873933914747968768357)
              ·
                refine ⟨3804913862609015244144067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20292873933914747968768357 3804913862609015244144067)
                ·
                  refine ⟨5707370793913522866216101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3804913862609015244144067 5707370793913522866216101)
                  ·
                    refine ⟨1070132023858785537415519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5707370793913522866216101 1070132023858785537415519)
                    ·
                      rfl

theorem cell22_3126112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 1, 4].length) (baseStart_3126112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126112 prefixEnd_3126112 := by exact prefixLift 3126112
  have htrace : WordTrace (prefixWord ++ tailWord_3126112) baseStart_3126112 baseEnd_3126112 := by
    simpa [prefixWord, tailWord_3126112, baseEnd_3126112] using wordTrace_append hprefix tailTrace_3126112
  have hstable : (prefixWord ++ tailWord_3126112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126112).length < 2 ^ (prefixWord ++ tailWord_3126112).sum := by decide
  have hdescent : baseEnd_3126112 < baseStart_3126112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126129 : List Nat := [1, 2, 2, 2, 1, 4, 4, 1, 1, 4]
def baseStart_3126129 : Nat := 118140960795 + 3126129 * 2 ^ 59
def prefixEnd_3126129 : Nat := 4983230072969 + 3 ^ 40 * 3126129 * 2
def baseEnd_3126129 : Nat := 1070137843306203159740467

theorem tailTrace_3126129 : CollatzResearch.WordTrace tailWord_3126129 prefixEnd_3126129 1070137843306203159740467 := by
  unfold tailWord_3126129
  simp only [CollatzResearch.WordTrace]
  refine ⟨114019291691576008172333441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76012861127717338781555627 114019291691576008172333441)
  ·
    refine ⟨85514468768682006129250081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114019291691576008172333441 85514468768682006129250081)
    ·
      refine ⟨64135851576511504596937561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85514468768682006129250081 64135851576511504596937561)
      ·
        refine ⟨48101888682383628447703171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64135851576511504596937561 48101888682383628447703171)
        ·
          refine ⟨72152833023575442671554757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48101888682383628447703171 72152833023575442671554757)
          ·
            refine ⟨13528656191920395500916517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72152833023575442671554757 13528656191920395500916517)
            ·
              refine ⟨2536623035985074156421847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13528656191920395500916517 2536623035985074156421847)
              ·
                refine ⟨3804934553977611234632771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2536623035985074156421847 3804934553977611234632771)
                ·
                  refine ⟨5707401830966416851949157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3804934553977611234632771 5707401830966416851949157)
                  ·
                    refine ⟨1070137843306203159740467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5707401830966416851949157 1070137843306203159740467)
                    ·
                      rfl

theorem cell22_3126129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_3126129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126129 prefixEnd_3126129 := by exact prefixLift 3126129
  have htrace : WordTrace (prefixWord ++ tailWord_3126129) baseStart_3126129 baseEnd_3126129 := by
    simpa [prefixWord, tailWord_3126129, baseEnd_3126129] using wordTrace_append hprefix tailTrace_3126129
  have hstable : (prefixWord ++ tailWord_3126129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126129).length < 2 ^ (prefixWord ++ tailWord_3126129).sum := by decide
  have hdescent : baseEnd_3126129 < baseStart_3126129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126214 : List Nat := [6, 1, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3126214 : Nat := 118140960795 + 3126214 * 2 ^ 59
def prefixEnd_3126214 : Nat := 4983230072969 + 3 ^ 40 * 3126214 * 2
def baseEnd_3126214 : Nat := 1070166940543291271365207

theorem tailTrace_3126214 : CollatzResearch.WordTrace tailWord_3126214 prefixEnd_3126214 1070166940543291271365207 := by
  unfold tailWord_3126214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3563199746758377115286803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76014927930845378459451797 3563199746758377115286803)
  ·
    refine ⟨5344799620137565672930205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3563199746758377115286803 5344799620137565672930205)
    ·
      refine ⟨2004299857551587127348827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5344799620137565672930205 2004299857551587127348827)
      ·
        refine ⟨3006449786327380691023241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2004299857551587127348827 3006449786327380691023241)
        ·
          refine ⟨2254837339745535518267431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3006449786327380691023241 2254837339745535518267431)
          ·
            refine ⟨3382256009618303277401147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254837339745535518267431 3382256009618303277401147)
            ·
              refine ⟨5073384014427454916101721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3382256009618303277401147 5073384014427454916101721)
              ·
                refine ⟨3805038010820591187076291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5073384014427454916101721 3805038010820591187076291)
                ·
                  refine ⟨5707557016230886780614437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3805038010820591187076291 5707557016230886780614437)
                  ·
                    refine ⟨1070166940543291271365207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5707557016230886780614437 1070166940543291271365207)
                    ·
                      rfl

theorem cell22_3126214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3126214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126214 prefixEnd_3126214 := by exact prefixLift 3126214
  have htrace : WordTrace (prefixWord ++ tailWord_3126214) baseStart_3126214 baseEnd_3126214 := by
    simpa [prefixWord, tailWord_3126214, baseEnd_3126214] using wordTrace_append hprefix tailTrace_3126214
  have hstable : (prefixWord ++ tailWord_3126214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126214).length < 2 ^ (prefixWord ++ tailWord_3126214).sum := by decide
  have hdescent : baseEnd_3126214 < baseStart_3126214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126296 : List Nat := [2, 1, 2, 3, 2, 3, 2, 3, 4]
def baseStart_3126296 : Nat := 118140960795 + 3126296 * 2 ^ 59
def prefixEnd_3126296 : Nat := 4983230072969 + 3 ^ 40 * 3126296 * 2
def baseEnd_3126296 : Nat := 356731670273023463604985

theorem tailTrace_3126296 : CollatzResearch.WordTrace tailWord_3126296 prefixEnd_3126296 356731670273023463604985 := by
  unfold tailWord_3126296
  simp only [CollatzResearch.WordTrace]
  refine ⟨57012691340985497846831371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76016921787980663795775161 57012691340985497846831371)
  ·
    refine ⟨85519037011478246770247057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57012691340985497846831371 85519037011478246770247057)
    ·
      refine ⟨64139277758608685077685293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85519037011478246770247057 64139277758608685077685293)
      ·
        refine ⟨24052229159478256904131985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64139277758608685077685293 24052229159478256904131985)
        ·
          refine ⟨18039171869608692678098989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24052229159478256904131985 18039171869608692678098989)
          ·
            refine ⟨6764689451103259754287121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18039171869608692678098989 6764689451103259754287121)
            ·
              refine ⟨5073517088327444815715341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6764689451103259754287121 5073517088327444815715341)
              ·
                refine ⟨1902568908122791805893253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5073517088327444815715341 1902568908122791805893253)
                ·
                  refine ⟨356731670273023463604985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1902568908122791805893253 356731670273023463604985)
                  ·
                    rfl

theorem cell22_3126296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 4].length) (baseStart_3126296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126296 prefixEnd_3126296 := by exact prefixLift 3126296
  have htrace : WordTrace (prefixWord ++ tailWord_3126296) baseStart_3126296 baseEnd_3126296 := by
    simpa [prefixWord, tailWord_3126296, baseEnd_3126296] using wordTrace_append hprefix tailTrace_3126296
  have hstable : (prefixWord ++ tailWord_3126296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126296).length < 2 ^ (prefixWord ++ tailWord_3126296).sum := by decide
  have hdescent : baseEnd_3126296 < baseStart_3126296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126307 : List Nat := [1, 1, 1, 4, 3, 3, 9]
def baseStart_3126307 : Nat := 118140960795 + 3126307 * 2 ^ 59
def prefixEnd_3126307 : Nat := 4983230072969 + 3 ^ 40 * 3126307 * 2
def baseEnd_3126307 : Nat := 39636991716439630695923

theorem tailTrace_3126307 : CollatzResearch.WordTrace tailWord_3126307 prefixEnd_3126307 39636991716439630695923 := by
  unfold tailWord_3126307
  simp only [CollatzResearch.WordTrace]
  refine ⟨114025783884931144572313175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76017189256620763048208783 114025783884931144572313175)
  ·
    refine ⟨171038675827396716858469763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114025783884931144572313175 171038675827396716858469763)
    ·
      refine ⟨256558013741095075287704645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171038675827396716858469763 256558013741095075287704645)
      ·
        refine ⟨48104627576455326616444621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256558013741095075287704645 48104627576455326616444621)
        ·
          refine ⟨18039235341170747481166733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48104627576455326616444621 18039235341170747481166733)
          ·
            refine ⟨6764713252939030305437525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18039235341170747481166733 6764713252939030305437525)
            ·
              refine ⟨39636991716439630695923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6764713252939030305437525 39636991716439630695923)
              ·
                rfl

theorem cell22_3126307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 9].length) (baseStart_3126307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126307 prefixEnd_3126307 := by exact prefixLift 3126307
  have htrace : WordTrace (prefixWord ++ tailWord_3126307) baseStart_3126307 baseEnd_3126307 := by
    simpa [prefixWord, tailWord_3126307, baseEnd_3126307] using wordTrace_append hprefix tailTrace_3126307
  have hstable : (prefixWord ++ tailWord_3126307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126307).length < 2 ^ (prefixWord ++ tailWord_3126307).sum := by decide
  have hdescent : baseEnd_3126307 < baseStart_3126307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126328 : List Nat := [2, 1, 2, 1, 5, 2, 3, 1, 2, 3]
def baseStart_3126328 : Nat := 118140960795 + 3126328 * 2 ^ 59
def prefixEnd_3126328 : Nat := 4983230072969 + 3 ^ 40 * 3126328 * 2
def baseEnd_3126328 : Nat := 1070205965073032974014857

theorem tailTrace_3126328 : CollatzResearch.WordTrace tailWord_3126328 prefixEnd_3126328 1070205965073032974014857 := by
  unfold tailWord_3126328
  simp only [CollatzResearch.WordTrace]
  refine ⟨57013274908927532579413819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76017699878570043439218425 57013274908927532579413819)
  ·
    refine ⟨85519912363391298869120729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57013274908927532579413819 85519912363391298869120729)
    ·
      refine ⟨64139934272543474151840547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85519912363391298869120729 64139934272543474151840547)
      ·
        refine ⟨96209901408815211227760821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64139934272543474151840547 96209901408815211227760821)
        ·
          refine ⟨9019678257076426052602577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96209901408815211227760821 9019678257076426052602577)
          ·
            refine ⟨6764758692807319539451933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9019678257076426052602577 6764758692807319539451933)
            ·
              refine ⟨2536784509802744827294475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6764758692807319539451933 2536784509802744827294475)
              ·
                refine ⟨3805176764704117240941713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2536784509802744827294475 3805176764704117240941713)
                ·
                  refine ⟨2853882573528087930706285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3805176764704117240941713 2853882573528087930706285)
                  ·
                    refine ⟨1070205965073032974014857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2853882573528087930706285 1070205965073032974014857)
                    ·
                      rfl

theorem cell22_3126328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_3126328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126328 prefixEnd_3126328 := by exact prefixLift 3126328
  have htrace : WordTrace (prefixWord ++ tailWord_3126328) baseStart_3126328 baseEnd_3126328 := by
    simpa [prefixWord, tailWord_3126328, baseEnd_3126328] using wordTrace_append hprefix tailTrace_3126328
  have hstable : (prefixWord ++ tailWord_3126328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126328).length < 2 ^ (prefixWord ++ tailWord_3126328).sum := by decide
  have hdescent : baseEnd_3126328 < baseStart_3126328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126339 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 3, 3]
def baseStart_3126339 : Nat := 118140960795 + 3126339 * 2 ^ 59
def prefixEnd_3126339 : Nat := 4983230072969 + 3 ^ 40 * 3126339 * 2
def baseEnd_3126339 : Nat := 1070209730597832611989823

theorem tailTrace_3126339 : CollatzResearch.WordTrace tailWord_3126339 prefixEnd_3126339 1070209730597832611989823 := by
  unfold tailWord_3126339
  simp only [CollatzResearch.WordTrace]
  refine ⟨114026951020815214037478071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76017967347210142691652047 114026951020815214037478071)
  ·
    refine ⟨171040426531222821056217107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114026951020815214037478071 171040426531222821056217107)
    ·
      refine ⟨256560639796834231584325661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171040426531222821056217107 256560639796834231584325661)
      ·
        refine ⟨96210239923812836844122123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256560639796834231584325661 96210239923812836844122123)
        ·
          refine ⟨144315359885719255266183185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96210239923812836844122123 144315359885719255266183185)
          ·
            refine ⟨108236519914289441449637389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144315359885719255266183185 108236519914289441449637389)
            ·
              refine ⟨40588694967858540543614021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108236519914289441449637389 40588694967858540543614021)
              ·
                refine ⟨7610380306473476351927629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40588694967858540543614021 7610380306473476351927629)
                ·
                  refine ⟨2853892614927553631972861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7610380306473476351927629 2853892614927553631972861)
                  ·
                    refine ⟨1070209730597832611989823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2853892614927553631972861 1070209730597832611989823)
                    ·
                      rfl

theorem cell22_3126339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 3].length) (baseStart_3126339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126339 prefixEnd_3126339 := by exact prefixLift 3126339
  have htrace : WordTrace (prefixWord ++ tailWord_3126339) baseStart_3126339 baseEnd_3126339 := by
    simpa [prefixWord, tailWord_3126339, baseEnd_3126339] using wordTrace_append hprefix tailTrace_3126339
  have hstable : (prefixWord ++ tailWord_3126339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126339).length < 2 ^ (prefixWord ++ tailWord_3126339).sum := by decide
  have hdescent : baseEnd_3126339 < baseStart_3126339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126358 : List Nat := [5, 2, 2, 1, 2, 2, 8]
def baseStart_3126358 : Nat := 118140960795 + 3126358 * 2 ^ 59
def prefixEnd_3126358 : Nat := 4983230072969 + 3 ^ 40 * 3126358 * 2
def baseEnd_3126358 : Nat := 39637638321708255398695

theorem tailTrace_3126358 : CollatzResearch.WordTrace tailWord_3126358 prefixEnd_3126358 39637638321708255398695 := by
  unfold tailWord_3126358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7126727750484148767651233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76018429338497586854946485 7126727750484148767651233)
  ·
    refine ⟨5345045812863111575738425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7126727750484148767651233 5345045812863111575738425)
    ·
      refine ⟨4008784359647333681803819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5345045812863111575738425 4008784359647333681803819)
      ·
        refine ⟨6013176539471000522705729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4008784359647333681803819 6013176539471000522705729)
        ·
          refine ⟨4509882404603250392029297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6013176539471000522705729 4509882404603250392029297)
          ·
            refine ⟨3382411803452437794021973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4509882404603250392029297 3382411803452437794021973)
            ·
              refine ⟨39637638321708255398695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3382411803452437794021973 39637638321708255398695)
              ·
                rfl

theorem cell22_3126358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 8].length) (baseStart_3126358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126358 prefixEnd_3126358 := by exact prefixLift 3126358
  have htrace : WordTrace (prefixWord ++ tailWord_3126358) baseStart_3126358 baseEnd_3126358 := by
    simpa [prefixWord, tailWord_3126358, baseEnd_3126358] using wordTrace_append hprefix tailTrace_3126358
  have hstable : (prefixWord ++ tailWord_3126358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126358).length < 2 ^ (prefixWord ++ tailWord_3126358).sum := by decide
  have hdescent : baseEnd_3126358 < baseStart_3126358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126429 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_3126429 : Nat := 118140960795 + 3126429 * 2 ^ 59
def prefixEnd_3126429 : Nat := 4983230072969 + 3 ^ 40 * 3126429 * 2
def baseEnd_3126429 : Nat := 1070240539437102377239547

theorem tailTrace_3126429 : CollatzResearch.WordTrace tailWord_3126429 prefixEnd_3126429 1070240539437102377239547 := by
  unfold tailWord_3126429
  simp only [CollatzResearch.WordTrace]
  refine ⟨114030233590489159408254341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76020155726992772938836227 114030233590489159408254341)
  ·
    refine ⟨21380668798216717389047689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114030233590489159408254341 21380668798216717389047689)
    ·
      refine ⟨16035501598662538041785767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21380668798216717389047689 16035501598662538041785767)
      ·
        refine ⟨24053252397993807062678651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16035501598662538041785767 24053252397993807062678651)
        ·
          refine ⟨36079878596990710594017977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24053252397993807062678651 36079878596990710594017977)
          ·
            refine ⟨27059908947743032945513483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36079878596990710594017977 27059908947743032945513483)
            ·
              refine ⟨40589863421614549418270225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27059908947743032945513483 40589863421614549418270225)
              ·
                refine ⟨30442397566210912063702669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40589863421614549418270225 30442397566210912063702669)
                ·
                  refine ⟨11415899087329092023888501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30442397566210912063702669 11415899087329092023888501)
                  ·
                    refine ⟨1070240539437102377239547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11415899087329092023888501 1070240539437102377239547)
                    ·
                      rfl

theorem cell22_3126429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_3126429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126429 prefixEnd_3126429 := by exact prefixLift 3126429
  have htrace : WordTrace (prefixWord ++ tailWord_3126429) baseStart_3126429 baseEnd_3126429 := by
    simpa [prefixWord, tailWord_3126429, baseEnd_3126429] using wordTrace_append hprefix tailTrace_3126429
  have hstable : (prefixWord ++ tailWord_3126429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126429).length < 2 ^ (prefixWord ++ tailWord_3126429).sum := by decide
  have hdescent : baseEnd_3126429 < baseStart_3126429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126461 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_3126461 : Nat := 118140960795 + 3126461 * 2 ^ 59
def prefixEnd_3126461 : Nat := 4983230072969 + 3 ^ 40 * 3126461 * 2
def baseEnd_3126461 : Nat := 1070251493691064960439449

theorem tailTrace_3126461 : CollatzResearch.WordTrace tailWord_3126461 prefixEnd_3126461 1070251493691064960439449 := by
  unfold tailWord_3126461
  simp only [CollatzResearch.WordTrace]
  refine ⟨114031400726373228873419237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76020933817582152582279491 114031400726373228873419237)
  ·
    refine ⟨21380887636194980413766107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114031400726373228873419237 21380887636194980413766107)
    ·
      refine ⟨32071331454292470620649161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21380887636194980413766107 32071331454292470620649161)
      ·
        refine ⟨24053498590719352965486871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32071331454292470620649161 24053498590719352965486871)
        ·
          refine ⟨36080247886079029448230307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24053498590719352965486871 36080247886079029448230307)
          ·
            refine ⟨54120371829118544172345461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36080247886079029448230307 54120371829118544172345461)
            ·
              refine ⟨5073784858979863516157387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54120371829118544172345461 5073784858979863516157387)
              ·
                refine ⟨7610677288469795274236081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5073784858979863516157387 7610677288469795274236081)
                ·
                  refine ⟨5708007966352346455677061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7610677288469795274236081 5708007966352346455677061)
                  ·
                    refine ⟨1070251493691064960439449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5708007966352346455677061 1070251493691064960439449)
                    ·
                      rfl

theorem cell22_3126461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_3126461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126461 prefixEnd_3126461 := by exact prefixLift 3126461
  have htrace : WordTrace (prefixWord ++ tailWord_3126461) baseStart_3126461 baseEnd_3126461 := by
    simpa [prefixWord, tailWord_3126461, baseEnd_3126461] using wordTrace_append hprefix tailTrace_3126461
  have hstable : (prefixWord ++ tailWord_3126461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126461).length < 2 ^ (prefixWord ++ tailWord_3126461).sum := by decide
  have hdescent : baseEnd_3126461 < baseStart_3126461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126465 : List Nat := [1, 2, 6, 1, 1, 2, 2, 3, 4]
def baseStart_3126465 : Nat := 118140960795 + 3126465 * 2 ^ 59
def prefixEnd_3126465 : Nat := 4983230072969 + 3 ^ 40 * 3126465 * 2
def baseEnd_3126465 : Nat := 356750954324270094446479

theorem tailTrace_3126465 : CollatzResearch.WordTrace tailWord_3126465 prefixEnd_3126465 356750954324270094446479 := by
  unfold tailWord_3126465
  simp only [CollatzResearch.WordTrace]
  refine ⟨114031546618358737556564849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76021031078905825037709899 114031546618358737556564849)
  ·
    refine ⟨85523659963769053167423637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114031546618358737556564849 85523659963769053167423637)
    ·
      refine ⟨4008921560801674367222983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85523659963769053167423637 4008921560801674367222983)
      ·
        refine ⟨6013382341202511550834475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4008921560801674367222983 6013382341202511550834475)
        ·
          refine ⟨9020073511803767326251713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6013382341202511550834475 9020073511803767326251713)
          ·
            refine ⟨6765055133852825494688785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9020073511803767326251713 6765055133852825494688785)
            ·
              refine ⟨5073791350389619121016589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6765055133852825494688785 5073791350389619121016589)
              ·
                refine ⟨1902671756396107170381221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5073791350389619121016589 1902671756396107170381221)
                ·
                  refine ⟨356750954324270094446479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1902671756396107170381221 356750954324270094446479)
                  ·
                    rfl

theorem cell22_3126465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 4].length) (baseStart_3126465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126465 prefixEnd_3126465 := by exact prefixLift 3126465
  have htrace : WordTrace (prefixWord ++ tailWord_3126465) baseStart_3126465 baseEnd_3126465 := by
    simpa [prefixWord, tailWord_3126465, baseEnd_3126465] using wordTrace_append hprefix tailTrace_3126465
  have hstable : (prefixWord ++ tailWord_3126465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126465).length < 2 ^ (prefixWord ++ tailWord_3126465).sum := by decide
  have hdescent : baseEnd_3126465 < baseStart_3126465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126516 : List Nat := [2, 6, 1, 2, 2, 1, 1, 3, 4]
def baseStart_3126516 : Nat := 118140960795 + 3126516 * 2 ^ 59
def prefixEnd_3126516 : Nat := 4983230072969 + 3 ^ 40 * 3126516 * 2
def baseEnd_3126516 : Nat := 356756773771687716771427

theorem tailTrace_3126516 : CollatzResearch.WordTrace tailWord_3126516 prefixEnd_3126516 356756773771687716771427 := by
  unfold tailWord_3126516
  simp only [CollatzResearch.WordTrace]
  refine ⟨57016703370586986633335701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76022271160782648844447601 57016703370586986633335701)
  ·
    refine ⟨2672657970496264998437611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57016703370586986633335701 2672657970496264998437611)
    ·
      refine ⟨4008986955744397497656417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2672657970496264998437611 4008986955744397497656417)
      ·
        refine ⟨3006740216808298123242313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4008986955744397497656417 3006740216808298123242313)
        ·
          refine ⟨2255055162606223592431735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3006740216808298123242313 2255055162606223592431735)
          ·
            refine ⟨3382582743909335388647603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255055162606223592431735 3382582743909335388647603)
            ·
              refine ⟨5073874115864003082971405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3382582743909335388647603 5073874115864003082971405)
              ·
                refine ⟨1902702793449001156114277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5073874115864003082971405 1902702793449001156114277)
                ·
                  refine ⟨356756773771687716771427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1902702793449001156114277 356756773771687716771427)
                  ·
                    rfl

theorem cell22_3126516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_3126516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126516 prefixEnd_3126516 := by exact prefixLift 3126516
  have htrace : WordTrace (prefixWord ++ tailWord_3126516) baseStart_3126516 baseEnd_3126516 := by
    simpa [prefixWord, tailWord_3126516, baseEnd_3126516] using wordTrace_append hprefix tailTrace_3126516
  have hstable : (prefixWord ++ tailWord_3126516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126516).length < 2 ^ (prefixWord ++ tailWord_3126516).sum := by decide
  have hdescent : baseEnd_3126516 < baseStart_3126516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126542 : List Nat := [4, 1, 1, 2, 1, 4, 3, 2, 1, 3]
def baseStart_3126542 : Nat := 118140960795 + 3126542 * 2 ^ 59
def prefixEnd_3126542 : Nat := 4983230072969 + 3 ^ 40 * 3126542 * 2
def baseEnd_3126542 : Nat := 1070279221646407749164201

theorem tailTrace_3126542 : CollatzResearch.WordTrace tailWord_3126542 prefixEnd_3126542 1070279221646407749164201 := by
  unfold tailWord_3126542
  simp only [CollatzResearch.WordTrace]
  refine ⟨14254294379884972463389735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76022903359386519804745253 14254294379884972463389735)
  ·
    refine ⟨21381441569827458695084603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14254294379884972463389735 21381441569827458695084603)
    ·
      refine ⟨32072162354741188042626905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21381441569827458695084603 32072162354741188042626905)
      ·
        refine ⟨24054121766055891031970179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32072162354741188042626905 24054121766055891031970179)
        ·
          refine ⟨36081182649083836547955269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24054121766055891031970179 36081182649083836547955269)
          ·
            refine ⟨6765221746703219352741613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36081182649083836547955269 6765221746703219352741613)
            ·
              refine ⟨2536958155013707257278105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6765221746703219352741613 2536958155013707257278105)
              ·
                refine ⟨1902718616260280442958579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2536958155013707257278105 1902718616260280442958579)
                ·
                  refine ⟨2854077924390420664437869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1902718616260280442958579 2854077924390420664437869)
                  ·
                    refine ⟨1070279221646407749164201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2854077924390420664437869 1070279221646407749164201)
                    ·
                      rfl

theorem cell22_3126542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_3126542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126542 prefixEnd_3126542 := by exact prefixLift 3126542
  have htrace : WordTrace (prefixWord ++ tailWord_3126542) baseStart_3126542 baseEnd_3126542 := by
    simpa [prefixWord, tailWord_3126542, baseEnd_3126542] using wordTrace_append hprefix tailTrace_3126542
  have hstable : (prefixWord ++ tailWord_3126542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126542).length < 2 ^ (prefixWord ++ tailWord_3126542).sum := by decide
  have hdescent : baseEnd_3126542 < baseStart_3126542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126551 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 3, 4]
def baseStart_3126551 : Nat := 118140960795 + 3126551 * 2 ^ 59
def prefixEnd_3126551 : Nat := 4983230072969 + 3 ^ 40 * 3126551 * 2
def baseEnd_3126551 : Nat := 1070282302530334725689173

theorem tailTrace_3126551 : CollatzResearch.WordTrace tailWord_3126551 prefixEnd_3126551 1070282302530334725689173 := by
  unfold tailWord_3126551
  simp only [CollatzResearch.WordTrace]
  refine ⟨114034683296047174244195507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76023122197364782829463671 114034683296047174244195507)
  ·
    refine ⟨171052024944070761366293261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114034683296047174244195507 171052024944070761366293261)
    ·
      refine ⟨64144509354026535512359973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171052024944070761366293261 64144509354026535512359973)
      ·
        refine ⟨12027095503879975408567495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64144509354026535512359973 12027095503879975408567495)
        ·
          refine ⟨18040643255819963112851243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12027095503879975408567495 18040643255819963112851243)
          ·
            refine ⟨27060964883729944669276865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18040643255819963112851243 27060964883729944669276865)
            ·
              refine ⟨20295723662797458501957649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27060964883729944669276865 20295723662797458501957649)
              ·
                refine ⟨15221792747098093876468237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20295723662797458501957649 15221792747098093876468237)
                ·
                  refine ⟨5708172280161785203675589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15221792747098093876468237 5708172280161785203675589)
                  ·
                    refine ⟨1070282302530334725689173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5708172280161785203675589 1070282302530334725689173)
                    ·
                      rfl

theorem cell22_3126551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_3126551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126551 prefixEnd_3126551 := by exact prefixLift 3126551
  have htrace : WordTrace (prefixWord ++ tailWord_3126551) baseStart_3126551 baseEnd_3126551 := by
    simpa [prefixWord, tailWord_3126551, baseEnd_3126551] using wordTrace_append hprefix tailTrace_3126551
  have hstable : (prefixWord ++ tailWord_3126551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126551).length < 2 ^ (prefixWord ++ tailWord_3126551).sum := by decide
  have hdescent : baseEnd_3126551 < baseStart_3126551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126568 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 3, 4]
def baseStart_3126568 : Nat := 118140960795 + 3126568 * 2 ^ 59
def prefixEnd_3126568 : Nat := 4983230072969 + 3 ^ 40 * 3126568 * 2
def baseEnd_3126568 : Nat := 1070288121977752348014121

theorem tailTrace_3126568 : CollatzResearch.WordTrace tailWord_3126568 prefixEnd_3126568 1070288121977752348014121 := by
  unfold tailWord_3126568
  simp only [CollatzResearch.WordTrace]
  refine ⟨57017651668492793073782179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76023535557990390765042905 57017651668492793073782179)
  ·
    refine ⟨85526477502739189610673269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57017651668492793073782179 85526477502739189610673269)
    ·
      refine ⟨8018107265881799026000619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85526477502739189610673269 8018107265881799026000619)
      ·
        refine ⟨12027160898822698539000929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8018107265881799026000619 12027160898822698539000929)
        ·
          refine ⟨9020370674117023904250697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12027160898822698539000929 9020370674117023904250697)
          ·
            refine ⟨6765278005587767928188023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9020370674117023904250697 6765278005587767928188023)
            ·
              refine ⟨10147917008381651892282035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6765278005587767928188023 10147917008381651892282035)
              ·
                refine ⟨15221875512572477838423053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10147917008381651892282035 15221875512572477838423053)
                ·
                  refine ⟨5708203317214679189408645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15221875512572477838423053 5708203317214679189408645)
                  ·
                    refine ⟨1070288121977752348014121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5708203317214679189408645 1070288121977752348014121)
                    ·
                      rfl

theorem cell22_3126568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_3126568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126568 prefixEnd_3126568 := by exact prefixLift 3126568
  have htrace : WordTrace (prefixWord ++ tailWord_3126568) baseStart_3126568 baseEnd_3126568 := by
    simpa [prefixWord, tailWord_3126568, baseEnd_3126568] using wordTrace_append hprefix tailTrace_3126568
  have hstable : (prefixWord ++ tailWord_3126568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126568).length < 2 ^ (prefixWord ++ tailWord_3126568).sum := by decide
  have hdescent : baseEnd_3126568 < baseStart_3126568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126581 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 3, 5]
def baseStart_3126581 : Nat := 118140960795 + 3126581 * 2 ^ 59
def prefixEnd_3126581 : Nat := 4983230072969 + 3 ^ 40 * 3126581 * 2
def baseEnd_3126581 : Nat := 1070292572143424647439081

theorem tailTrace_3126581 : CollatzResearch.WordTrace tailWord_3126581 prefixEnd_3126581 1070292572143424647439081 := by
  unfold tailWord_3126581
  simp only [CollatzResearch.WordTrace]
  refine ⟨114035777485938489367787597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76023851657292326245191731 114035777485938489367787597)
  ·
    refine ⟨42763416557226933512920349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114035777485938489367787597 42763416557226933512920349)
    ·
      refine ⟨16036281208960100067345131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42763416557226933512920349 16036281208960100067345131)
      ·
        refine ⟨24054421813440150101017697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16036281208960100067345131 24054421813440150101017697)
        ·
          refine ⟨18040816360080112575763273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24054421813440150101017697 18040816360080112575763273)
          ·
            refine ⟨13530612270060084431822455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18040816360080112575763273 13530612270060084431822455)
            ·
              refine ⟨20295918405090126647733683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13530612270060084431822455 20295918405090126647733683)
              ·
                refine ⟨30443877607635189971600525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20295918405090126647733683 30443877607635189971600525)
                ·
                  refine ⟨11416454102863196239350197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30443877607635189971600525 11416454102863196239350197)
                  ·
                    refine ⟨1070292572143424647439081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11416454102863196239350197 1070292572143424647439081)
                    ·
                      rfl

theorem cell22_3126581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_3126581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126581 prefixEnd_3126581 := by exact prefixLift 3126581
  have htrace : WordTrace (prefixWord ++ tailWord_3126581) baseStart_3126581 baseEnd_3126581 := by
    simpa [prefixWord, tailWord_3126581, baseEnd_3126581] using wordTrace_append hprefix tailTrace_3126581
  have hstable : (prefixWord ++ tailWord_3126581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126581).length < 2 ^ (prefixWord ++ tailWord_3126581).sum := by decide
  have hdescent : baseEnd_3126581 < baseStart_3126581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126594 : List Nat := [3, 19]
def baseStart_3126594 : Nat := 118140960795 + 3126594 * 2 ^ 59
def prefixEnd_3126594 : Nat := 4983230072969 + 3 ^ 40 * 3126594 * 2
def baseEnd_3126594 : Nat := 163130166485154236681

theorem tailTrace_3126594 : CollatzResearch.WordTrace tailWord_3126594 prefixEnd_3126594 163130166485154236681 := by
  unfold tailWord_3126594
  simp only [CollatzResearch.WordTrace]
  refine ⟨28509062908722848147002709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76024167756594261725340557 28509062908722848147002709)
  ·
    refine ⟨163130166485154236681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 19 28509062908722848147002709 163130166485154236681)
    ·
      rfl

theorem cell22_3126594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 19].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 19].length) (baseStart_3126594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126594 prefixEnd_3126594 := by exact prefixLift 3126594
  have htrace : WordTrace (prefixWord ++ tailWord_3126594) baseStart_3126594 baseEnd_3126594 := by
    simpa [prefixWord, tailWord_3126594, baseEnd_3126594] using wordTrace_append hprefix tailTrace_3126594
  have hstable : (prefixWord ++ tailWord_3126594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126594).length < 2 ^ (prefixWord ++ tailWord_3126594).sum := by decide
  have hdescent : baseEnd_3126594 < baseStart_3126594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126628 : List Nat := [2, 3, 1, 1, 3, 3, 3, 6]
def baseStart_3126628 : Nat := 118140960795 + 3126628 * 2 ^ 59
def prefixEnd_3126628 : Nat := 4983230072969 + 3 ^ 40 * 3126628 * 2
def baseEnd_3126628 : Nat := 118923184578214687945993

theorem tailTrace_3126628 : CollatzResearch.WordTrace tailWord_3126628 prefixEnd_3126628 118923184578214687945993 := by
  unfold tailWord_3126628
  simp only [CollatzResearch.WordTrace]
  refine ⟨57018745858384108197374269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76024994477845477596499025 57018745858384108197374269)
  ·
    refine ⟨21382029696894040574015351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57018745858384108197374269 21382029696894040574015351)
    ·
      refine ⟨32073044545341060861023027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21382029696894040574015351 32073044545341060861023027)
      ·
        refine ⟨48109566818011591291534541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32073044545341060861023027 48109566818011591291534541)
        ·
          refine ⟨18041087556754346734325453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48109566818011591291534541 18041087556754346734325453)
          ·
            refine ⟨6765407833782880025372045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18041087556754346734325453 6765407833782880025372045)
            ·
              refine ⟨2537027937668580009514517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6765407833782880025372045 2537027937668580009514517)
              ·
                refine ⟨118923184578214687945993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2537027937668580009514517 118923184578214687945993)
                ·
                  rfl

theorem cell22_3126628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 6].length) (baseStart_3126628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126628 prefixEnd_3126628 := by exact prefixLift 3126628
  have htrace : WordTrace (prefixWord ++ tailWord_3126628) baseStart_3126628 baseEnd_3126628 := by
    simpa [prefixWord, tailWord_3126628, baseEnd_3126628] using wordTrace_append hprefix tailTrace_3126628
  have hstable : (prefixWord ++ tailWord_3126628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126628).length < 2 ^ (prefixWord ++ tailWord_3126628).sum := by decide
  have hdescent : baseEnd_3126628 < baseStart_3126628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126660 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 3, 3]
def baseStart_3126660 : Nat := 118140960795 + 3126660 * 2 ^ 59
def prefixEnd_3126660 : Nat := 4983230072969 + 3 ^ 40 * 3126660 * 2
def baseEnd_3126660 : Nat := 1070319615457894774713839

theorem tailTrace_3126660 : CollatzResearch.WordTrace tailWord_3126660 prefixEnd_3126660 1070319615457894774713839 := by
  unfold tailWord_3126660
  simp only [CollatzResearch.WordTrace]
  refine ⟨57019329426326142929956717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76025772568434857239942289 57019329426326142929956717)
  ·
    refine ⟨21382248534872303598733769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57019329426326142929956717 21382248534872303598733769)
    ·
      refine ⟨16036686401154227699050327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21382248534872303598733769 16036686401154227699050327)
      ·
        refine ⟨24055029601731341548575491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16036686401154227699050327 24055029601731341548575491)
        ·
          refine ⟨36082544402597012322863237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24055029601731341548575491 36082544402597012322863237)
          ·
            refine ⟨6765477075486939810536857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36082544402597012322863237 6765477075486939810536857)
            ·
              refine ⟨5074107806615204857902643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6765477075486939810536857 5074107806615204857902643)
              ·
                refine ⟨7611161709922807286853965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5074107806615204857902643 7611161709922807286853965)
                ·
                  refine ⟨2854185641221052732570237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7611161709922807286853965 2854185641221052732570237)
                  ·
                    refine ⟨1070319615457894774713839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2854185641221052732570237 1070319615457894774713839)
                    ·
                      rfl

theorem cell22_3126660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_3126660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126660 prefixEnd_3126660 := by exact prefixLift 3126660
  have htrace : WordTrace (prefixWord ++ tailWord_3126660) baseStart_3126660 baseEnd_3126660 := by
    simpa [prefixWord, tailWord_3126660, baseEnd_3126660] using wordTrace_append hprefix tailTrace_3126660
  have hstable : (prefixWord ++ tailWord_3126660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126660).length < 2 ^ (prefixWord ++ tailWord_3126660).sum := by decide
  have hdescent : baseEnd_3126660 < baseStart_3126660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126731 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 3, 6]
def baseStart_3126731 : Nat := 118140960795 + 3126731 * 2 ^ 59
def prefixEnd_3126731 : Nat := 4983230072969 + 3 ^ 40 * 3126731 * 2
def baseEnd_3126731 : Nat := 1070343920208874256188621

theorem tailTrace_3126731 : CollatzResearch.WordTrace tailWord_3126731 prefixEnd_3126731 1070343920208874256188621 := by
  unfold tailWord_3126731
  simp only [CollatzResearch.WordTrace]
  refine ⟨114041248435395064985748047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76027498956930043323832031 114041248435395064985748047)
  ·
    refine ⟨171061872653092597478622071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114041248435395064985748047 171061872653092597478622071)
    ·
      refine ⟨256592808979638896217933107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171061872653092597478622071 256592808979638896217933107)
      ·
        refine ⟨384889213469458344326899661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256592808979638896217933107 384889213469458344326899661)
        ·
          refine ⟨144333455051046879122587373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384889213469458344326899661 144333455051046879122587373)
          ·
            refine ⟨54125045644142579670970265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144333455051046879122587373 54125045644142579670970265)
            ·
              refine ⟨40593784233106934753227699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54125045644142579670970265 40593784233106934753227699)
              ·
                refine ⟨60890676349660402129841549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40593784233106934753227699 60890676349660402129841549)
                ·
                  refine ⟨22834003631122650798690581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60890676349660402129841549 22834003631122650798690581)
                  ·
                    refine ⟨1070343920208874256188621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22834003631122650798690581 1070343920208874256188621)
                    ·
                      rfl

theorem cell22_3126731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 6].length) (baseStart_3126731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126731 prefixEnd_3126731 := by exact prefixLift 3126731
  have htrace : WordTrace (prefixWord ++ tailWord_3126731) baseStart_3126731 baseEnd_3126731 := by
    simpa [prefixWord, tailWord_3126731, baseEnd_3126731] using wordTrace_append hprefix tailTrace_3126731
  have hstable : (prefixWord ++ tailWord_3126731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126731).length < 2 ^ (prefixWord ++ tailWord_3126731).sum := by decide
  have hdescent : baseEnd_3126731 < baseStart_3126731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126761 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 4, 7]
def baseStart_3126761 : Nat := 118140960795 + 3126761 * 2 ^ 59
def prefixEnd_3126761 : Nat := 4983230072969 + 3 ^ 40 * 3126761 * 2
def baseEnd_3126761 : Nat := 1070354189821964177938529

theorem tailTrace_3126761 : CollatzResearch.WordTrace tailWord_3126761 prefixEnd_3126761 1070354189821964177938529 := by
  unfold tailWord_3126761
  simp only [CollatzResearch.WordTrace]
  refine ⟨114042342625286380109340137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76028228416857586739560091 114042342625286380109340137)
  ·
    refine ⟨85531756968964785082005103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114042342625286380109340137 85531756968964785082005103)
    ·
      refine ⟨128297635453447177623007655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85531756968964785082005103 128297635453447177623007655)
      ·
        refine ⟨192446453180170766434511483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128297635453447177623007655 192446453180170766434511483)
        ·
          refine ⟨288669679770256149651767225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192446453180170766434511483 288669679770256149651767225)
          ·
            refine ⟨216502259827692112238825419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288669679770256149651767225 216502259827692112238825419)
            ·
              refine ⟨324753389741538168358238129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216502259827692112238825419 324753389741538168358238129)
              ·
                refine ⟨243565042306153626268678597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324753389741538168358238129 243565042306153626268678597)
                ·
                  refine ⟨45668445432403804925377237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243565042306153626268678597 45668445432403804925377237)
                  ·
                    refine ⟨1070354189821964177938529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45668445432403804925377237 1070354189821964177938529)
                    ·
                      rfl

theorem cell22_3126761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_3126761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126761 prefixEnd_3126761 := by exact prefixLift 3126761
  have htrace : WordTrace (prefixWord ++ tailWord_3126761) baseStart_3126761 baseEnd_3126761 := by
    simpa [prefixWord, tailWord_3126761, baseEnd_3126761] using wordTrace_append hprefix tailTrace_3126761
  have hstable : (prefixWord ++ tailWord_3126761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126761).length < 2 ^ (prefixWord ++ tailWord_3126761).sum := by decide
  have hdescent : baseEnd_3126761 < baseStart_3126761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126814 : List Nat := [4, 3, 3, 1, 1, 1, 9]
def baseStart_3126814 : Nat := 118140960795 + 3126814 * 2 ^ 59
def prefixEnd_3126814 : Nat := 4983230072969 + 3 ^ 40 * 3126814 * 2
def baseEnd_3126814 : Nat := 39643419733521840976421

theorem tailTrace_3126814 : CollatzResearch.WordTrace tailWord_3126814 prefixEnd_3126814 39643419733521840976421 := by
  unfold tailWord_3126814
  simp only [CollatzResearch.WordTrace]
  refine ⟨14255534461761796270127437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76029517129396246774012997 14255534461761796270127437)
  ·
    refine ⟨5345825423160673601297789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14255534461761796270127437 5345825423160673601297789)
    ·
      refine ⟨2004684533685252600486671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5345825423160673601297789 2004684533685252600486671)
      ·
        refine ⟨3007026800527878900730007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2004684533685252600486671 3007026800527878900730007)
        ·
          refine ⟨4510540200791818351095011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3007026800527878900730007 4510540200791818351095011)
          ·
            refine ⟨6765810301187727526642517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4510540200791818351095011 6765810301187727526642517)
            ·
              refine ⟨39643419733521840976421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6765810301187727526642517 39643419733521840976421)
              ·
                rfl

theorem cell22_3126814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 9].length) (baseStart_3126814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126814 prefixEnd_3126814 := by exact prefixLift 3126814
  have htrace : WordTrace (prefixWord ++ tailWord_3126814) baseStart_3126814 baseEnd_3126814 := by
    simpa [prefixWord, tailWord_3126814, baseEnd_3126814] using wordTrace_append hprefix tailTrace_3126814
  have hstable : (prefixWord ++ tailWord_3126814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126814).length < 2 ^ (prefixWord ++ tailWord_3126814).sum := by decide
  have hdescent : baseEnd_3126814 < baseStart_3126814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126853 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 6]
def baseStart_3126853 : Nat := 118140960795 + 3126853 * 2 ^ 59
def prefixEnd_3126853 : Nat := 4983230072969 + 3 ^ 40 * 3126853 * 2
def baseEnd_3126853 : Nat := 356795227767368868212749

theorem tailTrace_3126853 : CollatzResearch.WordTrace tailWord_3126853 prefixEnd_3126853 356795227767368868212749 := by
  unfold tailWord_3126853
  simp only [CollatzResearch.WordTrace]
  refine ⟨114045698140953079821689213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76030465427302053214459475 114045698140953079821689213)
  ·
    refine ⟨42767136802857404933133455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114045698140953079821689213 42767136802857404933133455)
    ·
      refine ⟨64150705204286107399700183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42767136802857404933133455 64150705204286107399700183)
      ·
        refine ⟨96226057806429161099550275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64150705204286107399700183 96226057806429161099550275)
        ·
          refine ⟨144339086709643741649325413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96226057806429161099550275 144339086709643741649325413)
          ·
            refine ⟨27063578758058201559248515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144339086709643741649325413 27063578758058201559248515)
            ·
              refine ⟨40595368137087302338872773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27063578758058201559248515 40595368137087302338872773)
              ·
                refine ⟨7611631525703869188538645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40595368137087302338872773 7611631525703869188538645)
                ·
                  refine ⟨356795227767368868212749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7611631525703869188538645 356795227767368868212749)
                  ·
                    rfl

theorem cell22_3126853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_3126853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126853 prefixEnd_3126853 := by exact prefixLift 3126853
  have htrace : WordTrace (prefixWord ++ tailWord_3126853) baseStart_3126853 baseEnd_3126853 := by
    simpa [prefixWord, tailWord_3126853, baseEnd_3126853] using wordTrace_append hprefix tailTrace_3126853
  have hstable : (prefixWord ++ tailWord_3126853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126853).length < 2 ^ (prefixWord ++ tailWord_3126853).sum := by decide
  have hdescent : baseEnd_3126853 < baseStart_3126853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126928 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 4, 6]
def baseStart_3126928 : Nat := 118140960795 + 3126928 * 2 ^ 59
def prefixEnd_3126928 : Nat := 4983230072969 + 3 ^ 40 * 3126928 * 2
def baseEnd_3126928 : Nat := 1070411357334831409013017

theorem tailTrace_3126928 : CollatzResearch.WordTrace tailWord_3126928 prefixEnd_3126928 1070411357334831409013017 := by
  unfold tailWord_3126928
  simp only [CollatzResearch.WordTrace]
  refine ⟨57024216807840683815334719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76032289077120911753779625 57024216807840683815334719)
  ·
    refine ⟨85536325211761025723002079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57024216807840683815334719 85536325211761025723002079)
    ·
      refine ⟨128304487817641538584503119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85536325211761025723002079 128304487817641538584503119)
      ·
        refine ⟨192456731726462307876754679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128304487817641538584503119 192456731726462307876754679)
        ·
          refine ⟨288685097589693461815132019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192456731726462307876754679 288685097589693461815132019)
          ·
            refine ⟨433027646384540192722698029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288685097589693461815132019 433027646384540192722698029)
            ·
              refine ⟨162385367394202572271011761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 433027646384540192722698029 162385367394202572271011761)
              ·
                refine ⟨121789025545651929203258821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162385367394202572271011761 121789025545651929203258821)
                ·
                  refine ⟨22835442289809736725611029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121789025545651929203258821 22835442289809736725611029)
                  ·
                    refine ⟨1070411357334831409013017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22835442289809736725611029 1070411357334831409013017)
                    ·
                      rfl

theorem cell22_3126928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_3126928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126928 prefixEnd_3126928 := by exact prefixLift 3126928
  have htrace : WordTrace (prefixWord ++ tailWord_3126928) baseStart_3126928 baseEnd_3126928 := by
    simpa [prefixWord, tailWord_3126928, baseEnd_3126928] using wordTrace_append hprefix tailTrace_3126928
  have hstable : (prefixWord ++ tailWord_3126928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126928).length < 2 ^ (prefixWord ++ tailWord_3126928).sum := by decide
  have hdescent : baseEnd_3126928 < baseStart_3126928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126932 : List Nat := [2, 4, 2, 2, 3, 9]
def baseStart_3126932 : Nat := 118140960795 + 3126932 * 2 ^ 59
def prefixEnd_3126932 : Nat := 4983230072969 + 3 ^ 40 * 3126932 * 2
def baseEnd_3126932 : Nat := 13214971933537984344605

theorem tailTrace_3126932 : CollatzResearch.WordTrace tailWord_3126932 prefixEnd_3126932 13214971933537984344605 := by
  unfold tailWord_3126932
  simp only [CollatzResearch.WordTrace]
  refine ⟨57024289753833438156907525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76032386338444584209210033 57024289753833438156907525)
  ·
    refine ⟨10692054328843769654420161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57024289753833438156907525 10692054328843769654420161)
    ·
      refine ⟨8019040746632827240815121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10692054328843769654420161 8019040746632827240815121)
      ·
        refine ⟨6014280559974620430611341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8019040746632827240815121 6014280559974620430611341)
        ·
          refine ⟨2255355209990482661479253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6014280559974620430611341 2255355209990482661479253)
          ·
            refine ⟨13214971933537984344605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2255355209990482661479253 13214971933537984344605)
            ·
              rfl

theorem cell22_3126932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 9].length) (baseStart_3126932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126932 prefixEnd_3126932 := by exact prefixLift 3126932
  have htrace : WordTrace (prefixWord ++ tailWord_3126932) baseStart_3126932 baseEnd_3126932 := by
    simpa [prefixWord, tailWord_3126932, baseEnd_3126932] using wordTrace_append hprefix tailTrace_3126932
  have hstable : (prefixWord ++ tailWord_3126932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126932).length < 2 ^ (prefixWord ++ tailWord_3126932).sum := by decide
  have hdescent : baseEnd_3126932 < baseStart_3126932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126945 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 2, 6]
def baseStart_3126945 : Nat := 118140960795 + 3126945 * 2 ^ 59
def prefixEnd_3126945 : Nat := 4983230072969 + 3 ^ 40 * 3126945 * 2
def baseEnd_3126945 : Nat := 1070417176782249031337965

theorem tailTrace_3126945 : CollatzResearch.WordTrace tailWord_3126945 prefixEnd_3126945 1070417176782249031337965 := by
  unfold tailWord_3126945
  simp only [CollatzResearch.WordTrace]
  refine ⟨114049053656619779534038289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76032702437746519689358859 114049053656619779534038289)
  ·
    refine ⟨85536790242464834650528717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114049053656619779534038289 85536790242464834650528717)
    ·
      refine ⟨32076296340924312993948269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85536790242464834650528717 32076296340924312993948269)
      ·
        refine ⟨12028611127846617372730601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32076296340924312993948269 12028611127846617372730601)
        ·
          refine ⟨9021458345884963029547951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12028611127846617372730601 9021458345884963029547951)
          ·
            refine ⟨13532187518827444544321927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9021458345884963029547951 13532187518827444544321927)
            ·
              refine ⟨20298281278241166816482891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13532187518827444544321927 20298281278241166816482891)
              ·
                refine ⟨30447421917361750224724337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20298281278241166816482891 30447421917361750224724337)
                ·
                  refine ⟨22835566438021312668543253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30447421917361750224724337 22835566438021312668543253)
                  ·
                    refine ⟨1070417176782249031337965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22835566438021312668543253 1070417176782249031337965)
                    ·
                      rfl

theorem cell22_3126945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_3126945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126945 prefixEnd_3126945 := by exact prefixLift 3126945
  have htrace : WordTrace (prefixWord ++ tailWord_3126945) baseStart_3126945 baseEnd_3126945 := by
    simpa [prefixWord, tailWord_3126945, baseEnd_3126945] using wordTrace_append hprefix tailTrace_3126945
  have hstable : (prefixWord ++ tailWord_3126945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126945).length < 2 ^ (prefixWord ++ tailWord_3126945).sum := by decide
  have hdescent : baseEnd_3126945 < baseStart_3126945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126960 : List Nat := [2, 1, 1, 1, 2, 1, 6, 3, 5]
def baseStart_3126960 : Nat := 118140960795 + 3126960 * 2 ^ 59
def prefixEnd_3126960 : Nat := 4983230072969 + 3 ^ 40 * 3126960 * 2
def baseEnd_3126960 : Nat := 356807437196264664070973

theorem tailTrace_3126960 : CollatzResearch.WordTrace tailWord_3126960 prefixEnd_3126960 356807437196264664070973 := by
  unfold tailWord_3126960
  simp only [CollatzResearch.WordTrace]
  refine ⟨57024800375782718547917167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76033067167710291397222889 57024800375782718547917167)
  ·
    refine ⟨85537200563674077821875751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57024800375782718547917167 85537200563674077821875751)
    ·
      refine ⟨128305800845511116732813627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85537200563674077821875751 128305800845511116732813627)
      ·
        refine ⟨192458701268266675099220441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128305800845511116732813627 192458701268266675099220441)
        ·
          refine ⟨144344025951200006324415331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192458701268266675099220441 144344025951200006324415331)
          ·
            refine ⟨216516038926800009486622997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144344025951200006324415331 216516038926800009486622997)
            ·
              refine ⟨10149189324693750444685453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 216516038926800009486622997 10149189324693750444685453)
              ·
                refine ⟨3805945996760156416757045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10149189324693750444685453 3805945996760156416757045)
                ·
                  refine ⟨356807437196264664070973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3805945996760156416757045 356807437196264664070973)
                  ·
                    rfl

theorem cell22_3126960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 5].length) (baseStart_3126960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126960 prefixEnd_3126960 := by exact prefixLift 3126960
  have htrace : WordTrace (prefixWord ++ tailWord_3126960) baseStart_3126960 baseEnd_3126960 := by
    simpa [prefixWord, tailWord_3126960, baseEnd_3126960] using wordTrace_append hprefix tailTrace_3126960
  have hstable : (prefixWord ++ tailWord_3126960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126960).length < 2 ^ (prefixWord ++ tailWord_3126960).sum := by decide
  have hdescent : baseEnd_3126960 < baseStart_3126960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126994 : List Nat := [3, 2, 2, 2, 2, 3, 1, 2, 5]
def baseStart_3126994 : Nat := 118140960795 + 3126994 * 2 ^ 59
def prefixEnd_3126994 : Nat := 4983230072969 + 3 ^ 40 * 3126994 * 2
def baseEnd_3126994 : Nat := 356811316827876412287605

theorem tailTrace_3126994 : CollatzResearch.WordTrace tailWord_3126994 prefixEnd_3126994 356811316827876412287605 := by
  unfold tailWord_3126994
  simp only [CollatzResearch.WordTrace]
  refine ⟨28512710208360565225643009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76033893888961507268381357 28512710208360565225643009)
  ·
    refine ⟨21384532656270423919232257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28512710208360565225643009 21384532656270423919232257)
    ·
      refine ⟨16038399492202817939424193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21384532656270423919232257 16038399492202817939424193)
      ·
        refine ⟨12028799619152113454568145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16038399492202817939424193 12028799619152113454568145)
        ·
          refine ⟨9021599714364085090926109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12028799619152113454568145 9021599714364085090926109)
          ·
            refine ⟨3383099892886531909097291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9021599714364085090926109 3383099892886531909097291)
            ·
              refine ⟨5074649839329797863645937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3383099892886531909097291 5074649839329797863645937)
              ·
                refine ⟨3805987379497348397734453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5074649839329797863645937 3805987379497348397734453)
                ·
                  refine ⟨356811316827876412287605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3805987379497348397734453 356811316827876412287605)
                  ·
                    rfl

theorem cell22_3126994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_3126994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126994 prefixEnd_3126994 := by exact prefixLift 3126994
  have htrace : WordTrace (prefixWord ++ tailWord_3126994) baseStart_3126994 baseEnd_3126994 := by
    simpa [prefixWord, tailWord_3126994, baseEnd_3126994] using wordTrace_append hprefix tailTrace_3126994
  have hstable : (prefixWord ++ tailWord_3126994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126994).length < 2 ^ (prefixWord ++ tailWord_3126994).sum := by decide
  have hdescent : baseEnd_3126994 < baseStart_3126994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126998 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_3126998 : Nat := 118140960795 + 3126998 * 2 ^ 59
def prefixEnd_3126998 : Nat := 4983230072969 + 3 ^ 40 * 3126998 * 2
def baseEnd_3126998 : Nat := 1070435319765374559762803

theorem tailTrace_3126998 : CollatzResearch.WordTrace tailWord_3126998 prefixEnd_3126998 1070435319765374559762803 := by
  unfold tailWord_3126998
  simp only [CollatzResearch.WordTrace]
  refine ⟨7128186670339235599107353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76033991150285179723811765 7128186670339235599107353)
  ·
    refine ⟨5346140002754426699330515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7128186670339235599107353 5346140002754426699330515)
    ·
      refine ⟨8019210004131640048995773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5346140002754426699330515 8019210004131640048995773)
      ·
        refine ⟨3007203751549365018373415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8019210004131640048995773 3007203751549365018373415)
        ·
          refine ⟨4510805627324047527560123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3007203751549365018373415 4510805627324047527560123)
          ·
            refine ⟨6766208440986071291340185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4510805627324047527560123 6766208440986071291340185)
            ·
              refine ⟨5074656330739553468505139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6766208440986071291340185 5074656330739553468505139)
              ·
                refine ⟨7611984496109330202757709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5074656330739553468505139 7611984496109330202757709)
                ·
                  refine ⟨2854494186040998826034141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7611984496109330202757709 2854494186040998826034141)
                  ·
                    refine ⟨1070435319765374559762803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2854494186040998826034141 1070435319765374559762803)
                    ·
                      rfl

theorem cell22_3126998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_3126998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3126998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3126998 prefixEnd_3126998 := by exact prefixLift 3126998
  have htrace : WordTrace (prefixWord ++ tailWord_3126998) baseStart_3126998 baseEnd_3126998 := by
    simpa [prefixWord, tailWord_3126998, baseEnd_3126998] using wordTrace_append hprefix tailTrace_3126998
  have hstable : (prefixWord ++ tailWord_3126998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126998).length < 2 ^ (prefixWord ++ tailWord_3126998).sum := by decide
  have hdescent : baseEnd_3126998 < baseStart_3126998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127050 : List Nat := [3, 1, 2, 2, 1, 3, 10]
def baseStart_3127050 : Nat := 118140960795 + 3127050 * 2 ^ 59
def prefixEnd_3127050 : Nat := 4983230072969 + 3 ^ 40 * 3127050 * 2
def baseEnd_3127050 : Nat := 39646411867706065091209

theorem tailTrace_3127050 : CollatzResearch.WordTrace tailWord_3127050 prefixEnd_3127050 39646411867706065091209 := by
  unfold tailWord_3127050
  simp only [CollatzResearch.WordTrace]
  refine ⟨28513220830309845616652651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76035255547492921644407069 28513220830309845616652651)
  ·
    refine ⟨42769831245464768424978977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28513220830309845616652651 42769831245464768424978977)
    ·
      refine ⟨32077373434098576318734233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42769831245464768424978977 32077373434098576318734233)
      ·
        refine ⟨24058030075573932239050675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32077373434098576318734233 24058030075573932239050675)
        ·
          refine ⟨36087045113360898358576013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24058030075573932239050675 36087045113360898358576013)
          ·
            refine ⟨13532641917510336884466005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36087045113360898358576013 13532641917510336884466005)
            ·
              refine ⟨39646411867706065091209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13532641917510336884466005 39646411867706065091209)
              ·
                rfl

theorem cell22_3127050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 10].length) (baseStart_3127050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127050 prefixEnd_3127050 := by exact prefixLift 3127050
  have htrace : WordTrace (prefixWord ++ tailWord_3127050) baseStart_3127050 baseEnd_3127050 := by
    simpa [prefixWord, tailWord_3127050, baseEnd_3127050] using wordTrace_append hprefix tailTrace_3127050
  have hstable : (prefixWord ++ tailWord_3127050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127050).length < 2 ^ (prefixWord ++ tailWord_3127050).sum := by decide
  have hdescent : baseEnd_3127050 < baseStart_3127050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127086 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_3127086 : Nat := 118140960795 + 3127086 * 2 ^ 59
def prefixEnd_3127086 : Nat := 4983230072969 + 3 ^ 40 * 3127086 * 2
def baseEnd_3127086 : Nat := 1070465443963771663562533

theorem tailTrace_3127086 : CollatzResearch.WordTrace tailWord_3127086 prefixEnd_3127086 1070465443963771663562533 := by
  unfold tailWord_3127086
  simp only [CollatzResearch.WordTrace]
  refine ⟨14256774543638620076865139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76036130899405973743280741 14256774543638620076865139)
  ·
    refine ⟨21385161815457930115297709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14256774543638620076865139 21385161815457930115297709)
    ·
      refine ⟨8019435680796723793236641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21385161815457930115297709 8019435680796723793236641)
      ·
        refine ⟨6014576760597542844927481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8019435680796723793236641 6014576760597542844927481)
        ·
          refine ⟨4510932570448157133695611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6014576760597542844927481 4510932570448157133695611)
          ·
            refine ⟨6766398855672235700543417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4510932570448157133695611 6766398855672235700543417)
            ·
              refine ⟨5074799141754176775407563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6766398855672235700543417 5074799141754176775407563)
              ·
                refine ⟨7612198712631265163111345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5074799141754176775407563 7612198712631265163111345)
                ·
                  refine ⟨5709149034473448872333509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7612198712631265163111345 5709149034473448872333509)
                  ·
                    refine ⟨1070465443963771663562533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5709149034473448872333509 1070465443963771663562533)
                    ·
                      rfl

theorem cell22_3127086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_3127086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127086 prefixEnd_3127086 := by exact prefixLift 3127086
  have htrace : WordTrace (prefixWord ++ tailWord_3127086) baseStart_3127086 baseEnd_3127086 := by
    simpa [prefixWord, tailWord_3127086, baseEnd_3127086] using wordTrace_append hprefix tailTrace_3127086
  have hstable : (prefixWord ++ tailWord_3127086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127086).length < 2 ^ (prefixWord ++ tailWord_3127086).sum := by decide
  have hdescent : baseEnd_3127086 < baseStart_3127086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127095 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 7]
def baseStart_3127095 : Nat := 118140960795 + 3127095 * 2 ^ 59
def prefixEnd_3127095 : Nat := 4983230072969 + 3 ^ 40 * 3127095 * 2
def baseEnd_3127095 : Nat := 356822841615899546695835

theorem tailTrace_3127095 : CollatzResearch.WordTrace tailWord_3127095 prefixEnd_3127095 356822841615899546695835 := by
  unfold tailWord_3127095
  simp only [CollatzResearch.WordTrace]
  refine ⟨114054524606076355151998739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76036349737384236767999159 114054524606076355151998739)
  ·
    refine ⟨171081786909114532727998109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114054524606076355151998739 171081786909114532727998109)
    ·
      refine ⟨64155670090917949772999291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171081786909114532727998109 64155670090917949772999291)
      ·
        refine ⟨96233505136376924659498937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64155670090917949772999291 96233505136376924659498937)
        ·
          refine ⟨72175128852282693494624203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96233505136376924659498937 72175128852282693494624203)
          ·
            refine ⟨108262693278424040241936305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72175128852282693494624203 108262693278424040241936305)
            ·
              refine ⟨81197019958818030181452229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108262693278424040241936305 81197019958818030181452229)
              ·
                refine ⟨15224441242278380659022293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81197019958818030181452229 15224441242278380659022293)
                ·
                  refine ⟨356822841615899546695835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15224441242278380659022293 356822841615899546695835)
                  ·
                    rfl

theorem cell22_3127095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 7].length) (baseStart_3127095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127095 prefixEnd_3127095 := by exact prefixLift 3127095
  have htrace : WordTrace (prefixWord ++ tailWord_3127095) baseStart_3127095 baseEnd_3127095 := by
    simpa [prefixWord, tailWord_3127095, baseEnd_3127095] using wordTrace_append hprefix tailTrace_3127095
  have hstable : (prefixWord ++ tailWord_3127095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127095).length < 2 ^ (prefixWord ++ tailWord_3127095).sum := by decide
  have hdescent : baseEnd_3127095 < baseStart_3127095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127112 : List Nat := [2, 1, 3, 1, 1, 4, 1, 4, 5]
def baseStart_3127112 : Nat := 118140960795 + 3127112 * 2 ^ 59
def prefixEnd_3127112 : Nat := 4983230072969 + 3 ^ 40 * 3127112 * 2
def baseEnd_3127112 : Nat := 356824781431705420804151

theorem tailTrace_3127112 : CollatzResearch.WordTrace tailWord_3127112 prefixEnd_3127112 356824781431705420804151 := by
  unfold tailWord_3127112
  simp only [CollatzResearch.WordTrace]
  refine ⟨57027572323507383527683795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76036763098009844703578393 57027572323507383527683795)
  ·
    refine ⟨85541358485261075291525693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57027572323507383527683795 85541358485261075291525693)
    ·
      refine ⟨32078009431972903234322135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85541358485261075291525693 32078009431972903234322135)
      ·
        refine ⟨48117014147959354851483203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32078009431972903234322135 48117014147959354851483203)
        ·
          refine ⟨72175521221939032277224805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48117014147959354851483203 72175521221939032277224805)
          ·
            refine ⟨13532910229113568551979651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72175521221939032277224805 13532910229113568551979651)
            ·
              refine ⟨20299365343670352827969477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13532910229113568551979651 20299365343670352827969477)
              ·
                refine ⟨3806131001938191155244277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20299365343670352827969477 3806131001938191155244277)
                ·
                  refine ⟨356824781431705420804151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3806131001938191155244277 356824781431705420804151)
                  ·
                    rfl

theorem cell22_3127112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 5].length) (baseStart_3127112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127112 prefixEnd_3127112 := by exact prefixLift 3127112
  have htrace : WordTrace (prefixWord ++ tailWord_3127112) baseStart_3127112 baseEnd_3127112 := by
    simpa [prefixWord, tailWord_3127112, baseEnd_3127112] using wordTrace_append hprefix tailTrace_3127112
  have hstable : (prefixWord ++ tailWord_3127112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127112).length < 2 ^ (prefixWord ++ tailWord_3127112).sum := by decide
  have hdescent : baseEnd_3127112 < baseStart_3127112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127157 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 8]
def baseStart_3127157 : Nat := 118140960795 + 3127157 * 2 ^ 59
def prefixEnd_3127157 : Nat := 4983230072969 + 3 ^ 40 * 3127157 * 2
def baseEnd_3127157 : Nat := 356829916238250381679105

theorem tailTrace_3127157 : CollatzResearch.WordTrace tailWord_3127157 prefixEnd_3127157 356829916238250381679105 := by
  unfold tailWord_3127157
  simp only [CollatzResearch.WordTrace]
  refine ⟨114056785931851739740755725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76037857287901159827170483 114056785931851739740755725)
  ·
    refine ⟨42771294724444402402783397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114056785931851739740755725 42771294724444402402783397)
    ·
      refine ⟨8019617760833325450521887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42771294724444402402783397 8019617760833325450521887)
      ·
        refine ⟨12029426641249988175782831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8019617760833325450521887 12029426641249988175782831)
        ·
          refine ⟨18044139961874982263674247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12029426641249988175782831 18044139961874982263674247)
          ·
            refine ⟨27066209942812473395511371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18044139961874982263674247 27066209942812473395511371)
            ·
              refine ⟨40599314914218710093267057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27066209942812473395511371 40599314914218710093267057)
              ·
                refine ⟨30449486185664032569950293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40599314914218710093267057 30449486185664032569950293)
                ·
                  refine ⟨356829916238250381679105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30449486185664032569950293 356829916238250381679105)
                  ·
                    rfl

theorem cell22_3127157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_3127157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127157 prefixEnd_3127157 := by exact prefixLift 3127157
  have htrace : WordTrace (prefixWord ++ tailWord_3127157) baseStart_3127157 baseEnd_3127157 := by
    simpa [prefixWord, tailWord_3127157, baseEnd_3127157] using wordTrace_append hprefix tailTrace_3127157
  have hstable : (prefixWord ++ tailWord_3127157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127157).length < 2 ^ (prefixWord ++ tailWord_3127157).sum := by decide
  have hdescent : baseEnd_3127157 < baseStart_3127157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127172 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_3127172 : Nat := 118140960795 + 3127172 * 2 ^ 59
def prefixEnd_3127172 : Nat := 4983230072969 + 3 ^ 40 * 3127172 * 2
def baseEnd_3127172 : Nat := 1070494883521296105912269

theorem tailTrace_3127172 : CollatzResearch.WordTrace tailWord_3127172 prefixEnd_3127172 1070494883521296105912269 := by
  unfold tailWord_3127172
  simp only [CollatzResearch.WordTrace]
  refine ⟨57028666513398698651275885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76038222017864931535034513 57028666513398698651275885)
  ·
    refine ⟨21385749942524511994228457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57028666513398698651275885 21385749942524511994228457)
    ·
      refine ⟨16039312456893383995671343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21385749942524511994228457 16039312456893383995671343)
      ·
        refine ⟨24058968685340075993507015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16039312456893383995671343 24058968685340075993507015)
        ·
          refine ⟨36088453028010113990260523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24058968685340075993507015 36088453028010113990260523)
          ·
            refine ⟨54132679542015170985390785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36088453028010113990260523 54132679542015170985390785)
            ·
              refine ⟨40599509656511378239043089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54132679542015170985390785 40599509656511378239043089)
              ·
                refine ⟨30449632242383533679282317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40599509656511378239043089 30449632242383533679282317)
                ·
                  refine ⟨11418612090893825129730869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30449632242383533679282317 11418612090893825129730869)
                  ·
                    refine ⟨1070494883521296105912269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11418612090893825129730869 1070494883521296105912269)
                    ·
                      rfl

theorem cell22_3127172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_3127172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127172 prefixEnd_3127172 := by exact prefixLift 3127172
  have htrace : WordTrace (prefixWord ++ tailWord_3127172) baseStart_3127172 baseEnd_3127172 := by
    simpa [prefixWord, tailWord_3127172, baseEnd_3127172] using wordTrace_append hprefix tailTrace_3127172
  have hstable : (prefixWord ++ tailWord_3127172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127172).length < 2 ^ (prefixWord ++ tailWord_3127172).sum := by decide
  have hdescent : baseEnd_3127172 < baseStart_3127172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127232 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 2, 6]
def baseStart_3127232 : Nat := 118140960795 + 3127232 * 2 ^ 59
def prefixEnd_3127232 : Nat := 4983230072969 + 3 ^ 40 * 3127232 * 2
def baseEnd_3127232 : Nat := 1070515422747475949412085

theorem tailTrace_3127232 : CollatzResearch.WordTrace tailWord_3127232 prefixEnd_3127232 1070515422747475949412085 := by
  unfold tailWord_3127232
  simp only [CollatzResearch.WordTrace]
  refine ⟨57029760703290013774867975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76039680937720018366490633 57029760703290013774867975)
  ·
    refine ⟨85544641054935020662301963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57029760703290013774867975 85544641054935020662301963)
    ·
      refine ⟨128316961582402530993452945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85544641054935020662301963 128316961582402530993452945)
      ·
        refine ⟨96237721186801898245089709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128316961582402530993452945 96237721186801898245089709)
        ·
          refine ⟨36089145445050711841908641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96237721186801898245089709 36089145445050711841908641)
          ·
            refine ⟨27066859083788033881431481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36089145445050711841908641 27066859083788033881431481)
            ·
              refine ⟨20300144312841025411073611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27066859083788033881431481 20300144312841025411073611)
              ·
                refine ⟨30450216469261538116610417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20300144312841025411073611 30450216469261538116610417)
                ·
                  refine ⟨22837662351946153587457813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30450216469261538116610417 22837662351946153587457813)
                  ·
                    refine ⟨1070515422747475949412085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22837662351946153587457813 1070515422747475949412085)
                    ·
                      rfl

theorem cell22_3127232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_3127232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127232 prefixEnd_3127232 := by exact prefixLift 3127232
  have htrace : WordTrace (prefixWord ++ tailWord_3127232) baseStart_3127232 baseEnd_3127232 := by
    simpa [prefixWord, tailWord_3127232, baseEnd_3127232] using wordTrace_append hprefix tailTrace_3127232
  have hstable : (prefixWord ++ tailWord_3127232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127232).length < 2 ^ (prefixWord ++ tailWord_3127232).sum := by decide
  have hdescent : baseEnd_3127232 < baseStart_3127232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127281 : List Nat := [1, 2, 2, 2, 5, 1, 2, 2, 5]
def baseStart_3127281 : Nat := 118140960795 + 3127281 * 2 ^ 59
def prefixEnd_3127281 : Nat := 4983230072969 + 3 ^ 40 * 3127281 * 2
def baseEnd_3127281 : Nat := 356844065482952051645645

theorem tailTrace_3127281 : CollatzResearch.WordTrace tailWord_3127281 prefixEnd_3127281 356844065482952051645645 := by
  unfold tailWord_3127281
  simp only [CollatzResearch.WordTrace]
  refine ⟨114061308583402508918269697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76040872388935005945513131 114061308583402508918269697)
  ·
    refine ⟨85545981437551881688702273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114061308583402508918269697 85545981437551881688702273)
    ·
      refine ⟨64159486078163911266526705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85545981437551881688702273 64159486078163911266526705)
      ·
        refine ⟨48119614558622933449895029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64159486078163911266526705 48119614558622933449895029)
        ·
          refine ⟨4511213864870900010927659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48119614558622933449895029 4511213864870900010927659)
          ·
            refine ⟨6766820797306350016391489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4511213864870900010927659 6766820797306350016391489)
            ·
              refine ⟨5075115597979762512293617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6766820797306350016391489 5075115597979762512293617)
              ·
                refine ⟨3806336698484821884220213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5075115597979762512293617 3806336698484821884220213)
                ·
                  refine ⟨356844065482952051645645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3806336698484821884220213 356844065482952051645645)
                  ·
                    rfl

theorem cell22_3127281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 5].length) (baseStart_3127281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127281 prefixEnd_3127281 := by exact prefixLift 3127281
  have htrace : WordTrace (prefixWord ++ tailWord_3127281) baseStart_3127281 baseEnd_3127281 := by
    simpa [prefixWord, tailWord_3127281, baseEnd_3127281] using wordTrace_append hprefix tailTrace_3127281
  have hstable : (prefixWord ++ tailWord_3127281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127281).length < 2 ^ (prefixWord ++ tailWord_3127281).sum := by decide
  have hdescent : baseEnd_3127281 < baseStart_3127281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127399 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 7]
def baseStart_3127399 : Nat := 118140960795 + 3127399 * 2 ^ 59
def prefixEnd_3127399 : Nat := 4983230072969 + 3 ^ 40 * 3127399 * 2
def baseEnd_3127399 : Nat := 356857530086781060162191

theorem tailTrace_3127399 : CollatzResearch.WordTrace tailWord_3127399 prefixEnd_3127399 356857530086781060162191 := by
  unfold tailWord_3127399
  simp only [CollatzResearch.WordTrace]
  refine ⟨114065612396975015071065251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76043741597983343380710167 114065612396975015071065251)
  ·
    refine ⟨171098418595462522606597877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114065612396975015071065251 171098418595462522606597877)
    ·
      refine ⟨16040476743324611494368551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171098418595462522606597877 16040476743324611494368551)
      ·
        refine ⟨24060715114986917241552827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16040476743324611494368551 24060715114986917241552827)
        ·
          refine ⟨36091072672480375862329241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24060715114986917241552827 36091072672480375862329241)
          ·
            refine ⟨27068304504360281896746931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36091072672480375862329241 27068304504360281896746931)
            ·
              refine ⟨40602456756540422845120397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27068304504360281896746931 40602456756540422845120397)
              ·
                refine ⟨15225921283702658566920149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40602456756540422845120397 15225921283702658566920149)
                ·
                  refine ⟨356857530086781060162191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15225921283702658566920149 356857530086781060162191)
                  ·
                    rfl

theorem cell22_3127399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 7].length) (baseStart_3127399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127399 prefixEnd_3127399 := by exact prefixLift 3127399
  have htrace : WordTrace (prefixWord ++ tailWord_3127399) baseStart_3127399 baseEnd_3127399 := by
    simpa [prefixWord, tailWord_3127399, baseEnd_3127399] using wordTrace_append hprefix tailTrace_3127399
  have hstable : (prefixWord ++ tailWord_3127399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127399).length < 2 ^ (prefixWord ++ tailWord_3127399).sum := by decide
  have hdescent : baseEnd_3127399 < baseStart_3127399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127504 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 3, 9]
def baseStart_3127504 : Nat := 118140960795 + 3127504 * 2 ^ 59
def prefixEnd_3127504 : Nat := 4983230072969 + 3 ^ 40 * 3127504 * 2
def baseEnd_3127504 : Nat := 1070608533906157906611251

theorem tailTrace_3127504 : CollatzResearch.WordTrace tailWord_3127504 prefixEnd_3127504 1070608533906157906611251 := by
  unfold tailWord_3127504
  simp only [CollatzResearch.WordTrace]
  refine ⟨57034721030797309001818783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76046294707729745335758377 57034721030797309001818783)
  ·
    refine ⟨85552081546195963502728175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57034721030797309001818783 85552081546195963502728175)
    ·
      refine ⟨128328122319293945254092263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85552081546195963502728175 128328122319293945254092263)
      ·
        refine ⟨192492183478940917881138395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128328122319293945254092263 192492183478940917881138395)
        ·
          refine ⟨288738275218411376821707593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192492183478940917881138395 288738275218411376821707593)
          ·
            refine ⟨216553706413808532616280695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288738275218411376821707593 216553706413808532616280695)
            ·
              refine ⟨324830559620712798924421043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216553706413808532616280695 324830559620712798924421043)
              ·
                refine ⟨487245839431069198386631565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324830559620712798924421043 487245839431069198386631565)
                ·
                  refine ⟨182717189786650949394986837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487245839431069198386631565 182717189786650949394986837)
                  ·
                    refine ⟨1070608533906157906611251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 182717189786650949394986837 1070608533906157906611251)
                    ·
                      rfl

theorem cell22_3127504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_3127504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127504 prefixEnd_3127504 := by exact prefixLift 3127504
  have htrace : WordTrace (prefixWord ++ tailWord_3127504) baseStart_3127504 baseEnd_3127504 := by
    simpa [prefixWord, tailWord_3127504, baseEnd_3127504] using wordTrace_append hprefix tailTrace_3127504
  have hstable : (prefixWord ++ tailWord_3127504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127504).length < 2 ^ (prefixWord ++ tailWord_3127504).sum := by decide
  have hdescent : baseEnd_3127504 < baseStart_3127504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127506 : List Nat := [3, 2, 2, 2, 1, 3, 9]
def baseStart_3127506 : Nat := 118140960795 + 3127506 * 2 ^ 59
def prefixEnd_3127506 : Nat := 4983230072969 + 3 ^ 40 * 3127506 * 2
def baseEnd_3127506 : Nat := 39652193279519650668935

theorem tailTrace_3127506 : CollatzResearch.WordTrace tailWord_3127506 prefixEnd_3127506 39652193279519650668935 := by
  unfold tailWord_3127506
  simp only [CollatzResearch.WordTrace]
  refine ⟨28517378751896843086302593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76046343338391581563473581 28517378751896843086302593)
  ·
    refine ⟨21388034063922632314726945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28517378751896843086302593 21388034063922632314726945)
    ·
      refine ⟨16041025547941974236045209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21388034063922632314726945 16041025547941974236045209)
      ·
        refine ⟨12030769160956480677033907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16041025547941974236045209 12030769160956480677033907)
        ·
          refine ⟨18046153741434721015550861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12030769160956480677033907 18046153741434721015550861)
          ·
            refine ⟨6767307653038020380831573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18046153741434721015550861 6767307653038020380831573)
            ·
              refine ⟨39652193279519650668935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6767307653038020380831573 39652193279519650668935)
              ·
                rfl

theorem cell22_3127506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 9].length) (baseStart_3127506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127506 prefixEnd_3127506 := by exact prefixLift 3127506
  have htrace : WordTrace (prefixWord ++ tailWord_3127506) baseStart_3127506 baseEnd_3127506 := by
    simpa [prefixWord, tailWord_3127506, baseEnd_3127506] using wordTrace_append hprefix tailTrace_3127506
  have hstable : (prefixWord ++ tailWord_3127506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127506).length < 2 ^ (prefixWord ++ tailWord_3127506).sum := by decide
  have hdescent : baseEnd_3127506 < baseStart_3127506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127527 : List Nat := [1, 1, 5, 3, 1, 2, 3, 1, 2, 3]
def baseStart_3127527 : Nat := 118140960795 + 3127527 * 2 ^ 59
def prefixEnd_3127527 : Nat := 4983230072969 + 3 ^ 40 * 3127527 * 2
def baseEnd_3127527 : Nat := 1070616407276193513286181

theorem tailTrace_3127527 : CollatzResearch.WordTrace tailWord_3127527 prefixEnd_3127527 1070616407276193513286181 := by
  unfold tailWord_3127527
  simp only [CollatzResearch.WordTrace]
  refine ⟨114070280940511292931724835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76046853960340861954483223 114070280940511292931724835)
  ·
    refine ⟨171105421410766939397587253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114070280940511292931724835 171105421410766939397587253)
    ·
      refine ⟨16041133257259400568523805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171105421410766939397587253 16041133257259400568523805)
      ·
        refine ⟨6015424971472275213196427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16041133257259400568523805 6015424971472275213196427)
        ·
          refine ⟨9023137457208412819794641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6015424971472275213196427 9023137457208412819794641)
          ·
            refine ⟨6767353092906309614845981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9023137457208412819794641 6767353092906309614845981)
            ·
              refine ⟨2537757409839866105567243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6767353092906309614845981 2537757409839866105567243)
              ·
                refine ⟨3806636114759799158350865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2537757409839866105567243 3806636114759799158350865)
                ·
                  refine ⟨2854977086069849368763149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3806636114759799158350865 2854977086069849368763149)
                  ·
                    refine ⟨1070616407276193513286181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2854977086069849368763149 1070616407276193513286181)
                    ·
                      rfl

theorem cell22_3127527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_3127527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127527 prefixEnd_3127527 := by exact prefixLift 3127527
  have htrace : WordTrace (prefixWord ++ tailWord_3127527) baseStart_3127527 baseEnd_3127527 := by
    simpa [prefixWord, tailWord_3127527, baseEnd_3127527] using wordTrace_append hprefix tailTrace_3127527
  have hstable : (prefixWord ++ tailWord_3127527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127527).length < 2 ^ (prefixWord ++ tailWord_3127527).sum := by decide
  have hdescent : baseEnd_3127527 < baseStart_3127527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127596 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 6]
def baseStart_3127596 : Nat := 118140960795 + 3127596 * 2 ^ 59
def prefixEnd_3127596 : Nat := 4983230072969 + 3 ^ 40 * 3127596 * 2
def baseEnd_3127596 : Nat := 356880009128766777770323

theorem tailTrace_3127596 : CollatzResearch.WordTrace tailWord_3127596 prefixEnd_3127596 356880009128766777770323 := by
  unfold tailWord_3127596
  simp only [CollatzResearch.WordTrace]
  refine ⟨57036398788630658857993321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76048531718174211810657761 57036398788630658857993321)
  ·
    refine ⟨42777299091472994143494991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57036398788630658857993321 42777299091472994143494991)
    ·
      refine ⟨64165948637209491215242487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42777299091472994143494991 64165948637209491215242487)
      ·
        refine ⟨96248922955814236822863731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64165948637209491215242487 96248922955814236822863731)
        ·
          refine ⟨144373384433721355234295597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96248922955814236822863731 144373384433721355234295597)
          ·
            refine ⟨54140019162645508212860849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144373384433721355234295597 54140019162645508212860849)
            ·
              refine ⟨40605014371984131159645637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54140019162645508212860849 40605014371984131159645637)
              ·
                refine ⟨7613440194747024592433557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40605014371984131159645637 7613440194747024592433557)
                ·
                  refine ⟨356880009128766777770323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7613440194747024592433557 356880009128766777770323)
                  ·
                    rfl

theorem cell22_3127596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_3127596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127596 prefixEnd_3127596 := by exact prefixLift 3127596
  have htrace : WordTrace (prefixWord ++ tailWord_3127596) baseStart_3127596 baseEnd_3127596 := by
    simpa [prefixWord, tailWord_3127596, baseEnd_3127596] using wordTrace_append hprefix tailTrace_3127596
  have hstable : (prefixWord ++ tailWord_3127596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127596).length < 2 ^ (prefixWord ++ tailWord_3127596).sum := by decide
  have hdescent : baseEnd_3127596 < baseStart_3127596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127615 : List Nat := [1, 1, 2, 2, 4, 1, 5, 1, 1, 4]
def baseStart_3127615 : Nat := 118140960795 + 3127615 * 2 ^ 59
def prefixEnd_3127615 : Nat := 4983230072969 + 3 ^ 40 * 3127615 * 2
def baseEnd_3127615 : Nat := 1070646531474590617085911

theorem tailTrace_3127615 : CollatzResearch.WordTrace tailWord_3127615 prefixEnd_3127615 1070646531474590617085911 := by
  unfold tailWord_3127615
  simp only [CollatzResearch.WordTrace]
  refine ⟨114073490564192483960928299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76048993709461655973952199 114073490564192483960928299)
  ·
    refine ⟨171110235846288725941392449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114073490564192483960928299 171110235846288725941392449)
    ·
      refine ⟨128332676884716544456044337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171110235846288725941392449 128332676884716544456044337)
      ·
        refine ⟨96249507663537408342033253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128332676884716544456044337 96249507663537408342033253)
        ·
          refine ⟨18046782686913264064131235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96249507663537408342033253 18046782686913264064131235)
          ·
            refine ⟨27070174030369896096196853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18046782686913264064131235 27070174030369896096196853)
            ·
              refine ⟨2537828815347177759018455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27070174030369896096196853 2537828815347177759018455)
              ·
                refine ⟨3806743223020766638527683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2537828815347177759018455 3806743223020766638527683)
                ·
                  refine ⟨5710114834531149957791525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3806743223020766638527683 5710114834531149957791525)
                  ·
                    refine ⟨1070646531474590617085911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5710114834531149957791525 1070646531474590617085911)
                    ·
                      rfl

theorem cell22_3127615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 1, 4].length) (baseStart_3127615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127615 prefixEnd_3127615 := by exact prefixLift 3127615
  have htrace : WordTrace (prefixWord ++ tailWord_3127615) baseStart_3127615 baseEnd_3127615 := by
    simpa [prefixWord, tailWord_3127615, baseEnd_3127615] using wordTrace_append hprefix tailTrace_3127615
  have hstable : (prefixWord ++ tailWord_3127615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127615).length < 2 ^ (prefixWord ++ tailWord_3127615).sum := by decide
  have hdescent : baseEnd_3127615 < baseStart_3127615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127626 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 5, 6]
def baseStart_3127626 : Nat := 118140960795 + 3127626 * 2 ^ 59
def prefixEnd_3127626 : Nat := 4983230072969 + 3 ^ 40 * 3127626 * 2
def baseEnd_3127626 : Nat := 1070650296999390255060877

theorem tailTrace_3127626 : CollatzResearch.WordTrace tailWord_3127626 prefixEnd_3127626 1070650296999390255060877 := by
  unfold tailWord_3127626
  simp only [CollatzResearch.WordTrace]
  refine ⟨28518472941788158209894683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76049261178101755226385821 28518472941788158209894683)
  ·
    refine ⟨42777709412682237314842025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28518472941788158209894683 42777709412682237314842025)
    ·
      refine ⟨32083282059511677986131519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42777709412682237314842025 32083282059511677986131519)
      ·
        refine ⟨48124923089267516979197279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32083282059511677986131519 48124923089267516979197279)
        ·
          refine ⟨72187384633901275468795919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48124923089267516979197279 72187384633901275468795919)
          ·
            refine ⟨108281076950851913203193879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72187384633901275468795919 108281076950851913203193879)
            ·
              refine ⟨162421615426277869804790819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108281076950851913203193879 162421615426277869804790819)
              ·
                refine ⟨243632423139416804707186229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162421615426277869804790819 243632423139416804707186229)
                ·
                  refine ⟨22840539669320325441298709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 243632423139416804707186229 22840539669320325441298709)
                  ·
                    refine ⟨1070650296999390255060877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22840539669320325441298709 1070650296999390255060877)
                    ·
                      rfl

theorem cell22_3127626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_3127626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127626 prefixEnd_3127626 := by exact prefixLift 3127626
  have htrace : WordTrace (prefixWord ++ tailWord_3127626) baseStart_3127626 baseEnd_3127626 := by
    simpa [prefixWord, tailWord_3127626, baseEnd_3127626] using wordTrace_append hprefix tailTrace_3127626
  have hstable : (prefixWord ++ tailWord_3127626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127626).length < 2 ^ (prefixWord ++ tailWord_3127626).sum := by decide
  have hdescent : baseEnd_3127626 < baseStart_3127626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127671 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 1, 8]
def baseStart_3127671 : Nat := 118140960795 + 3127671 * 2 ^ 59
def prefixEnd_3127671 : Nat := 4983230072969 + 3 ^ 40 * 3127671 * 2
def baseEnd_3127671 : Nat := 1070665701419025137685739

theorem tailTrace_3127671 : CollatzResearch.WordTrace tailWord_3127671 prefixEnd_3127671 1070665701419025137685739 := by
  unfold tailWord_3127671
  simp only [CollatzResearch.WordTrace]
  refine ⟨114075533051989605524966867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76050355367993070349977911 114075533051989605524966867)
  ·
    refine ⟨171113299577984408287450301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114075533051989605524966867 171113299577984408287450301)
    ·
      refine ⟨64167487341744153107793863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171113299577984408287450301 64167487341744153107793863)
      ·
        refine ⟨96251231012616229661690795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64167487341744153107793863 96251231012616229661690795)
        ·
          refine ⟨144376846518924344492536193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96251231012616229661690795 144376846518924344492536193)
          ·
            refine ⟨108282634889193258369402145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144376846518924344492536193 108282634889193258369402145)
            ·
              refine ⟨81211976166894943777051609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108282634889193258369402145 81211976166894943777051609)
              ·
                refine ⟨60908982125171207832788707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81211976166894943777051609 60908982125171207832788707)
                ·
                  refine ⟨91363473187756811749183061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60908982125171207832788707 91363473187756811749183061)
                  ·
                    refine ⟨1070665701419025137685739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91363473187756811749183061 1070665701419025137685739)
                    ·
                      rfl

theorem cell22_3127671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_3127671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127671 prefixEnd_3127671 := by exact prefixLift 3127671
  have htrace : WordTrace (prefixWord ++ tailWord_3127671) baseStart_3127671 baseEnd_3127671 := by
    simpa [prefixWord, tailWord_3127671, baseEnd_3127671] using wordTrace_append hprefix tailTrace_3127671
  have hstable : (prefixWord ++ tailWord_3127671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127671).length < 2 ^ (prefixWord ++ tailWord_3127671).sum := by decide
  have hdescent : baseEnd_3127671 < baseStart_3127671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127673 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 7, 3]
def baseStart_3127673 : Nat := 118140960795 + 3127673 * 2 ^ 59
def prefixEnd_3127673 : Nat := 4983230072969 + 3 ^ 40 * 3127673 * 2
def baseEnd_3127673 : Nat := 1070666386059897799135733

theorem tailTrace_3127673 : CollatzResearch.WordTrace tailWord_3127673 prefixEnd_3127673 1070666386059897799135733 := by
  unfold tailWord_3127673
  simp only [CollatzResearch.WordTrace]
  refine ⟨114075605997982359866539673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76050403998654906577693115 114075605997982359866539673)
  ·
    refine ⟨85556704498486769899904755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114075605997982359866539673 85556704498486769899904755)
    ·
      refine ⟨128335056747730154849857133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85556704498486769899904755 128335056747730154849857133)
      ·
        refine ⟨48125646280398808068696425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128335056747730154849857133 48125646280398808068696425)
        ·
          refine ⟨36094234710299106051522319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48125646280398808068696425 36094234710299106051522319)
          ·
            refine ⟨54141352065448659077283479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36094234710299106051522319 54141352065448659077283479)
            ·
              refine ⟨81212028098172988615925219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54141352065448659077283479 81212028098172988615925219)
              ·
                refine ⟨121818042147259482923887829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81212028098172988615925219 121818042147259482923887829)
                ·
                  refine ⟨2855110362826394131028621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 121818042147259482923887829 2855110362826394131028621)
                  ·
                    refine ⟨1070666386059897799135733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2855110362826394131028621 1070666386059897799135733)
                    ·
                      rfl

theorem cell22_3127673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 3].length) (baseStart_3127673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127673 prefixEnd_3127673 := by exact prefixLift 3127673
  have htrace : WordTrace (prefixWord ++ tailWord_3127673) baseStart_3127673 baseEnd_3127673 := by
    simpa [prefixWord, tailWord_3127673, baseEnd_3127673] using wordTrace_append hprefix tailTrace_3127673
  have hstable : (prefixWord ++ tailWord_3127673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127673).length < 2 ^ (prefixWord ++ tailWord_3127673).sum := by decide
  have hdescent : baseEnd_3127673 < baseStart_3127673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127703 : List Nat := [1, 1, 3, 3, 1, 1, 2, 5, 5]
def baseStart_3127703 : Nat := 118140960795 + 3127703 * 2 ^ 59
def prefixEnd_3127703 : Nat := 4983230072969 + 3 ^ 40 * 3127703 * 2
def baseEnd_3127703 : Nat := 356892218557662573628547

theorem tailTrace_3127703 : CollatzResearch.WordTrace tailWord_3127703 prefixEnd_3127703 356892218557662573628547 := by
  unfold tailWord_3127703
  simp only [CollatzResearch.WordTrace]
  refine ⟨114076700187873674990131763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76051133458582449993421175 114076700187873674990131763)
  ·
    refine ⟨171115050281810512485197645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114076700187873674990131763 171115050281810512485197645)
    ·
      refine ⟨64168143855678942181949117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171115050281810512485197645 64168143855678942181949117)
      ·
        refine ⟨24063053945879603318230919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64168143855678942181949117 24063053945879603318230919)
        ·
          refine ⟨36094580918819404977346379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24063053945879603318230919 36094580918819404977346379)
          ·
            refine ⟨54141871378229107466019569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36094580918819404977346379 54141871378229107466019569)
            ·
              refine ⟨40606403533671830599514677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54141871378229107466019569 40606403533671830599514677)
              ·
                refine ⟨3806850331281734118704501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40606403533671830599514677 3806850331281734118704501)
                ·
                  refine ⟨356892218557662573628547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3806850331281734118704501 356892218557662573628547)
                  ·
                    rfl

theorem cell22_3127703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 5].length) (baseStart_3127703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127703 prefixEnd_3127703 := by exact prefixLift 3127703
  have htrace : WordTrace (prefixWord ++ tailWord_3127703) baseStart_3127703 baseEnd_3127703 := by
    simpa [prefixWord, tailWord_3127703, baseEnd_3127703] using wordTrace_append hprefix tailTrace_3127703
  have hstable : (prefixWord ++ tailWord_3127703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127703).length < 2 ^ (prefixWord ++ tailWord_3127703).sum := by decide
  have hdescent : baseEnd_3127703 < baseStart_3127703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127720 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 7]
def baseStart_3127720 : Nat := 118140960795 + 3127720 * 2 ^ 59
def prefixEnd_3127720 : Nat := 4983230072969 + 3 ^ 40 * 3127720 * 2
def baseEnd_3127720 : Nat := 356894158373468447736863

theorem tailTrace_3127720 : CollatzResearch.WordTrace tailWord_3127720 prefixEnd_3127720 356894158373468447736863 := by
  unfold tailWord_3127720
  simp only [CollatzResearch.WordTrace]
  refine ⟨57038660114406043446750307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76051546819208057929000409 57038660114406043446750307)
  ·
    refine ⟨85557990171609065170125461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57038660114406043446750307 85557990171609065170125461)
    ·
      refine ⟨4010530789294174929849631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85557990171609065170125461 4010530789294174929849631)
      ·
        refine ⟨6015796183941262394774447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4010530789294174929849631 6015796183941262394774447)
        ·
          refine ⟨9023694275911893592161671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6015796183941262394774447 9023694275911893592161671)
          ·
            refine ⟨13535541413867840388242507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9023694275911893592161671 13535541413867840388242507)
            ·
              refine ⟨20303312120801760582363761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13535541413867840388242507 20303312120801760582363761)
              ·
                refine ⟨15227484090601320436772821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20303312120801760582363761 15227484090601320436772821)
                ·
                  refine ⟨356894158373468447736863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15227484090601320436772821 356894158373468447736863)
                  ·
                    rfl

theorem cell22_3127720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 7].length) (baseStart_3127720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127720 prefixEnd_3127720 := by exact prefixLift 3127720
  have htrace : WordTrace (prefixWord ++ tailWord_3127720) baseStart_3127720 baseEnd_3127720 := by
    simpa [prefixWord, tailWord_3127720, baseEnd_3127720] using wordTrace_append hprefix tailTrace_3127720
  have hstable : (prefixWord ++ tailWord_3127720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127720).length < 2 ^ (prefixWord ++ tailWord_3127720).sum := by decide
  have hdescent : baseEnd_3127720 < baseStart_3127720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127917 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 6]
def baseStart_3127917 : Nat := 118140960795 + 3127917 * 2 ^ 59
def prefixEnd_3127917 : Nat := 4983230072969 + 3 ^ 40 * 3127917 * 2
def baseEnd_3127917 : Nat := 356916637415454165344995

theorem tailTrace_3127917 : CollatzResearch.WordTrace tailWord_3127917 prefixEnd_3127917 356916637415454165344995 := by
  unfold tailWord_3127917
  simp only [CollatzResearch.WordTrace]
  refine ⟨114084505409098389538422005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76056336939398926358948003 114084505409098389538422005)
  ·
    refine ⟨10695422382102974019227063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114084505409098389538422005 10695422382102974019227063)
    ·
      refine ⟨16043133573154461028840595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10695422382102974019227063 16043133573154461028840595)
      ·
        refine ⟨24064700359731691543260893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16043133573154461028840595 24064700359731691543260893)
        ·
          refine ⟨9024262634899384328722835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24064700359731691543260893 9024262634899384328722835)
          ·
            refine ⟨13536393952349076493084253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9024262634899384328722835 13536393952349076493084253)
            ·
              refine ⟨5076147732130903684906595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13536393952349076493084253 5076147732130903684906595)
              ·
                refine ⟨7614221598196355527359893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5076147732130903684906595 7614221598196355527359893)
                ·
                  refine ⟨356916637415454165344995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7614221598196355527359893 356916637415454165344995)
                  ·
                    rfl

theorem cell22_3127917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_3127917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127917 prefixEnd_3127917 := by exact prefixLift 3127917
  have htrace : WordTrace (prefixWord ++ tailWord_3127917) baseStart_3127917 baseEnd_3127917 := by
    simpa [prefixWord, tailWord_3127917, baseEnd_3127917] using wordTrace_append hprefix tailTrace_3127917
  have hstable : (prefixWord ++ tailWord_3127917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127917).length < 2 ^ (prefixWord ++ tailWord_3127917).sum := by decide
  have hdescent : baseEnd_3127917 < baseStart_3127917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127962 : List Nat := [3, 1, 1, 6, 1, 10]
def baseStart_3127962 : Nat := 118140960795 + 3127962 * 2 ^ 59
def prefixEnd_3127962 : Nat := 4983230072969 + 3 ^ 40 * 3127962 * 2
def baseEnd_3127962 : Nat := 13219324897111078748887

theorem tailTrace_3127962 : CollatzResearch.WordTrace tailWord_3127962 prefixEnd_3127962 13219324897111078748887 := by
  unfold tailWord_3127962
  simp only [CollatzResearch.WordTrace]
  refine ⟨28521536673483840555952535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76057431129290241482540093 28521536673483840555952535)
  ·
    refine ⟨42782305010225760833928803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28521536673483840555952535 42782305010225760833928803)
    ·
      refine ⟨64173457515338641250893205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42782305010225760833928803 64173457515338641250893205)
      ·
        refine ⟨3008130821031498808635619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64173457515338641250893205 3008130821031498808635619)
        ·
          refine ⟨4512196231547248212953429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3008130821031498808635619 4512196231547248212953429)
          ·
            refine ⟨13219324897111078748887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4512196231547248212953429 13219324897111078748887)
            ·
              rfl

theorem cell22_3127962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 10].length) (baseStart_3127962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127962 prefixEnd_3127962 := by exact prefixLift 3127962
  have htrace : WordTrace (prefixWord ++ tailWord_3127962) baseStart_3127962 baseEnd_3127962 := by
    simpa [prefixWord, tailWord_3127962, baseEnd_3127962] using wordTrace_append hprefix tailTrace_3127962
  have hstable : (prefixWord ++ tailWord_3127962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127962).length < 2 ^ (prefixWord ++ tailWord_3127962).sum := by decide
  have hdescent : baseEnd_3127962 < baseStart_3127962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127966 : List Nat := [4, 3, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_3127966 : Nat := 118140960795 + 3127966 * 2 ^ 59
def prefixEnd_3127966 : Nat := 4983230072969 + 3 ^ 40 * 3127966 * 2
def baseEnd_3127966 : Nat := 1070766685947742701559835

theorem tailTrace_3127966 : CollatzResearch.WordTrace tailWord_3127966 prefixEnd_3127966 1070766685947742701559835 := by
  unfold tailWord_3127966
  simp only [CollatzResearch.WordTrace]
  refine ⟨14260786573240108863369469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76057528390613913937970501 14260786573240108863369469)
  ·
    refine ⟨5347794964965040823763551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14260786573240108863369469 5347794964965040823763551)
    ·
      refine ⟨8021692447447561235645327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5347794964965040823763551 8021692447447561235645327)
      ·
        refine ⟨12032538671171341853467991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8021692447447561235645327 12032538671171341853467991)
        ·
          refine ⟨18048808006757012780201987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12032538671171341853467991 18048808006757012780201987)
          ·
            refine ⟨27073212010135519170302981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18048808006757012780201987 27073212010135519170302981)
            ·
              refine ⟨5076227251900409844431809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27073212010135519170302981 5076227251900409844431809)
              ·
                refine ⟨3807170438925307383323857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5076227251900409844431809 3807170438925307383323857)
                ·
                  refine ⟨2855377829193980537492893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3807170438925307383323857 2855377829193980537492893)
                  ·
                    refine ⟨1070766685947742701559835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2855377829193980537492893 1070766685947742701559835)
                    ·
                      rfl

theorem cell22_3127966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_3127966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127966 prefixEnd_3127966 := by exact prefixLift 3127966
  have htrace : WordTrace (prefixWord ++ tailWord_3127966) baseStart_3127966 baseEnd_3127966 := by
    simpa [prefixWord, tailWord_3127966, baseEnd_3127966] using wordTrace_append hprefix tailTrace_3127966
  have hstable : (prefixWord ++ tailWord_3127966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127966).length < 2 ^ (prefixWord ++ tailWord_3127966).sum := by decide
  have hdescent : baseEnd_3127966 < baseStart_3127966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127968 : List Nat := [2, 1, 1, 4, 5, 1, 2, 2, 4]
def baseStart_3127968 : Nat := 118140960795 + 3127968 * 2 ^ 59
def prefixEnd_3127968 : Nat := 4983230072969 + 3 ^ 40 * 3127968 * 2
def baseEnd_3127968 : Nat := 356922456862871787669943

theorem tailTrace_3127968 : CollatzResearch.WordTrace tailWord_3127968 prefixEnd_3127968 356922456862871787669943 := by
  unfold tailWord_3127968
  simp only [CollatzResearch.WordTrace]
  refine ⟨57043182765956812624264279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76057577021275750165685705 57043182765956812624264279)
  ·
    refine ⟨85564774148935218936396419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57043182765956812624264279 85564774148935218936396419)
    ·
      refine ⟨128347161223402828404594629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85564774148935218936396419 128347161223402828404594629)
      ·
        refine ⟨24065092729388030325861493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128347161223402828404594629 24065092729388030325861493)
        ·
          refine ⟨2256102443380127843049515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24065092729388030325861493 2256102443380127843049515)
          ·
            refine ⟨3384153665070191764574273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256102443380127843049515 3384153665070191764574273)
            ·
              refine ⟨2538115248802643823430705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3384153665070191764574273 2538115248802643823430705)
              ·
                refine ⟨1903586436601982867573029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2538115248802643823430705 1903586436601982867573029)
                ·
                  refine ⟨356922456862871787669943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1903586436601982867573029 356922456862871787669943)
                  ·
                    rfl

theorem cell22_3127968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 4].length) (baseStart_3127968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3127968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3127968 prefixEnd_3127968 := by exact prefixLift 3127968
  have htrace : WordTrace (prefixWord ++ tailWord_3127968) baseStart_3127968 baseEnd_3127968 := by
    simpa [prefixWord, tailWord_3127968, baseEnd_3127968] using wordTrace_append hprefix tailTrace_3127968
  have hstable : (prefixWord ++ tailWord_3127968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127968).length < 2 ^ (prefixWord ++ tailWord_3127968).sum := by decide
  have hdescent : baseEnd_3127968 < baseStart_3127968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128005 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 6, 5]
def baseStart_3128005 : Nat := 118140960795 + 3128005 * 2 ^ 59
def prefixEnd_3128005 : Nat := 4983230072969 + 3 ^ 40 * 3128005 * 2
def baseEnd_3128005 : Nat := 1070780036444759599834715

theorem tailTrace_3128005 : CollatzResearch.WordTrace tailWord_3128005 prefixEnd_3128005 1070780036444759599834715 := by
  unfold tailWord_3128005
  simp only [CollatzResearch.WordTrace]
  refine ⟨114087715032779580567625469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76058476688519720378416979 114087715032779580567625469)
  ·
    refine ⟨42782893137292342712859551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114087715032779580567625469 42782893137292342712859551)
    ·
      refine ⟨64174339705938514069289327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42782893137292342712859551 64174339705938514069289327)
      ·
        refine ⟨96261509558907771103933991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64174339705938514069289327 96261509558907771103933991)
        ·
          refine ⟨144392264338361656655900987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96261509558907771103933991 144392264338361656655900987)
          ·
            refine ⟨216588396507542484983851481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144392264338361656655900987 216588396507542484983851481)
            ·
              refine ⟨162441297380656863737888611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216588396507542484983851481 162441297380656863737888611)
              ·
                refine ⟨243661946070985295606832917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162441297380656863737888611 243661946070985295606832917)
                ·
                  refine ⟨11421653722077435731570293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 243661946070985295606832917 11421653722077435731570293)
                  ·
                    refine ⟨1070780036444759599834715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11421653722077435731570293 1070780036444759599834715)
                    ·
                      rfl

theorem cell22_3128005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_3128005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128005 prefixEnd_3128005 := by exact prefixLift 3128005
  have htrace : WordTrace (prefixWord ++ tailWord_3128005) baseStart_3128005 baseEnd_3128005 := by
    simpa [prefixWord, tailWord_3128005, baseEnd_3128005] using wordTrace_append hprefix tailTrace_3128005
  have hstable : (prefixWord ++ tailWord_3128005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128005).length < 2 ^ (prefixWord ++ tailWord_3128005).sum := by decide
  have hdescent : baseEnd_3128005 < baseStart_3128005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128024 : List Nat := [2, 1, 2, 2, 3, 4, 1, 2, 5]
def baseStart_3128024 : Nat := 118140960795 + 3128024 * 2 ^ 59
def prefixEnd_3128024 : Nat := 4983230072969 + 3 ^ 40 * 3128024 * 2
def baseEnd_3128024 : Nat := 356928846844349961203219

theorem tailTrace_3128024 : CollatzResearch.WordTrace tailWord_3128024 prefixEnd_3128024 356928846844349961203219 := by
  unfold tailWord_3128024
  simp only [CollatzResearch.WordTrace]
  refine ⟨57044204009855373406283563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76058938679807164541711417 57044204009855373406283563)
  ·
    refine ⟨85566306014783060109425345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57044204009855373406283563 85566306014783060109425345)
    ·
      refine ⟨64174729511087295082069009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85566306014783060109425345 64174729511087295082069009)
      ·
        refine ⟨48131047133315471311551757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64174729511087295082069009 48131047133315471311551757)
        ·
          refine ⟨18049142674993301741831909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48131047133315471311551757 18049142674993301741831909)
          ·
            refine ⟨3384214251561244076593483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18049142674993301741831909 3384214251561244076593483)
            ·
              refine ⟨5076321377341866114890225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3384214251561244076593483 5076321377341866114890225)
              ·
                refine ⟨3807241033006399586167669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5076321377341866114890225 3807241033006399586167669)
                ·
                  refine ⟨356928846844349961203219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3807241033006399586167669 356928846844349961203219)
                  ·
                    rfl

theorem cell22_3128024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 5].length) (baseStart_3128024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128024 prefixEnd_3128024 := by exact prefixLift 3128024
  have htrace : WordTrace (prefixWord ++ tailWord_3128024) baseStart_3128024 baseEnd_3128024 := by
    simpa [prefixWord, tailWord_3128024, baseEnd_3128024] using wordTrace_append hprefix tailTrace_3128024
  have hstable : (prefixWord ++ tailWord_3128024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128024).length < 2 ^ (prefixWord ++ tailWord_3128024).sum := by decide
  have hdescent : baseEnd_3128024 < baseStart_3128024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128028 : List Nat := [2, 2, 5, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3128028 : Nat := 118140960795 + 3128028 * 2 ^ 59
def prefixEnd_3128028 : Nat := 4983230072969 + 3 ^ 40 * 3128028 * 2
def baseEnd_3128028 : Nat := 1070787909814795206509645

theorem tailTrace_3128028 : CollatzResearch.WordTrace tailWord_3128028 prefixEnd_3128028 1070787909814795206509645 := by
  unfold tailWord_3128028
  simp only [CollatzResearch.WordTrace]
  refine ⟨57044276955848127747856369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76059035941130836997141825 57044276955848127747856369)
  ·
    refine ⟨42783207716886095810892277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57044276955848127747856369 42783207716886095810892277)
    ·
      refine ⟨4010925723458071482271151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42783207716886095810892277 4010925723458071482271151)
      ·
        refine ⟨6016388585187107223406727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4010925723458071482271151 6016388585187107223406727)
        ·
          refine ⟨9024582877780660835110091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6016388585187107223406727 9024582877780660835110091)
          ·
            refine ⟨13536874316670991252665137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9024582877780660835110091 13536874316670991252665137)
            ·
              refine ⟨10152655737503243439498853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13536874316670991252665137 10152655737503243439498853)
              ·
                refine ⟨1903622950781858144906035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10152655737503243439498853 1903622950781858144906035)
                ·
                  refine ⟨2855434426172787217359053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903622950781858144906035 2855434426172787217359053)
                  ·
                    refine ⟨1070787909814795206509645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2855434426172787217359053 1070787909814795206509645)
                    ·
                      rfl

theorem cell22_3128028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3128028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128028 prefixEnd_3128028 := by exact prefixLift 3128028
  have htrace : WordTrace (prefixWord ++ tailWord_3128028) baseStart_3128028 baseEnd_3128028 := by
    simpa [prefixWord, tailWord_3128028, baseEnd_3128028] using wordTrace_append hprefix tailTrace_3128028
  have hstable : (prefixWord ++ tailWord_3128028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128028).length < 2 ^ (prefixWord ++ tailWord_3128028).sum := by decide
  have hdescent : baseEnd_3128028 < baseStart_3128028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128097 : List Nat := [1, 2, 3, 2, 1, 2, 4, 7]
def baseStart_3128097 : Nat := 118140960795 + 3128097 * 2 ^ 59
def prefixEnd_3128097 : Nat := 4983230072969 + 3 ^ 40 * 3128097 * 2
def baseEnd_3128097 : Nat := 118979058880544669614937

theorem tailTrace_3128097 : CollatzResearch.WordTrace tailWord_3128097 prefixEnd_3128097 118979058880544669614937 := by
  unfold tailWord_3128097
  simp only [CollatzResearch.WordTrace]
  refine ⟨114091070548446280279974545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76060713698964186853316363 114091070548446280279974545)
  ·
    refine ⟨85568302911334710209980909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114091070548446280279974545 85568302911334710209980909)
    ·
      refine ⟨32088113591750516328742841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85568302911334710209980909 32088113591750516328742841)
      ·
        refine ⟨24066085193812887246557131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32088113591750516328742841 24066085193812887246557131)
        ·
          refine ⟨36099127790719330869835697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24066085193812887246557131 36099127790719330869835697)
          ·
            refine ⟨27074345843039498152376773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36099127790719330869835697 27074345843039498152376773)
            ·
              refine ⟨5076439845569905903570645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27074345843039498152376773 5076439845569905903570645)
              ·
                refine ⟨118979058880544669614937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5076439845569905903570645 118979058880544669614937)
                ·
                  rfl

theorem cell22_3128097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 7].length) (baseStart_3128097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128097 prefixEnd_3128097 := by exact prefixLift 3128097
  have htrace : WordTrace (prefixWord ++ tailWord_3128097) baseStart_3128097 baseEnd_3128097 := by
    simpa [prefixWord, tailWord_3128097, baseEnd_3128097] using wordTrace_append hprefix tailTrace_3128097
  have hstable : (prefixWord ++ tailWord_3128097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128097).length < 2 ^ (prefixWord ++ tailWord_3128097).sum := by decide
  have hdescent : baseEnd_3128097 < baseStart_3128097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128142 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 7]
def baseStart_3128142 : Nat := 118140960795 + 3128142 * 2 ^ 59
def prefixEnd_3128142 : Nat := 4983230072969 + 3 ^ 40 * 3128142 * 2
def baseEnd_3128142 : Nat := 356942311448178969719765

theorem tailTrace_3128142 : CollatzResearch.WordTrace tailWord_3128142 prefixEnd_3128142 356942311448178969719765 := by
  unfold tailWord_3128142
  simp only [CollatzResearch.WordTrace]
  refine ⟨14261588979160406620670335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76061807888855501976908453 14261588979160406620670335)
  ·
    refine ⟨21392383468740609931005503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14261588979160406620670335 21392383468740609931005503)
    ·
      refine ⟨32088575203110914896508255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21392383468740609931005503 32088575203110914896508255)
      ·
        refine ⟨48132862804666372344762383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32088575203110914896508255 48132862804666372344762383)
        ·
          refine ⟨72199294206999558517143575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48132862804666372344762383 72199294206999558517143575)
          ·
            refine ⟨108298941310499337775715363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72199294206999558517143575 108298941310499337775715363)
            ·
              refine ⟨162448411965749006663573045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108298941310499337775715363 162448411965749006663573045)
              ·
                refine ⟨15229538621788969374709973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162448411965749006663573045 15229538621788969374709973)
                ·
                  refine ⟨356942311448178969719765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15229538621788969374709973 356942311448178969719765)
                  ·
                    rfl

theorem cell22_3128142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_3128142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128142 prefixEnd_3128142 := by exact prefixLift 3128142
  have htrace : WordTrace (prefixWord ++ tailWord_3128142) baseStart_3128142 baseEnd_3128142 := by
    simpa [prefixWord, tailWord_3128142, baseEnd_3128142] using wordTrace_append hprefix tailTrace_3128142
  have hstable : (prefixWord ++ tailWord_3128142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128142).length < 2 ^ (prefixWord ++ tailWord_3128142).sum := by decide
  have hdescent : baseEnd_3128142 < baseStart_3128142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128249 : List Nat := [1, 2, 1, 4, 2, 4, 8]
def baseStart_3128249 : Nat := 118140960795 + 3128249 * 2 ^ 59
def prefixEnd_3128249 : Nat := 4983230072969 + 3 ^ 40 * 3128249 * 2
def baseEnd_3128249 : Nat := 39661613430786085064221

theorem tailTrace_3128249 : CollatzResearch.WordTrace tailWord_3128249 prefixEnd_3128249 39661613430786085064221 := by
  unfold tailWord_3128249
  simp only [CollatzResearch.WordTrace]
  refine ⟨114096614443895610239507801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76064409629263740159671867 114096614443895610239507801)
  ·
    refine ⟨85572460832921707679630851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114096614443895610239507801 85572460832921707679630851)
    ·
      refine ⟨128358691249382561519446277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85572460832921707679630851 128358691249382561519446277)
      ·
        refine ⟨24067254609259230284896177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128358691249382561519446277 24067254609259230284896177)
        ·
          refine ⟨18050440956944422713672133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24067254609259230284896177 18050440956944422713672133)
          ·
            refine ⟨3384457679427079258813525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18050440956944422713672133 3384457679427079258813525)
            ·
              refine ⟨39661613430786085064221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3384457679427079258813525 39661613430786085064221)
              ·
                rfl

theorem cell22_3128249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 8].length) (baseStart_3128249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128249 prefixEnd_3128249 := by exact prefixLift 3128249
  have htrace : WordTrace (prefixWord ++ tailWord_3128249) baseStart_3128249 baseEnd_3128249 := by
    simpa [prefixWord, tailWord_3128249, baseEnd_3128249] using wordTrace_append hprefix tailTrace_3128249
  have hstable : (prefixWord ++ tailWord_3128249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128249).length < 2 ^ (prefixWord ++ tailWord_3128249).sum := by decide
  have hdescent : baseEnd_3128249 < baseStart_3128249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128270 : List Nat := [4, 1, 1, 1, 2, 5, 2, 1, 2, 3]
def baseStart_3128270 : Nat := 118140960795 + 3128270 * 2 ^ 59
def prefixEnd_3128270 : Nat := 4983230072969 + 3 ^ 40 * 3128270 * 2
def baseEnd_3128270 : Nat := 1070870751360387241958903

theorem tailTrace_3128270 : CollatzResearch.WordTrace tailWord_3128270 prefixEnd_3128270 1070870751360387241958903 := by
  unfold tailWord_3128270
  simp only [CollatzResearch.WordTrace]
  refine ⟨14262172547102441353252783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76064920251213020550681509 14262172547102441353252783)
  ·
    refine ⟨21393258820653662029879175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14262172547102441353252783 21393258820653662029879175)
    ·
      refine ⟨32089888230980493044818763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21393258820653662029879175 32089888230980493044818763)
      ·
        refine ⟨48134832346470739567228145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32089888230980493044818763 48134832346470739567228145)
        ·
          refine ⟨36101124259853054675421109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48134832346470739567228145 36101124259853054675421109)
          ·
            refine ⟨3384480399361223875820729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36101124259853054675421109 3384480399361223875820729)
            ·
              refine ⟨2538360299520917906865547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3384480399361223875820729 2538360299520917906865547)
              ·
                refine ⟨3807540449281376860298321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2538360299520917906865547 3807540449281376860298321)
                ·
                  refine ⟨2855655336961032645223741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3807540449281376860298321 2855655336961032645223741)
                  ·
                    refine ⟨1070870751360387241958903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2855655336961032645223741 1070870751360387241958903)
                    ·
                      rfl

theorem cell22_3128270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_3128270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128270 prefixEnd_3128270 := by exact prefixLift 3128270
  have htrace : WordTrace (prefixWord ++ tailWord_3128270) baseStart_3128270 baseEnd_3128270 := by
    simpa [prefixWord, tailWord_3128270, baseEnd_3128270] using wordTrace_append hprefix tailTrace_3128270
  have hstable : (prefixWord ++ tailWord_3128270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128270).length < 2 ^ (prefixWord ++ tailWord_3128270).sum := by decide
  have hdescent : baseEnd_3128270 < baseStart_3128270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128341 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 3, 4]
def baseStart_3128341 : Nat := 118140960795 + 3128341 * 2 ^ 59
def prefixEnd_3128341 : Nat := 4983230072969 + 3 ^ 40 * 3128341 * 2
def baseEnd_3128341 : Nat := 1070895056111366723433685

theorem tailTrace_3128341 : CollatzResearch.WordTrace tailWord_3128341 prefixEnd_3128341 1070895056111366723433685 := by
  unfold tailWord_3128341
  simp only [CollatzResearch.WordTrace]
  refine ⟨114099969959562309951856877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76066646639708206634571251 114099969959562309951856877)
  ·
    refine ⟨42787488734835866231946329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114099969959562309951856877 42787488734835866231946329)
    ·
      refine ⟨32090616551126899673959747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42787488734835866231946329 32090616551126899673959747)
      ·
        refine ⟨48135924826690349510939621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32090616551126899673959747 48135924826690349510939621)
        ·
          refine ⟨9025485905004440533301179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48135924826690349510939621 9025485905004440533301179)
          ·
            refine ⟨13538228857506660799951769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9025485905004440533301179 13538228857506660799951769)
            ·
              refine ⟨10153671643129995599963827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13538228857506660799951769 10153671643129995599963827)
              ·
                refine ⟨15230507464694993399945741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10153671643129995599963827 15230507464694993399945741)
                ·
                  refine ⟨5711440299260622524979653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15230507464694993399945741 5711440299260622524979653)
                  ·
                    refine ⟨1070895056111366723433685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5711440299260622524979653 1070895056111366723433685)
                    ·
                      rfl

theorem cell22_3128341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_3128341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128341 prefixEnd_3128341 := by exact prefixLift 3128341
  have htrace : WordTrace (prefixWord ++ tailWord_3128341) baseStart_3128341 baseEnd_3128341 := by
    simpa [prefixWord, tailWord_3128341, baseEnd_3128341] using wordTrace_append hprefix tailTrace_3128341
  have hstable : (prefixWord ++ tailWord_3128341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128341).length < 2 ^ (prefixWord ++ tailWord_3128341).sum := by decide
  have hdescent : baseEnd_3128341 < baseStart_3128341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128384 : List Nat := [2, 1, 1, 2, 2, 3, 2, 9]
def baseStart_3128384 : Nat := 118140960795 + 3128384 * 2 ^ 59
def prefixEnd_3128384 : Nat := 4983230072969 + 3 ^ 40 * 3128384 * 2
def baseEnd_3128384 : Nat := 118989975098903216067617

theorem tailTrace_3128384 : CollatzResearch.WordTrace tailWord_3128384 prefixEnd_3128384 118989975098903216067617 := by
  unfold tailWord_3128384
  simp only [CollatzResearch.WordTrace]
  refine ⟨57050769149203264147836103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76067692198937685530448137 57050769149203264147836103)
  ·
    refine ⟨85576153723804896221754155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57050769149203264147836103 85576153723804896221754155)
    ·
      refine ⟨128364230585707344332631233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85576153723804896221754155 128364230585707344332631233)
      ·
        refine ⟨96273172939280508249473425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128364230585707344332631233 96273172939280508249473425)
        ·
          refine ⟨72204879704460381187105069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96273172939280508249473425 72204879704460381187105069)
          ·
            refine ⟨27076829889172642945164401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72204879704460381187105069 27076829889172642945164401)
            ·
              refine ⟨20307622416879482208873301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27076829889172642945164401 20307622416879482208873301)
              ·
                refine ⟨118989975098903216067617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20307622416879482208873301 118989975098903216067617)
                ·
                  rfl

theorem cell22_3128384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 9].length) (baseStart_3128384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128384 prefixEnd_3128384 := by exact prefixLift 3128384
  have htrace : WordTrace (prefixWord ++ tailWord_3128384) baseStart_3128384 baseEnd_3128384 := by
    simpa [prefixWord, tailWord_3128384, baseEnd_3128384] using wordTrace_append hprefix tailTrace_3128384
  have hstable : (prefixWord ++ tailWord_3128384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128384).length < 2 ^ (prefixWord ++ tailWord_3128384).sum := by decide
  have hdescent : baseEnd_3128384 < baseStart_3128384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128401 : List Nat := [1, 2, 2, 1, 3, 1, 6, 6]
def baseStart_3128401 : Nat := 118140960795 + 3128401 * 2 ^ 59
def prefixEnd_3128401 : Nat := 4983230072969 + 3 ^ 40 * 3128401 * 2
def baseEnd_3128401 : Nat := 118990621704171840770389

theorem tailTrace_3128401 : CollatzResearch.WordTrace tailWord_3128401 prefixEnd_3128401 118990621704171840770389 := by
  unfold tailWord_3128401
  simp only [CollatzResearch.WordTrace]
  refine ⟨114102158339344940199041057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76068105559563293466027371 114102158339344940199041057)
  ·
    refine ⟨85576618754508705149280793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114102158339344940199041057 85576618754508705149280793)
    ·
      refine ⟨64182464065881528861960595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85576618754508705149280793 64182464065881528861960595)
      ·
        refine ⟨96273696098822293292940893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64182464065881528861960595 96273696098822293292940893)
        ·
          refine ⟨36102636037058359984852835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96273696098822293292940893 36102636037058359984852835)
          ·
            refine ⟨54153954055587539977279253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36102636037058359984852835 54153954055587539977279253)
            ·
              refine ⟨2538466596355665936434965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54153954055587539977279253 2538466596355665936434965)
              ·
                refine ⟨118990621704171840770389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2538466596355665936434965 118990621704171840770389)
                ·
                  rfl

theorem cell22_3128401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 6].length) (baseStart_3128401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128401 prefixEnd_3128401 := by exact prefixLift 3128401
  have htrace : WordTrace (prefixWord ++ tailWord_3128401) baseStart_3128401 baseEnd_3128401 := by
    simpa [prefixWord, tailWord_3128401, baseEnd_3128401] using wordTrace_append hprefix tailTrace_3128401
  have hstable : (prefixWord ++ tailWord_3128401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128401).length < 2 ^ (prefixWord ++ tailWord_3128401).sum := by decide
  have hdescent : baseEnd_3128401 < baseStart_3128401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128418 : List Nat := [3, 3, 2, 2, 1, 3, 8]
def baseStart_3128418 : Nat := 118140960795 + 3128418 * 2 ^ 59
def prefixEnd_3128418 : Nat := 4983230072969 + 3 ^ 40 * 3128418 * 2
def baseEnd_3128418 : Nat := 39663756103146821824387

theorem tailTrace_3128418 : CollatzResearch.WordTrace tailWord_3128418 prefixEnd_3128418 39663756103146821824387 := by
  unfold tailWord_3128418
  simp only [CollatzResearch.WordTrace]
  refine ⟨28525694595070838025602477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76068518920188901401606605 28525694595070838025602477)
  ·
    refine ⟨10697135473151564259600929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28525694595070838025602477 10697135473151564259600929)
    ·
      refine ⟨8022851604863673194700697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10697135473151564259600929 8022851604863673194700697)
      ·
        refine ⟨6017138703647754896025523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8022851604863673194700697 6017138703647754896025523)
        ·
          refine ⟨9025708055471632344038285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6017138703647754896025523 9025708055471632344038285)
          ·
            refine ⟨3384640520801862129014357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9025708055471632344038285 3384640520801862129014357)
            ·
              refine ⟨39663756103146821824387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3384640520801862129014357 39663756103146821824387)
              ·
                rfl

theorem cell22_3128418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 8].length) (baseStart_3128418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128418 prefixEnd_3128418 := by exact prefixLift 3128418
  have htrace : WordTrace (prefixWord ++ tailWord_3128418) baseStart_3128418 baseEnd_3128418 := by
    simpa [prefixWord, tailWord_3128418, baseEnd_3128418] using wordTrace_append hprefix tailTrace_3128418
  have hstable : (prefixWord ++ tailWord_3128418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128418).length < 2 ^ (prefixWord ++ tailWord_3128418).sum := by decide
  have hdescent : baseEnd_3128418 < baseStart_3128418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128484 : List Nat := [2, 3, 1, 2, 3, 3, 2, 2, 1, 3]
def baseStart_3128484 : Nat := 118140960795 + 3128484 * 2 ^ 59
def prefixEnd_3128484 : Nat := 4983230072969 + 3 ^ 40 * 3128484 * 2
def baseEnd_3128484 : Nat := 1070944007933762017108247

theorem tailTrace_3128484 : CollatzResearch.WordTrace tailWord_3128484 prefixEnd_3128484 1070944007933762017108247 := by
  unfold tailWord_3128484
  simp only [CollatzResearch.WordTrace]
  refine ⟨57052592799022122687156253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76070123732029496916208337 57052592799022122687156253)
  ·
    refine ⟨21394722299633296007683595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57052592799022122687156253 21394722299633296007683595)
    ·
      refine ⟨32092083449449944011525393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21394722299633296007683595 32092083449449944011525393)
      ·
        refine ⟨24069062587087458008644045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32092083449449944011525393 24069062587087458008644045)
        ·
          refine ⟨9025898470157796753241517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24069062587087458008644045 9025898470157796753241517)
          ·
            refine ⟨3384711926309173782465569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9025898470157796753241517 3384711926309173782465569)
            ·
              refine ⟨2538533944731880336849177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3384711926309173782465569 2538533944731880336849177)
              ·
                refine ⟨1903900458548910252636883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2538533944731880336849177 1903900458548910252636883)
                ·
                  refine ⟨2855850687823365378955325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903900458548910252636883 2855850687823365378955325)
                  ·
                    refine ⟨1070944007933762017108247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2855850687823365378955325 1070944007933762017108247)
                    ·
                      rfl

theorem cell22_3128484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_3128484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128484 prefixEnd_3128484 := by exact prefixLift 3128484
  have htrace : WordTrace (prefixWord ++ tailWord_3128484) baseStart_3128484 baseEnd_3128484 := by
    simpa [prefixWord, tailWord_3128484, baseEnd_3128484] using wordTrace_append hprefix tailTrace_3128484
  have hstable : (prefixWord ++ tailWord_3128484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128484).length < 2 ^ (prefixWord ++ tailWord_3128484).sum := by decide
  have hdescent : baseEnd_3128484 < baseStart_3128484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128508 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 6]
def baseStart_3128508 : Nat := 118140960795 + 3128508 * 2 ^ 59
def prefixEnd_3128508 : Nat := 4983230072969 + 3 ^ 40 * 3128508 * 2
def baseEnd_3128508 : Nat := 356984074541411318169391

theorem tailTrace_3128508 : CollatzResearch.WordTrace tailWord_3128508 prefixEnd_3128508 356984074541411318169391 := by
  unfold tailWord_3128508
  simp only [CollatzResearch.WordTrace]
  refine ⟨57053030474978648736593089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76070707299971531648790785 57053030474978648736593089)
  ·
    refine ⟨42789772856233986552444817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57053030474978648736593089 42789772856233986552444817)
    ·
      refine ⟨32092329642175489914333613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42789772856233986552444817 32092329642175489914333613)
      ·
        refine ⟨12034623615815808717875105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32092329642175489914333613 12034623615815808717875105)
        ·
          refine ⟨9025967711861856538406329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12034623615815808717875105 9025967711861856538406329)
          ·
            refine ⟨6769475783896392403804747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9025967711861856538406329 6769475783896392403804747)
            ·
              refine ⟨10154213675844588605707121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6769475783896392403804747 10154213675844588605707121)
              ·
                refine ⟨7615660256883441454280341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10154213675844588605707121 7615660256883441454280341)
                ·
                  refine ⟨356984074541411318169391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7615660256883441454280341 356984074541411318169391)
                  ·
                    rfl

theorem cell22_3128508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_3128508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128508 prefixEnd_3128508 := by exact prefixLift 3128508
  have htrace : WordTrace (prefixWord ++ tailWord_3128508) baseStart_3128508 baseEnd_3128508 := by
    simpa [prefixWord, tailWord_3128508, baseEnd_3128508] using wordTrace_append hprefix tailTrace_3128508
  have hstable : (prefixWord ++ tailWord_3128508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128508).length < 2 ^ (prefixWord ++ tailWord_3128508).sum := by decide
  have hdescent : baseEnd_3128508 < baseStart_3128508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128518 : List Nat := [6, 1, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3128518 : Nat := 118140960795 + 3128518 * 2 ^ 59
def prefixEnd_3128518 : Nat := 4983230072969 + 3 ^ 40 * 3128518 * 2
def baseEnd_3128518 : Nat := 1070955646828597261758143

theorem tailTrace_3128518 : CollatzResearch.WordTrace tailWord_3128518 prefixEnd_3128518 1070955646828597261758143 := by
  unfold tailWord_3128518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3565825802497533411907819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76070950453280712787366805 3565825802497533411907819)
  ·
    refine ⟨5348738703746300117861729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3565825802497533411907819 5348738703746300117861729)
    ·
      refine ⟨4011554027809725088396297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5348738703746300117861729 4011554027809725088396297)
      ·
        refine ⟨3008665520857293816297223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4011554027809725088396297 3008665520857293816297223)
        ·
          refine ⟨4512998281285940724445835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3008665520857293816297223 4512998281285940724445835)
          ·
            refine ⟨6769497421928911086668753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4512998281285940724445835 6769497421928911086668753)
            ·
              refine ⟨5077123066446683315001565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6769497421928911086668753 5077123066446683315001565)
              ·
                refine ⟨1903921149917506243125587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5077123066446683315001565 1903921149917506243125587)
                ·
                  refine ⟨2855881724876259364688381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903921149917506243125587 2855881724876259364688381)
                  ·
                    refine ⟨1070955646828597261758143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2855881724876259364688381 1070955646828597261758143)
                    ·
                      rfl

theorem cell22_3128518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3128518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128518 prefixEnd_3128518 := by exact prefixLift 3128518
  have htrace : WordTrace (prefixWord ++ tailWord_3128518) baseStart_3128518 baseEnd_3128518 := by
    simpa [prefixWord, tailWord_3128518, baseEnd_3128518] using wordTrace_append hprefix tailTrace_3128518
  have hstable : (prefixWord ++ tailWord_3128518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128518).length < 2 ^ (prefixWord ++ tailWord_3128518).sum := by decide
  have hdescent : baseEnd_3128518 < baseStart_3128518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128581 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 9]
def baseStart_3128581 : Nat := 118140960795 + 3128581 * 2 ^ 59
def prefixEnd_3128581 : Nat := 4983230072969 + 3 ^ 40 * 3128581 * 2
def baseEnd_3128581 : Nat := 356992404338695365810983

theorem tailTrace_3128581 : CollatzResearch.WordTrace tailWord_3128581 prefixEnd_3128581 356992404338695365810983 := by
  unfold tailWord_3128581
  simp only [CollatzResearch.WordTrace]
  refine ⟨114108723478692830940593597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76072482319128553960395731 114108723478692830940593597)
  ·
    refine ⟨42790771304509811602722599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114108723478692830940593597 42790771304509811602722599)
    ·
      refine ⟨64186156956764717404083899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42790771304509811602722599 64186156956764717404083899)
      ·
        refine ⟨96279235435147076106125849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64186156956764717404083899 96279235435147076106125849)
        ·
          refine ⟨72209426576360307079594387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96279235435147076106125849 72209426576360307079594387)
          ·
            refine ⟨108314139864540460619391581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72209426576360307079594387 108314139864540460619391581)
            ·
              refine ⟨40617802449202672732271843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108314139864540460619391581 40617802449202672732271843)
              ·
                refine ⟨60926703673804009098407765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40617802449202672732271843 60926703673804009098407765)
                ·
                  refine ⟨356992404338695365810983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60926703673804009098407765 356992404338695365810983)
                  ·
                    rfl

theorem cell22_3128581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_3128581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128581 prefixEnd_3128581 := by exact prefixLift 3128581
  have htrace : WordTrace (prefixWord ++ tailWord_3128581) baseStart_3128581 baseEnd_3128581 := by
    simpa [prefixWord, tailWord_3128581, baseEnd_3128581] using wordTrace_append hprefix tailTrace_3128581
  have hstable : (prefixWord ++ tailWord_3128581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128581).length < 2 ^ (prefixWord ++ tailWord_3128581).sum := by decide
  have hdescent : baseEnd_3128581 < baseStart_3128581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128602 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 3, 3]
def baseStart_3128602 : Nat := 118140960795 + 3128602 * 2 ^ 59
def prefixEnd_3128602 : Nat := 4983230072969 + 3 ^ 40 * 3128602 * 2
def baseEnd_3128602 : Nat := 1070984401745249042657885

theorem tailTrace_3128602 : CollatzResearch.WordTrace tailWord_3128602 prefixEnd_3128602 1070984401745249042657885 := by
  unfold tailWord_3128602
  simp only [CollatzResearch.WordTrace]
  refine ⟨28527372352904187881777015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76072992941077834351405373 28527372352904187881777015)
  ·
    refine ⟨42791058529356281822665523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28527372352904187881777015 42791058529356281822665523)
    ·
      refine ⟨64186587794034422733998285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42791058529356281822665523 64186587794034422733998285)
      ·
        refine ⟨24069970422762908525249357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64186587794034422733998285 24069970422762908525249357)
        ·
          refine ⟨9026238908536090696968509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24069970422762908525249357 9026238908536090696968509)
          ·
            refine ⟨3384839590701034011363191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9026238908536090696968509 3384839590701034011363191)
            ·
              refine ⟨5077259386051551017044787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3384839590701034011363191 5077259386051551017044787)
              ·
                refine ⟨7615889079077326525567181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5077259386051551017044787 7615889079077326525567181)
                ·
                  refine ⟨2855958404653997447087693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7615889079077326525567181 2855958404653997447087693)
                  ·
                    refine ⟨1070984401745249042657885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2855958404653997447087693 1070984401745249042657885)
                    ·
                      rfl

theorem cell22_3128602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_3128602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128602 prefixEnd_3128602 := by exact prefixLift 3128602
  have htrace : WordTrace (prefixWord ++ tailWord_3128602) baseStart_3128602 baseEnd_3128602 := by
    simpa [prefixWord, tailWord_3128602, baseEnd_3128602] using wordTrace_append hprefix tailTrace_3128602
  have hstable : (prefixWord ++ tailWord_3128602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128602).length < 2 ^ (prefixWord ++ tailWord_3128602).sum := by decide
  have hdescent : baseEnd_3128602 < baseStart_3128602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128658 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_3128658 : Nat := 118140960795 + 3128658 * 2 ^ 59
def prefixEnd_3128658 : Nat := 4983230072969 + 3 ^ 40 * 3128658 * 2
def baseEnd_3128658 : Nat := 1071003571689683563257713

theorem tailTrace_3128658 : CollatzResearch.WordTrace tailWord_3128658 prefixEnd_3128658 1071003571689683563257713 := by
  unfold tailWord_3128658
  simp only [CollatzResearch.WordTrace]
  refine ⟨28527882974853468272786657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76074354599609248727431085 28527882974853468272786657)
  ·
    refine ⟨21395912231140101204589993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28527882974853468272786657 21395912231140101204589993)
    ·
      refine ⟨16046934173355075903442495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21395912231140101204589993 16046934173355075903442495)
      ·
        refine ⟨24070401260032613855163743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16046934173355075903442495 24070401260032613855163743)
        ·
          refine ⟨36105601890048920782745615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24070401260032613855163743 36105601890048920782745615)
          ·
            refine ⟨54158402835073381174118423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36105601890048920782745615 54158402835073381174118423)
            ·
              refine ⟨81237604252610071761177635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54158402835073381174118423 81237604252610071761177635)
              ·
                refine ⟨121856406378915107641766453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81237604252610071761177635 121856406378915107641766453)
                ·
                  refine ⟨11424038098023291341415605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121856406378915107641766453 11424038098023291341415605)
                  ·
                    refine ⟨1071003571689683563257713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11424038098023291341415605 1071003571689683563257713)
                    ·
                      rfl

theorem cell22_3128658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_3128658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128658 prefixEnd_3128658 := by exact prefixLift 3128658
  have htrace : WordTrace (prefixWord ++ tailWord_3128658) baseStart_3128658 baseEnd_3128658 := by
    simpa [prefixWord, tailWord_3128658, baseEnd_3128658] using wordTrace_append hprefix tailTrace_3128658
  have hstable : (prefixWord ++ tailWord_3128658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128658).length < 2 ^ (prefixWord ++ tailWord_3128658).sum := by decide
  have hdescent : baseEnd_3128658 < baseStart_3128658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128673 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 4, 4]
def baseStart_3128673 : Nat := 118140960795 + 3128673 * 2 ^ 59
def prefixEnd_3128673 : Nat := 4983230072969 + 3 ^ 40 * 3128673 * 2
def baseEnd_3128673 : Nat := 1071008706496228524132667

theorem tailTrace_3128673 : CollatzResearch.WordTrace tailWord_3128673 prefixEnd_3128673 1071008706496228524132667 := by
  unfold tailWord_3128673
  simp only [CollatzResearch.WordTrace]
  refine ⟨114112078994359530652942673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76074719329573020435295115 114112078994359530652942673)
  ·
    refine ⟨85584059245769647989707005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114112078994359530652942673 85584059245769647989707005)
    ·
      refine ⟨32094022217163617996140127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85584059245769647989707005 32094022217163617996140127)
      ·
        refine ⟨48141033325745426994210191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32094022217163617996140127 48141033325745426994210191)
        ·
          refine ⟨72211549988618140491315287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48141033325745426994210191 72211549988618140491315287)
          ·
            refine ⟨108317324982927210736972931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72211549988618140491315287 108317324982927210736972931)
            ·
              refine ⟨162475987474390816105459397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108317324982927210736972931 162475987474390816105459397)
              ·
                refine ⟨30464247651448278019773637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162475987474390816105459397 30464247651448278019773637)
                ·
                  refine ⟨5712046434646552128707557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30464247651448278019773637 5712046434646552128707557)
                  ·
                    refine ⟨1071008706496228524132667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5712046434646552128707557 1071008706496228524132667)
                    ·
                      rfl

theorem cell22_3128673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_3128673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128673 prefixEnd_3128673 := by exact prefixLift 3128673
  have htrace : WordTrace (prefixWord ++ tailWord_3128673) baseStart_3128673 baseEnd_3128673 := by
    simpa [prefixWord, tailWord_3128673, baseEnd_3128673] using wordTrace_append hprefix tailTrace_3128673
  have hstable : (prefixWord ++ tailWord_3128673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128673).length < 2 ^ (prefixWord ++ tailWord_3128673).sum := by decide
  have hdescent : baseEnd_3128673 < baseStart_3128673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128675 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 1, 5]
def baseStart_3128675 : Nat := 118140960795 + 3128675 * 2 ^ 59
def prefixEnd_3128675 : Nat := 4983230072969 + 3 ^ 40 * 3128675 * 2
def baseEnd_3128675 : Nat := 1071009391137101185582661

theorem tailTrace_3128675 : CollatzResearch.WordTrace tailWord_3128675 prefixEnd_3128675 1071009391137101185582661 := by
  unfold tailWord_3128675
  simp only [CollatzResearch.WordTrace]
  refine ⟨114112151940352284994515479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76074767960234856663010319 114112151940352284994515479)
  ·
    refine ⟨171168227910528427491773219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114112151940352284994515479 171168227910528427491773219)
    ·
      refine ⟨256752341865792641237659829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171168227910528427491773219 256752341865792641237659829)
      ·
        refine ⟨24070532049918060116030609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 256752341865792641237659829 24070532049918060116030609)
        ·
          refine ⟨18052899037438545087022957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24070532049918060116030609 18052899037438545087022957)
          ·
            refine ⟨6769837139039454407633609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18052899037438545087022957 6769837139039454407633609)
            ·
              refine ⟨5077377854279590805725207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6769837139039454407633609 5077377854279590805725207)
              ·
                refine ⟨7616066781419386208587811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5077377854279590805725207 7616066781419386208587811)
                ·
                  refine ⟨11424100172129079312881717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7616066781419386208587811 11424100172129079312881717)
                  ·
                    refine ⟨1071009391137101185582661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11424100172129079312881717 1071009391137101185582661)
                    ·
                      rfl

theorem cell22_3128675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 5].length) (baseStart_3128675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128675 prefixEnd_3128675 := by exact prefixLift 3128675
  have htrace : WordTrace (prefixWord ++ tailWord_3128675) baseStart_3128675 baseEnd_3128675 := by
    simpa [prefixWord, tailWord_3128675, baseEnd_3128675] using wordTrace_append hprefix tailTrace_3128675
  have hstable : (prefixWord ++ tailWord_3128675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128675).length < 2 ^ (prefixWord ++ tailWord_3128675).sum := by decide
  have hdescent : baseEnd_3128675 < baseStart_3128675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128705 : List Nat := [1, 2, 4, 3, 2, 1, 9]
def baseStart_3128705 : Nat := 118140960795 + 3128705 * 2 ^ 59
def prefixEnd_3128705 : Nat := 4983230072969 + 3 ^ 40 * 3128705 * 2
def baseEnd_3128705 : Nat := 39667394842599670641947

theorem tailTrace_3128705 : CollatzResearch.WordTrace tailWord_3128705 prefixEnd_3128705 39667394842599670641947 := by
  unfold tailWord_3128705
  simp only [CollatzResearch.WordTrace]
  refine ⟨114113246130243600118107569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76075497420162400078738379 114113246130243600118107569)
  ·
    refine ⟨85584934597682700088580677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114113246130243600118107569 85584934597682700088580677)
    ·
      refine ⟨16047175237065506266608877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85584934597682700088580677 16047175237065506266608877)
      ·
        refine ⟨6017690713899564849978329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16047175237065506266608877 6017690713899564849978329)
        ·
          refine ⟨4513268035424673637483747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6017690713899564849978329 4513268035424673637483747)
          ·
            refine ⟨6769902053137010456225621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4513268035424673637483747 6769902053137010456225621)
            ·
              refine ⟨39667394842599670641947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6769902053137010456225621 39667394842599670641947)
              ·
                rfl

theorem cell22_3128705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 9].length) (baseStart_3128705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128705 prefixEnd_3128705 := by exact prefixLift 3128705
  have htrace : WordTrace (prefixWord ++ tailWord_3128705) baseStart_3128705 baseEnd_3128705 := by
    simpa [prefixWord, tailWord_3128705, baseEnd_3128705] using wordTrace_append hprefix tailTrace_3128705
  have hstable : (prefixWord ++ tailWord_3128705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128705).length < 2 ^ (prefixWord ++ tailWord_3128705).sum := by decide
  have hdescent : baseEnd_3128705 < baseStart_3128705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128748 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 1, 7]
def baseStart_3128748 : Nat := 118140960795 + 3128748 * 2 ^ 59
def prefixEnd_3128748 : Nat := 4983230072969 + 3 ^ 40 * 3128748 * 2
def baseEnd_3128748 : Nat := 1071034380528953328507437

theorem tailTrace_3128748 : CollatzResearch.WordTrace tailWord_3128748 prefixEnd_3128748 1071034380528953328507437 := by
  unfold tailWord_3128748
  simp only [CollatzResearch.WordTrace]
  refine ⟨57057407234543909230961449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76076542979391878974615265 57057407234543909230961449)
  ·
    refine ⟨42793055425907931923221087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57057407234543909230961449 42793055425907931923221087)
    ·
      refine ⟨64189583138861897884831631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42793055425907931923221087 64189583138861897884831631)
      ·
        refine ⟨96284374708292846827247447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64189583138861897884831631 96284374708292846827247447)
        ·
          refine ⟨144426562062439270240871171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96284374708292846827247447 144426562062439270240871171)
          ·
            refine ⟨216639843093658905361306757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144426562062439270240871171 216639843093658905361306757)
            ·
              refine ⟨40619970580061044755245017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216639843093658905361306757 40619970580061044755245017)
              ·
                refine ⟨30464977935045783566433763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40619970580061044755245017 30464977935045783566433763)
                ·
                  refine ⟨45697466902568675349650645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30464977935045783566433763 45697466902568675349650645)
                  ·
                    refine ⟨1071034380528953328507437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45697466902568675349650645 1071034380528953328507437)
                    ·
                      rfl

theorem cell22_3128748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_3128748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128748 prefixEnd_3128748 := by exact prefixLift 3128748
  have htrace : WordTrace (prefixWord ++ tailWord_3128748) baseStart_3128748 baseEnd_3128748 := by
    simpa [prefixWord, tailWord_3128748, baseEnd_3128748] using wordTrace_append hprefix tailTrace_3128748
  have hstable : (prefixWord ++ tailWord_3128748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128748).length < 2 ^ (prefixWord ++ tailWord_3128748).sum := by decide
  have hdescent : baseEnd_3128748 < baseStart_3128748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128797 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_3128797 : Nat := 118140960795 + 3128797 * 2 ^ 59
def prefixEnd_3128797 : Nat := 4983230072969 + 3 ^ 40 * 3128797 * 2
def baseEnd_3128797 : Nat := 1071051154230333534032287

theorem tailTrace_3128797 : CollatzResearch.WordTrace tailWord_3128797 prefixEnd_3128797 1071051154230333534032287 := by
  unfold tailWord_3128797
  simp only [CollatzResearch.WordTrace]
  refine ⟨114116601645910299830456645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76077734430606866553637763 114116601645910299830456645)
  ·
    refine ⟨21396862808608181218210621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114116601645910299830456645 21396862808608181218210621)
    ·
      refine ⟨8023823553228067956828983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21396862808608181218210621 8023823553228067956828983)
      ·
        refine ⟨12035735329842101935243475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8023823553228067956828983 12035735329842101935243475)
        ·
          refine ⟨18053602994763152902865213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12035735329842101935243475 18053602994763152902865213)
          ·
            refine ⟨6770101123036182338574455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18053602994763152902865213 6770101123036182338574455)
            ·
              refine ⟨10155151684554273507861683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6770101123036182338574455 10155151684554273507861683)
              ·
                refine ⟨15232727526831410261792525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10155151684554273507861683 15232727526831410261792525)
                ·
                  refine ⟨5712272822561778848172197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15232727526831410261792525 5712272822561778848172197)
                  ·
                    refine ⟨1071051154230333534032287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5712272822561778848172197 1071051154230333534032287)
                    ·
                      rfl

theorem cell22_3128797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_3128797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128797 prefixEnd_3128797 := by exact prefixLift 3128797
  have htrace : WordTrace (prefixWord ++ tailWord_3128797) baseStart_3128797 baseEnd_3128797 := by
    simpa [prefixWord, tailWord_3128797, baseEnd_3128797] using wordTrace_append hprefix tailTrace_3128797
  have hstable : (prefixWord ++ tailWord_3128797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128797).length < 2 ^ (prefixWord ++ tailWord_3128797).sum := by decide
  have hdescent : baseEnd_3128797 < baseStart_3128797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128814 : List Nat := [4, 1, 2, 1, 2, 1, 5, 1, 1, 4]
def baseStart_3128814 : Nat := 118140960795 + 3128814 * 2 ^ 59
def prefixEnd_3128814 : Nat := 4983230072969 + 3 ^ 40 * 3128814 * 2
def baseEnd_3128814 : Nat := 1071056973677751156357235

theorem tailTrace_3128814 : CollatzResearch.WordTrace tailWord_3128814 prefixEnd_3128814 1071056973677751156357235 := by
  unfold tailWord_3128814
  simp only [CollatzResearch.WordTrace]
  refine ⟨14264652710856088966728187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76078147791232474489216997 14264652710856088966728187)
  ·
    refine ⟨21396979066284133450092281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14264652710856088966728187 21396979066284133450092281)
    ·
      refine ⟨16047734299713100087569211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21396979066284133450092281 16047734299713100087569211)
      ·
        refine ⟨24071601449569650131353817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16047734299713100087569211 24071601449569650131353817)
        ·
          refine ⟨18053701087177237598515363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24071601449569650131353817 18053701087177237598515363)
          ·
            refine ⟨27080551630765856397773045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18053701087177237598515363 27080551630765856397773045)
            ·
              refine ⟨2538801715384299037291223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27080551630765856397773045 2538801715384299037291223)
              ·
                refine ⟨3808202573076448555936835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2538801715384299037291223 3808202573076448555936835)
                ·
                  refine ⟨5712303859614672833905253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3808202573076448555936835 5712303859614672833905253)
                  ·
                    refine ⟨1071056973677751156357235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5712303859614672833905253 1071056973677751156357235)
                    ·
                      rfl

theorem cell22_3128814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_3128814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128814 prefixEnd_3128814 := by exact prefixLift 3128814
  have htrace : WordTrace (prefixWord ++ tailWord_3128814) baseStart_3128814 baseEnd_3128814 := by
    simpa [prefixWord, tailWord_3128814, baseEnd_3128814] using wordTrace_append hprefix tailTrace_3128814
  have hstable : (prefixWord ++ tailWord_3128814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128814).length < 2 ^ (prefixWord ++ tailWord_3128814).sum := by decide
  have hdescent : baseEnd_3128814 < baseStart_3128814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128829 : List Nat := [1, 4, 1, 1, 1, 4, 4, 2, 4]
def baseStart_3128829 : Nat := 118140960795 + 3128829 * 2 ^ 59
def prefixEnd_3128829 : Nat := 4983230072969 + 3 ^ 40 * 3128829 * 2
def baseEnd_3128829 : Nat := 357020702828098705744063

theorem tailTrace_3128829 : CollatzResearch.WordTrace tailWord_3128829 prefixEnd_3128829 357020702828098705744063 := by
  unfold tailWord_3128829
  simp only [CollatzResearch.WordTrace]
  refine ⟨114117768781794369295621541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76078512521196246197081027 114117768781794369295621541)
  ·
    refine ⟨21397081646586444242929039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114117768781794369295621541 21397081646586444242929039)
    ·
      refine ⟨32095622469879666364393559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21397081646586444242929039 32095622469879666364393559)
      ·
        refine ⟨48143433704819499546590339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32095622469879666364393559 48143433704819499546590339)
        ·
          refine ⟨72215150557229249319885509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48143433704819499546590339 72215150557229249319885509)
          ·
            refine ⟨13540340729480484247478533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72215150557229249319885509 13540340729480484247478533)
            ·
              refine ⟨2538813886777590796402225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13540340729480484247478533 2538813886777590796402225)
              ·
                refine ⟨1904110415083193097301669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2538813886777590796402225 1904110415083193097301669)
                ·
                  refine ⟨357020702828098705744063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1904110415083193097301669 357020702828098705744063)
                  ·
                    rfl

theorem cell22_3128829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_3128829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128829 prefixEnd_3128829 := by exact prefixLift 3128829
  have htrace : WordTrace (prefixWord ++ tailWord_3128829) baseStart_3128829 baseEnd_3128829 := by
    simpa [prefixWord, tailWord_3128829, baseEnd_3128829] using wordTrace_append hprefix tailTrace_3128829
  have hstable : (prefixWord ++ tailWord_3128829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128829).length < 2 ^ (prefixWord ++ tailWord_3128829).sum := by decide
  have hdescent : baseEnd_3128829 < baseStart_3128829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128840 : List Nat := [2, 1, 3, 2, 1, 1, 5, 7]
def baseStart_3128840 : Nat := 118140960795 + 3128840 * 2 ^ 59
def prefixEnd_3128840 : Nat := 4983230072969 + 3 ^ 40 * 3128840 * 2
def baseEnd_3128840 : Nat := 119007319334343972800795

theorem tailTrace_3128840 : CollatzResearch.WordTrace tailWord_3128840 prefixEnd_3128840 119007319334343972800795 := by
  unfold tailWord_3128840
  simp only [CollatzResearch.WordTrace]
  refine ⟨57059084992377259087135987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76078779989836345449514649 57059084992377259087135987)
  ·
    refine ⟨85588627488565888630703981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57059084992377259087135987 85588627488565888630703981)
    ·
      refine ⟨32095735308212208236513993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85588627488565888630703981 32095735308212208236513993)
      ·
        refine ⟨24071801481159156177385495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32095735308212208236513993 24071801481159156177385495)
        ·
          refine ⟨36107702221738734266078243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24071801481159156177385495 36107702221738734266078243)
          ·
            refine ⟨54161553332608101399117365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36107702221738734266078243 54161553332608101399117365)
            ·
              refine ⟨5077645624932009506167253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54161553332608101399117365 5077645624932009506167253)
              ·
                refine ⟨119007319334343972800795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5077645624932009506167253 119007319334343972800795)
                ·
                  rfl

theorem cell22_3128840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 7].length) (baseStart_3128840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128840 prefixEnd_3128840 := by exact prefixLift 3128840
  have htrace : WordTrace (prefixWord ++ tailWord_3128840) baseStart_3128840 baseEnd_3128840 := by
    simpa [prefixWord, tailWord_3128840, baseEnd_3128840] using wordTrace_append hprefix tailTrace_3128840
  have hstable : (prefixWord ++ tailWord_3128840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128840).length < 2 ^ (prefixWord ++ tailWord_3128840).sum := by decide
  have hdescent : baseEnd_3128840 < baseStart_3128840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128889 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 3, 3]
def baseStart_3128889 : Nat := 118140960795 + 3128889 * 2 ^ 59
def prefixEnd_3128889 : Nat := 4983230072969 + 3 ^ 40 * 3128889 * 2
def baseEnd_3128889 : Nat := 1071082647710475960732005

theorem tailTrace_3128889 : CollatzResearch.WordTrace tailWord_3128889 prefixEnd_3128889 1071082647710475960732005 := by
  unfold tailWord_3128889
  simp only [CollatzResearch.WordTrace]
  refine ⟨114119957161576999542805721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76079971441051333028537147 114119957161576999542805721)
  ·
    refine ⟨85589967871182749657104291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114119957161576999542805721 85589967871182749657104291)
    ·
      refine ⟨128384951806774124485656437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85589967871182749657104291 128384951806774124485656437)
      ·
        refine ⟨12036089231885074170530291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128384951806774124485656437 12036089231885074170530291)
        ·
          refine ⟨18054133847827611255795437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12036089231885074170530291 18054133847827611255795437)
          ·
            refine ⟨6770300192935354220923289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18054133847827611255795437 6770300192935354220923289)
            ·
              refine ⟨5077725144701515665692467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6770300192935354220923289 5077725144701515665692467)
              ·
                refine ⟨7616587717052273498538701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5077725144701515665692467 7616587717052273498538701)
                ·
                  refine ⟨2856220393894602561952013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7616587717052273498538701 2856220393894602561952013)
                  ·
                    refine ⟨1071082647710475960732005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2856220393894602561952013 1071082647710475960732005)
                    ·
                      rfl

theorem cell22_3128889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 3].length) (baseStart_3128889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128889 prefixEnd_3128889 := by exact prefixLift 3128889
  have htrace : WordTrace (prefixWord ++ tailWord_3128889) baseStart_3128889 baseEnd_3128889 := by
    simpa [prefixWord, tailWord_3128889, baseEnd_3128889] using wordTrace_append hprefix tailTrace_3128889
  have hstable : (prefixWord ++ tailWord_3128889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128889).length < 2 ^ (prefixWord ++ tailWord_3128889).sum := by decide
  have hdescent : baseEnd_3128889 < baseStart_3128889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3128996 : List Nat := [2, 3, 1, 2, 2, 3, 2, 2, 2, 3]
def baseStart_3128996 : Nat := 118140960795 + 3128996 * 2 ^ 59
def prefixEnd_3128996 : Nat := 4983230072969 + 3 ^ 40 * 3128996 * 2
def baseEnd_3128996 : Nat := 1071119275997163348306677

theorem tailTrace_3128996 : CollatzResearch.WordTrace tailWord_3128996 prefixEnd_3128996 1071119275997163348306677 := by
  unfold tailWord_3128996
  simp only [CollatzResearch.WordTrace]
  refine ⟨57061929886094678408475421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76082573181459571211300561 57061929886094678408475421)
  ·
    refine ⟨21398223707285504403178283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57061929886094678408475421 21398223707285504403178283)
    ·
      refine ⟨32097335560928256604767425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21398223707285504403178283 32097335560928256604767425)
      ·
        refine ⟨24073001670696192453575569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32097335560928256604767425 24073001670696192453575569)
        ·
          refine ⟨18054751253022144340181677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24073001670696192453575569 18054751253022144340181677)
          ·
            refine ⟨6770531719883304127568129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18054751253022144340181677 6770531719883304127568129)
            ·
              refine ⟨5077898789912478095676097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6770531719883304127568129 5077898789912478095676097)
              ·
                refine ⟨3808424092434358571757073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5077898789912478095676097 3808424092434358571757073)
                ·
                  refine ⟨2856318069325768928817805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3808424092434358571757073 2856318069325768928817805)
                  ·
                    refine ⟨1071119275997163348306677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2856318069325768928817805 1071119275997163348306677)
                    ·
                      rfl

theorem cell22_3128996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_3128996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3128996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3128996 prefixEnd_3128996 := by exact prefixLift 3128996
  have htrace : WordTrace (prefixWord ++ tailWord_3128996) baseStart_3128996 baseEnd_3128996 := by
    simpa [prefixWord, tailWord_3128996, baseEnd_3128996] using wordTrace_append hprefix tailTrace_3128996
  have hstable : (prefixWord ++ tailWord_3128996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3128996).length < 2 ^ (prefixWord ++ tailWord_3128996).sum := by decide
  have hdescent : baseEnd_3128996 < baseStart_3128996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3128996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129024 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 3, 3]
def baseStart_3129024 : Nat := 118140960795 + 3129024 * 2 ^ 59
def prefixEnd_3129024 : Nat := 4983230072969 + 3 ^ 40 * 3129024 * 2
def baseEnd_3129024 : Nat := 1071128860969380608606591

theorem tailTrace_3129024 : CollatzResearch.WordTrace tailWord_3129024 prefixEnd_3129024 1071128860969380608606591 := by
  unfold tailWord_3129024
  simp only [CollatzResearch.WordTrace]
  refine ⟨57062440508043958799485063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76083254010725278399313417 57062440508043958799485063)
  ·
    refine ⟨85593660762065938199227595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57062440508043958799485063 85593660762065938199227595)
    ·
      refine ⟨128390491143098907298841393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85593660762065938199227595 128390491143098907298841393)
      ·
        refine ⟨96292868357324180474131045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128390491143098907298841393 96292868357324180474131045)
        ·
          refine ⟨18054912816998283838899571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96292868357324180474131045 18054912816998283838899571)
          ·
            refine ⟨27082369225497425758349357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18054912816998283838899571 27082369225497425758349357)
            ·
              refine ⟨10155888459561534659381009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27082369225497425758349357 10155888459561534659381009)
              ·
                refine ⟨7616916344671150994535757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10155888459561534659381009 7616916344671150994535757)
                ·
                  refine ⟨2856343629251681622950909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7616916344671150994535757 2856343629251681622950909)
                  ·
                    refine ⟨1071128860969380608606591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2856343629251681622950909 1071128860969380608606591)
                    ·
                      rfl

theorem cell22_3129024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 3, 3].length) (baseStart_3129024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129024 prefixEnd_3129024 := by exact prefixLift 3129024
  have htrace : WordTrace (prefixWord ++ tailWord_3129024) baseStart_3129024 baseEnd_3129024 := by
    simpa [prefixWord, tailWord_3129024, baseEnd_3129024] using wordTrace_append hprefix tailTrace_3129024
  have hstable : (prefixWord ++ tailWord_3129024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129024).length < 2 ^ (prefixWord ++ tailWord_3129024).sum := by decide
  have hdescent : baseEnd_3129024 < baseStart_3129024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129041 : List Nat := [1, 2, 2, 1, 2, 4, 1, 5, 1, 3]
def baseStart_3129041 : Nat := 118140960795 + 3129041 * 2 ^ 59
def prefixEnd_3129041 : Nat := 4983230072969 + 3 ^ 40 * 3129041 * 2
def baseEnd_3129041 : Nat := 1071134680416798230931539

theorem tailTrace_3129041 : CollatzResearch.WordTrace tailWord_3129041 prefixEnd_3129041 1071134680416798230931539 := by
  unfold tailWord_3129041
  simp only [CollatzResearch.WordTrace]
  refine ⟨114125501057026329502338977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76083667371350886334892651 114125501057026329502338977)
  ·
    refine ⟨85594125792769747126754233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114125501057026329502338977 85594125792769747126754233)
    ·
      refine ⟨64195594344577310345065675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85594125792769747126754233 64195594344577310345065675)
      ·
        refine ⟨96293391516865965517598513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64195594344577310345065675 96293391516865965517598513)
        ·
          refine ⟨72220043637649474138198885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96293391516865965517598513 72220043637649474138198885)
          ·
            refine ⟨13541258182059276400912291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72220043637649474138198885 13541258182059276400912291)
            ·
              refine ⟨20311887273088914601368437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13541258182059276400912291 20311887273088914601368437)
              ·
                refine ⟨1904239431852085743878291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20311887273088914601368437 1904239431852085743878291)
                ·
                  refine ⟨2856359147778128615817437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1904239431852085743878291 2856359147778128615817437)
                  ·
                    refine ⟨1071134680416798230931539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2856359147778128615817437 1071134680416798230931539)
                    ·
                      rfl

theorem cell22_3129041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_3129041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129041 prefixEnd_3129041 := by exact prefixLift 3129041
  have htrace : WordTrace (prefixWord ++ tailWord_3129041) baseStart_3129041 baseEnd_3129041 := by
    simpa [prefixWord, tailWord_3129041, baseEnd_3129041] using wordTrace_append hprefix tailTrace_3129041
  have hstable : (prefixWord ++ tailWord_3129041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129041).length < 2 ^ (prefixWord ++ tailWord_3129041).sum := by decide
  have hdescent : baseEnd_3129041 < baseStart_3129041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129067 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 5, 4]
def baseStart_3129067 : Nat := 118140960795 + 3129067 * 2 ^ 59
def prefixEnd_3129067 : Nat := 4983230072969 + 3 ^ 40 * 3129067 * 2
def baseEnd_3129067 : Nat := 1071143580748142829781459

theorem tailTrace_3129067 : CollatzResearch.WordTrace tailWord_3129067 prefixEnd_3129067 1071143580748142829781459 := by
  unfold tailWord_3129067
  simp only [CollatzResearch.WordTrace]
  refine ⟨114126449354932135942785455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76084299569954757295190303 114126449354932135942785455)
  ·
    refine ⟨171189674032398203914178183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114126449354932135942785455 171189674032398203914178183)
    ·
      refine ⟨256784511048597305871267275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171189674032398203914178183 256784511048597305871267275)
      ·
        refine ⟨385176766572895958806900913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256784511048597305871267275 385176766572895958806900913)
        ·
          refine ⟨288882574929671969105175685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385176766572895958806900913 288882574929671969105175685)
          ·
            refine ⟨54165482799313494207220441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 288882574929671969105175685 54165482799313494207220441)
            ·
              refine ⟨40624112099485120655415331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54165482799313494207220441 40624112099485120655415331)
              ·
                refine ⟨60936168149227680983122997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40624112099485120655415331 60936168149227680983122997)
                ·
                  refine ⟨5712765763990095092167781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60936168149227680983122997 5712765763990095092167781)
                  ·
                    refine ⟨1071143580748142829781459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5712765763990095092167781 1071143580748142829781459)
                    ·
                      rfl

theorem cell22_3129067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 4].length) (baseStart_3129067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129067 prefixEnd_3129067 := by exact prefixLift 3129067
  have htrace : WordTrace (prefixWord ++ tailWord_3129067) baseStart_3129067 baseEnd_3129067 := by
    simpa [prefixWord, tailWord_3129067, baseEnd_3129067] using wordTrace_append hprefix tailTrace_3129067
  have hstable : (prefixWord ++ tailWord_3129067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129067).length < 2 ^ (prefixWord ++ tailWord_3129067).sum := by decide
  have hdescent : baseEnd_3129067 < baseStart_3129067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129069 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_3129069 : Nat := 118140960795 + 3129069 * 2 ^ 59
def prefixEnd_3129069 : Nat := 4983230072969 + 3 ^ 40 * 3129069 * 2
def baseEnd_3129069 : Nat := 1071144265389015491231453

theorem tailTrace_3129069 : CollatzResearch.WordTrace tailWord_3129069 prefixEnd_3129069 1071144265389015491231453 := by
  unfold tailWord_3129069
  simp only [CollatzResearch.WordTrace]
  refine ⟨114126522300924890284358261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76084348200616593522905507 114126522300924890284358261)
  ·
    refine ⟨10699361465711708464158587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114126522300924890284358261 10699361465711708464158587)
    ·
      refine ⟨16049042198567562696237881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10699361465711708464158587 16049042198567562696237881)
      ·
        refine ⟨12036781648925672022178411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16049042198567562696237881 12036781648925672022178411)
        ·
          refine ⟨18055172473388508033267617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12036781648925672022178411 18055172473388508033267617)
          ·
            refine ⟨13541379355041381024950713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18055172473388508033267617 13541379355041381024950713)
            ·
              refine ⟨10156034516281035768713035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13541379355041381024950713 10156034516281035768713035)
              ·
                refine ⟨15234051774421553653069553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10156034516281035768713035 15234051774421553653069553)
                ·
                  refine ⟨11425538830816165239802165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15234051774421553653069553 11425538830816165239802165)
                  ·
                    refine ⟨1071144265389015491231453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11425538830816165239802165 1071144265389015491231453)
                    ·
                      rfl

theorem cell22_3129069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_3129069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129069 prefixEnd_3129069 := by exact prefixLift 3129069
  have htrace : WordTrace (prefixWord ++ tailWord_3129069) baseStart_3129069 baseEnd_3129069 := by
    simpa [prefixWord, tailWord_3129069, baseEnd_3129069] using wordTrace_append hprefix tailTrace_3129069
  have hstable : (prefixWord ++ tailWord_3129069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129069).length < 2 ^ (prefixWord ++ tailWord_3129069).sum := by decide
  have hdescent : baseEnd_3129069 < baseStart_3129069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129097 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 3, 5]
def baseStart_3129097 : Nat := 118140960795 + 3129097 * 2 ^ 59
def prefixEnd_3129097 : Nat := 4983230072969 + 3 ^ 40 * 3129097 * 2
def baseEnd_3129097 : Nat := 1071153850361232751531367

theorem tailTrace_3129097 : CollatzResearch.WordTrace tailWord_3129097 prefixEnd_3129097 1071153850361232751531367 := by
  unfold tailWord_3129097
  simp only [CollatzResearch.WordTrace]
  refine ⟨114127543544823451066377545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76085029029882300710918363 114127543544823451066377545)
  ·
    refine ⟨85595657658617588299783159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114127543544823451066377545 85595657658617588299783159)
    ·
      refine ⟨128393486487926382449674739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85595657658617588299783159 128393486487926382449674739)
      ·
        refine ⟨192590229731889573674512109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128393486487926382449674739 192590229731889573674512109)
        ·
          refine ⟨72221336149458590127942041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192590229731889573674512109 72221336149458590127942041)
          ·
            refine ⟨54166002112093942595956531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72221336149458590127942041 54166002112093942595956531)
            ·
              refine ⟨81249003168140913893934797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54166002112093942595956531 81249003168140913893934797)
              ·
                refine ⟨30468376188052842710225549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81249003168140913893934797 30468376188052842710225549)
                ·
                  refine ⟨11425641070519816016334581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30468376188052842710225549 11425641070519816016334581)
                  ·
                    refine ⟨1071153850361232751531367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11425641070519816016334581 1071153850361232751531367)
                    ·
                      rfl

theorem cell22_3129097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_3129097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129097 prefixEnd_3129097 := by exact prefixLift 3129097
  have htrace : WordTrace (prefixWord ++ tailWord_3129097) baseStart_3129097 baseEnd_3129097 := by
    simpa [prefixWord, tailWord_3129097, baseEnd_3129097] using wordTrace_append hprefix tailTrace_3129097
  have hstable : (prefixWord ++ tailWord_3129097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129097).length < 2 ^ (prefixWord ++ tailWord_3129097).sum := by decide
  have hdescent : baseEnd_3129097 < baseStart_3129097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129146 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 2, 4]
def baseStart_3129146 : Nat := 118140960795 + 3129146 * 2 ^ 59
def prefixEnd_3129146 : Nat := 4983230072969 + 3 ^ 40 * 3129146 * 2
def baseEnd_3129146 : Nat := 1071170624062612957056217

theorem tailTrace_3129146 : CollatzResearch.WordTrace tailWord_3129146 prefixEnd_3129146 1071170624062612957056217 := by
  unfold tailWord_3129146
  simp only [CollatzResearch.WordTrace]
  refine ⟨28532332680411483108727823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76086220481097288289940861 28532332680411483108727823)
  ·
    refine ⟨42798499020617224663091735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28532332680411483108727823 42798499020617224663091735)
    ·
      refine ⟨64197748530925836994637603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42798499020617224663091735 64197748530925836994637603)
      ·
        refine ⟨96296622796388755491956405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64197748530925836994637603 96296622796388755491956405)
        ·
          refine ⟨9027808387161445827370913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96296622796388755491956405 9027808387161445827370913)
          ·
            refine ⟨6770856290371084370528185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9027808387161445827370913 6770856290371084370528185)
            ·
              refine ⟨5078142217778313277896139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6770856290371084370528185 5078142217778313277896139)
              ·
                refine ⟨7617213326667469916844209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5078142217778313277896139 7617213326667469916844209)
                ·
                  refine ⟨5712909995000602437633157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7617213326667469916844209 5712909995000602437633157)
                  ·
                    refine ⟨1071170624062612957056217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5712909995000602437633157 1071170624062612957056217)
                    ·
                      rfl

theorem cell22_3129146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_3129146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129146 prefixEnd_3129146 := by exact prefixLift 3129146
  have htrace : WordTrace (prefixWord ++ tailWord_3129146) baseStart_3129146 baseEnd_3129146 := by
    simpa [prefixWord, tailWord_3129146, baseEnd_3129146] using wordTrace_append hprefix tailTrace_3129146
  have hstable : (prefixWord ++ tailWord_3129146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129146).length < 2 ^ (prefixWord ++ tailWord_3129146).sum := by decide
  have hdescent : baseEnd_3129146 < baseStart_3129146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129165 : List Nat := [1, 6, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_3129165 : Nat := 118140960795 + 3129165 * 2 ^ 59
def prefixEnd_3129165 : Nat := 4983230072969 + 3 ^ 40 * 3129165 * 2
def baseEnd_3129165 : Nat := 1071177128150903240831159

theorem tailTrace_3129165 : CollatzResearch.WordTrace tailWord_3129165 prefixEnd_3129165 1071177128150903240831159 := by
  unfold tailWord_3129165
  simp only [CollatzResearch.WordTrace]
  refine ⟨114130023708577098679852949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76086682472384732453235299 114130023708577098679852949)
  ·
    refine ⟨5349844861339551500618107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 114130023708577098679852949 5349844861339551500618107)
    ·
      refine ⟨8024767292009327250927161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5349844861339551500618107 8024767292009327250927161)
      ·
        refine ⟨6018575469006995438195371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8024767292009327250927161 6018575469006995438195371)
        ·
          refine ⟨9027863203510493157293057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6018575469006995438195371 9027863203510493157293057)
          ·
            refine ⟨6770897402632869867969793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9027863203510493157293057 6770897402632869867969793)
            ·
              refine ⟨5078173051974652400977345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6770897402632869867969793 5078173051974652400977345)
              ·
                refine ⟨3808629788980989300733009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5078173051974652400977345 3808629788980989300733009)
                ·
                  refine ⟨2856472341735741975549757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3808629788980989300733009 2856472341735741975549757)
                  ·
                    refine ⟨1071177128150903240831159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2856472341735741975549757 1071177128150903240831159)
                    ·
                      rfl

theorem cell22_3129165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_3129165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129165 prefixEnd_3129165 := by exact prefixLift 3129165
  have htrace : WordTrace (prefixWord ++ tailWord_3129165) baseStart_3129165 baseEnd_3129165 := by
    simpa [prefixWord, tailWord_3129165, baseEnd_3129165] using wordTrace_append hprefix tailTrace_3129165
  have hstable : (prefixWord ++ tailWord_3129165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129165).length < 2 ^ (prefixWord ++ tailWord_3129165).sum := by decide
  have hdescent : baseEnd_3129165 < baseStart_3129165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129223 : List Nat := [1, 1, 4, 2, 4, 2, 1, 2, 5]
def baseStart_3129223 : Nat := 118140960795 + 3129223 * 2 ^ 59
def prefixEnd_3129223 : Nat := 4983230072969 + 3 ^ 40 * 3129223 * 2
def baseEnd_3129223 : Nat := 357065660912070140960327

theorem tailTrace_3129223 : CollatzResearch.WordTrace tailWord_3129223 prefixEnd_3129223 357065660912070140960327 := by
  unfold tailWord_3129223
  simp only [CollatzResearch.WordTrace]
  refine ⟨114132139142366974585464323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76088092761577983056976215 114132139142366974585464323)
  ·
    refine ⟨171198208713550461878196485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114132139142366974585464323 171198208713550461878196485)
    ·
      refine ⟨32099664133790711602161841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171198208713550461878196485 32099664133790711602161841)
      ·
        refine ⟨24074748100343033701621381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32099664133790711602161841 24074748100343033701621381)
        ·
          refine ⟨4514015268814318819054009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24074748100343033701621381 4514015268814318819054009)
          ·
            refine ⟨3385511451610739114290507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4514015268814318819054009 3385511451610739114290507)
            ·
              refine ⟨5078267177416108671435761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3385511451610739114290507 5078267177416108671435761)
              ·
                refine ⟨3808700383062081503576821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5078267177416108671435761 3808700383062081503576821)
                ·
                  refine ⟨357065660912070140960327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3808700383062081503576821 357065660912070140960327)
                  ·
                    rfl

theorem cell22_3129223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 5].length) (baseStart_3129223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129223 prefixEnd_3129223 := by exact prefixLift 3129223
  have htrace : WordTrace (prefixWord ++ tailWord_3129223) baseStart_3129223 baseEnd_3129223 := by
    simpa [prefixWord, tailWord_3129223, baseEnd_3129223] using wordTrace_append hprefix tailTrace_3129223
  have hstable : (prefixWord ++ tailWord_3129223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129223).length < 2 ^ (prefixWord ++ tailWord_3129223).sum := by decide
  have hdescent : baseEnd_3129223 < baseStart_3129223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129240 : List Nat := [2, 1, 2, 6, 1, 1, 3, 1, 5]
def baseStart_3129240 : Nat := 118140960795 + 3129240 * 2 ^ 59
def prefixEnd_3129240 : Nat := 4983230072969 + 3 ^ 40 * 3129240 * 2
def baseEnd_3129240 : Nat := 357067600727876015068643

theorem tailTrace_3129240 : CollatzResearch.WordTrace tailWord_3129240 prefixEnd_3129240 357067600727876015068643 := by
  unfold tailWord_3129240
  simp only [CollatzResearch.WordTrace]
  refine ⟨57066379591652693244416587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76088506122203590992555449 57066379591652693244416587)
  ·
    refine ⟨85599569387479039866624881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57066379591652693244416587 85599569387479039866624881)
    ·
      refine ⟨64199677040609279899968661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85599569387479039866624881 64199677040609279899968661)
      ·
        refine ⟨3009359861278559995311031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64199677040609279899968661 3009359861278559995311031)
        ·
          refine ⟨4514039791917839992966547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3009359861278559995311031 4514039791917839992966547)
          ·
            refine ⟨6771059687876759989449821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514039791917839992966547 6771059687876759989449821)
            ·
              refine ⟨2539147382953784996043683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6771059687876759989449821 2539147382953784996043683)
              ·
                refine ⟨3808721074430677494065525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2539147382953784996043683 3808721074430677494065525)
                ·
                  refine ⟨357067600727876015068643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3808721074430677494065525 357067600727876015068643)
                  ·
                    rfl

theorem cell22_3129240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 5].length) (baseStart_3129240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129240 prefixEnd_3129240 := by exact prefixLift 3129240
  have htrace : WordTrace (prefixWord ++ tailWord_3129240) baseStart_3129240 baseEnd_3129240 := by
    simpa [prefixWord, tailWord_3129240, baseEnd_3129240] using wordTrace_append hprefix tailTrace_3129240
  have hstable : (prefixWord ++ tailWord_3129240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129240).length < 2 ^ (prefixWord ++ tailWord_3129240).sum := by decide
  have hdescent : baseEnd_3129240 < baseStart_3129240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129264 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 8, 4]
def baseStart_3129264 : Nat := 118140960795 + 3129264 * 2 ^ 59
def prefixEnd_3129264 : Nat := 4983230072969 + 3 ^ 40 * 3129264 * 2
def baseEnd_3129264 : Nat := 1071211017874099982605855

theorem tailTrace_3129264 : CollatzResearch.WordTrace tailWord_3129264 prefixEnd_3129264 1071211017874099982605855 := by
  unfold tailWord_3129264
  simp only [CollatzResearch.WordTrace]
  refine ⟨57066817267609219293853423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76089089690145625725137897 57066817267609219293853423)
  ·
    refine ⟨85600225901413828940780135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57066817267609219293853423 85600225901413828940780135)
    ·
      refine ⟨128400338852120743411170203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85600225901413828940780135 128400338852120743411170203)
      ·
        refine ⟨192600508278181115116755305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128400338852120743411170203 192600508278181115116755305)
        ·
          refine ⟨144450381208635836337566479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192600508278181115116755305 144450381208635836337566479)
          ·
            refine ⟨216675571812953754506349719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144450381208635836337566479 216675571812953754506349719)
            ·
              refine ⟨325013357719430631759524579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216675571812953754506349719 325013357719430631759524579)
              ·
                refine ⟨487520036579145947639286869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325013357719430631759524579 487520036579145947639286869)
                ·
                  refine ⟨5713125428661866573897893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 487520036579145947639286869 5713125428661866573897893)
                  ·
                    refine ⟨1071211017874099982605855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5713125428661866573897893 1071211017874099982605855)
                    ·
                      rfl

theorem cell22_3129264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_3129264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129264 prefixEnd_3129264 := by exact prefixLift 3129264
  have htrace : WordTrace (prefixWord ++ tailWord_3129264) baseStart_3129264 baseEnd_3129264 := by
    simpa [prefixWord, tailWord_3129264, baseEnd_3129264] using wordTrace_append hprefix tailTrace_3129264
  have hstable : (prefixWord ++ tailWord_3129264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129264).length < 2 ^ (prefixWord ++ tailWord_3129264).sum := by decide
  have hdescent : baseEnd_3129264 < baseStart_3129264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129324 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 9]
def baseStart_3129324 : Nat := 118140960795 + 3129324 * 2 ^ 59
def prefixEnd_3129324 : Nat := 4983230072969 + 3 ^ 40 * 3129324 * 2
def baseEnd_3129324 : Nat := 357077185700093275368557

theorem tailTrace_3129324 : CollatzResearch.WordTrace tailWord_3129324 prefixEnd_3129324 357077185700093275368557 := by
  unfold tailWord_3129324
  simp only [CollatzResearch.WordTrace]
  refine ⟨57067911457500534417445513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76090548610000712556594017 57067911457500534417445513)
  ·
    refine ⟨42800933593125400813084135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57067911457500534417445513 42800933593125400813084135)
    ·
      refine ⟨64201400389688101219626203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42800933593125400813084135 64201400389688101219626203)
      ·
        refine ⟨96302100584532151829439305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64201400389688101219626203 96302100584532151829439305)
        ·
          refine ⟨72226575438399113872079479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96302100584532151829439305 72226575438399113872079479)
          ·
            refine ⟨108339863157598670808119219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72226575438399113872079479 108339863157598670808119219)
            ·
              refine ⟨162509794736398006212178829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108339863157598670808119219 162509794736398006212178829)
              ·
                refine ⟨60941173026149252329567061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162509794736398006212178829 60941173026149252329567061)
                ·
                  refine ⟨357077185700093275368557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60941173026149252329567061 357077185700093275368557)
                  ·
                    rfl

theorem cell22_3129324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_3129324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129324 prefixEnd_3129324 := by exact prefixLift 3129324
  have htrace : WordTrace (prefixWord ++ tailWord_3129324) baseStart_3129324 baseEnd_3129324 := by
    simpa [prefixWord, tailWord_3129324, baseEnd_3129324] using wordTrace_append hprefix tailTrace_3129324
  have hstable : (prefixWord ++ tailWord_3129324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129324).length < 2 ^ (prefixWord ++ tailWord_3129324).sum := by decide
  have hdescent : baseEnd_3129324 < baseStart_3129324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129341 : List Nat := [1, 4, 1, 1, 1, 2, 3, 4, 5]
def baseStart_3129341 : Nat := 118140960795 + 3129341 * 2 ^ 59
def prefixEnd_3129341 : Nat := 4983230072969 + 3 ^ 40 * 3129341 * 2
def baseEnd_3129341 : Nat := 357079125515899149476873

theorem tailTrace_3129341 : CollatzResearch.WordTrace tailWord_3129341 prefixEnd_3129341 357079125515899149476873 := by
  unfold tailWord_3129341
  simp only [CollatzResearch.WordTrace]
  refine ⟨114136442955939480738259877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76090961970626320492173251 114136442955939480738259877)
  ·
    refine ⟨21400583054238652638423727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114136442955939480738259877 21400583054238652638423727)
    ·
      refine ⟨32100874581357978957635591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21400583054238652638423727 32100874581357978957635591)
      ·
        refine ⟨48151311872036968436453387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32100874581357978957635591 48151311872036968436453387)
        ·
          refine ⟨72226967808055452654680081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48151311872036968436453387 72226967808055452654680081)
          ·
            refine ⟨54170225856041589491010061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72226967808055452654680081 54170225856041589491010061)
            ·
              refine ⟨20313834696015596059128773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54170225856041589491010061 20313834696015596059128773)
              ·
                refine ⟨3808844005502924261086645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20313834696015596059128773 3808844005502924261086645)
                ·
                  refine ⟨357079125515899149476873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3808844005502924261086645 357079125515899149476873)
                  ·
                    rfl

theorem cell22_3129341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_3129341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129341 prefixEnd_3129341 := by exact prefixLift 3129341
  have htrace : WordTrace (prefixWord ++ tailWord_3129341) baseStart_3129341 baseEnd_3129341 := by
    simpa [prefixWord, tailWord_3129341, baseEnd_3129341] using wordTrace_append hprefix tailTrace_3129341
  have hstable : (prefixWord ++ tailWord_3129341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129341).length < 2 ^ (prefixWord ++ tailWord_3129341).sum := by decide
  have hdescent : baseEnd_3129341 < baseStart_3129341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129345 : List Nat := [1, 2, 4, 1, 2, 1, 3, 4, 1, 3]
def baseStart_3129345 : Nat := 118140960795 + 3129345 * 2 ^ 59
def prefixEnd_3129345 : Nat := 4983230072969 + 3 ^ 40 * 3129345 * 2
def baseEnd_3129345 : Nat := 1071238745829442771330607

theorem tailTrace_3129345 : CollatzResearch.WordTrace tailWord_3129345 prefixEnd_3129345 1071238745829442771330607 := by
  unfold tailWord_3129345
  simp only [CollatzResearch.WordTrace]
  refine ⟨114136588847924989421405489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76091059231949992947603659 114136588847924989421405489)
  ·
    refine ⟨85602441635943742066054117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114136588847924989421405489 85602441635943742066054117)
    ·
      refine ⟨16050457806739451637385147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85602441635943742066054117 16050457806739451637385147)
      ·
        refine ⟨24075686710109177456077721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16050457806739451637385147 24075686710109177456077721)
        ·
          refine ⟨18056765032581883092058291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24075686710109177456077721 18056765032581883092058291)
          ·
            refine ⟨27085147548872824638087437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18056765032581883092058291 27085147548872824638087437)
            ·
              refine ⟨10156930330827309239282789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27085147548872824638087437 10156930330827309239282789)
              ·
                refine ⟨1904424437030120482365523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10156930330827309239282789 1904424437030120482365523)
                ·
                  refine ⟨2856636655545180723548285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1904424437030120482365523 2856636655545180723548285)
                  ·
                    refine ⟨1071238745829442771330607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2856636655545180723548285 1071238745829442771330607)
                    ·
                      rfl

theorem cell22_3129345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_3129345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129345 prefixEnd_3129345 := by exact prefixLift 3129345
  have htrace : WordTrace (prefixWord ++ tailWord_3129345) baseStart_3129345 baseEnd_3129345 := by
    simpa [prefixWord, tailWord_3129345, baseEnd_3129345] using wordTrace_append hprefix tailTrace_3129345
  have hstable : (prefixWord ++ tailWord_3129345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129345).length < 2 ^ (prefixWord ++ tailWord_3129345).sum := by decide
  have hdescent : baseEnd_3129345 < baseStart_3129345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129356 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 2, 5]
def baseStart_3129356 : Nat := 118140960795 + 3129356 * 2 ^ 59
def prefixEnd_3129356 : Nat := 4983230072969 + 3 ^ 40 * 3129356 * 2
def baseEnd_3129356 : Nat := 1071242511354242409305573

theorem tailTrace_3129356 : CollatzResearch.WordTrace tailWord_3129356 prefixEnd_3129356 1071242511354242409305573 := by
  unfold tailWord_3129356
  simp only [CollatzResearch.WordTrace]
  refine ⟨57068495025442569150027961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76091326700590092200037281 57068495025442569150027961)
  ·
    refine ⟨42801371269081926862520971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57068495025442569150027961 42801371269081926862520971)
    ·
      refine ⟨64202056903622890293781457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42801371269081926862520971 64202056903622890293781457)
      ·
        refine ⟨48151542677717167720336093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64202056903622890293781457 48151542677717167720336093)
        ·
          refine ⟨18056828504143937895126035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48151542677717167720336093 18056828504143937895126035)
          ·
            refine ⟨27085242756215906842689053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18056828504143937895126035 27085242756215906842689053)
            ·
              refine ⟨10156966033580965066008395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27085242756215906842689053 10156966033580965066008395)
              ·
                refine ⟨15235449050371447599012593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10156966033580965066008395 15235449050371447599012593)
                ·
                  refine ⟨11426586787778585699259445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15235449050371447599012593 11426586787778585699259445)
                  ·
                    refine ⟨1071242511354242409305573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11426586787778585699259445 1071242511354242409305573)
                    ·
                      rfl

theorem cell22_3129356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_3129356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129356 prefixEnd_3129356 := by exact prefixLift 3129356
  have htrace : WordTrace (prefixWord ++ tailWord_3129356) baseStart_3129356 baseEnd_3129356 := by
    simpa [prefixWord, tailWord_3129356, baseEnd_3129356] using wordTrace_append hprefix tailTrace_3129356
  have hstable : (prefixWord ++ tailWord_3129356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129356).length < 2 ^ (prefixWord ++ tailWord_3129356).sum := by decide
  have hdescent : baseEnd_3129356 < baseStart_3129356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129416 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 6, 4]
def baseStart_3129416 : Nat := 118140960795 + 3129416 * 2 ^ 59
def prefixEnd_3129416 : Nat := 4983230072969 + 3 ^ 40 * 3129416 * 2
def baseEnd_3129416 : Nat := 1071263050580422252805389

theorem tailTrace_3129416 : CollatzResearch.WordTrace tailWord_3129416 prefixEnd_3129416 1071263050580422252805389 := by
  unfold tailWord_3129416
  simp only [CollatzResearch.WordTrace]
  refine ⟨57069589215333884273620051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76092785620445179031493401 57069589215333884273620051)
  ·
    refine ⟨85604383823000826410430077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57069589215333884273620051 85604383823000826410430077)
    ·
      refine ⟨32101643933625309903911279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85604383823000826410430077 32101643933625309903911279)
      ·
        refine ⟨48152465900437964855866919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32101643933625309903911279 48152465900437964855866919)
        ·
          refine ⟨72228698850656947283800379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48152465900437964855866919 72228698850656947283800379)
          ·
            refine ⟨108343048275985420925700569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72228698850656947283800379 108343048275985420925700569)
            ·
              refine ⟨81257286206989065694275427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108343048275985420925700569 81257286206989065694275427)
              ·
                refine ⟨121885929310483598541413141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81257286206989065694275427 121885929310483598541413141)
                ·
                  refine ⟨5713402936428918681628741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121885929310483598541413141 5713402936428918681628741)
                  ·
                    refine ⟨1071263050580422252805389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5713402936428918681628741 1071263050580422252805389)
                    ·
                      rfl

theorem cell22_3129416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_3129416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129416 prefixEnd_3129416 := by exact prefixLift 3129416
  have htrace : WordTrace (prefixWord ++ tailWord_3129416) baseStart_3129416 baseEnd_3129416 := by
    simpa [prefixWord, tailWord_3129416, baseEnd_3129416] using wordTrace_append hprefix tailTrace_3129416
  have hstable : (prefixWord ++ tailWord_3129416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129416).length < 2 ^ (prefixWord ++ tailWord_3129416).sum := by decide
  have hdescent : baseEnd_3129416 < baseStart_3129416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129437 : List Nat := [1, 4, 4, 1, 1, 1, 3, 3, 4]
def baseStart_3129437 : Nat := 118140960795 + 3129437 * 2 ^ 59
def prefixEnd_3129437 : Nat := 4983230072969 + 3 ^ 40 * 3129437 * 2
def baseEnd_3129437 : Nat := 357090079769861732676775

theorem tailTrace_3129437 : CollatzResearch.WordTrace tailWord_3129437 prefixEnd_3129437 357090079769861732676775 := by
  unfold tailWord_3129437
  simp only [CollatzResearch.WordTrace]
  refine ⟨114139944363591689133754565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76093296242394459422503043 114139944363591689133754565)
  ·
    refine ⟨21401239568173441712578981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114139944363591689133754565 21401239568173441712578981)
    ·
      refine ⟨4012732419032520321108559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21401239568173441712578981 4012732419032520321108559)
      ·
        refine ⟨6019098628548780481662839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4012732419032520321108559 6019098628548780481662839)
        ·
          refine ⟨9028647942823170722494259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6019098628548780481662839 9028647942823170722494259)
          ·
            refine ⟨13542971914234756083741389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9028647942823170722494259 13542971914234756083741389)
            ·
              refine ⟨5078614467838033531403021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13542971914234756083741389 5078614467838033531403021)
              ·
                refine ⟨1904480425439262574276133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5078614467838033531403021 1904480425439262574276133)
                ·
                  refine ⟨357090079769861732676775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1904480425439262574276133 357090079769861732676775)
                  ·
                    rfl

theorem cell22_3129437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_3129437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129437 prefixEnd_3129437 := by exact prefixLift 3129437
  have htrace : WordTrace (prefixWord ++ tailWord_3129437) baseStart_3129437 baseEnd_3129437 := by
    simpa [prefixWord, tailWord_3129437, baseEnd_3129437] using wordTrace_append hprefix tailTrace_3129437
  have hstable : (prefixWord ++ tailWord_3129437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129437).length < 2 ^ (prefixWord ++ tailWord_3129437).sum := by decide
  have hdescent : baseEnd_3129437 < baseStart_3129437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129450 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 2, 4]
def baseStart_3129450 : Nat := 118140960795 + 3129450 * 2 ^ 59
def prefixEnd_3129450 : Nat := 4983230072969 + 3 ^ 40 * 3129450 * 2
def baseEnd_3129450 : Nat := 1071274689475257497455285

theorem tailTrace_3129450 : CollatzResearch.WordTrace tailWord_3129450 prefixEnd_3129450 1071274689475257497455285 := by
  unfold tailWord_3129450
  simp only [CollatzResearch.WordTrace]
  refine ⟨28535104628136148088494451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76093612341696394902651869 28535104628136148088494451)
  ·
    refine ⟨42802656942204222132741677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28535104628136148088494451 42802656942204222132741677)
    ·
      refine ⟨16050996353326583299778129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42802656942204222132741677 16050996353326583299778129)
      ·
        refine ⟨12038247264994937474833597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16050996353326583299778129 12038247264994937474833597)
        ·
          refine ⟨4514342724373101553062599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12038247264994937474833597 4514342724373101553062599)
          ·
            refine ⟨6771514086559652329593899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514342724373101553062599 6771514086559652329593899)
            ·
              refine ⟨10157271129839478494390849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6771514086559652329593899 10157271129839478494390849)
              ·
                refine ⟨7617953347379608870793137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10157271129839478494390849 7617953347379608870793137)
                ·
                  refine ⟨5713465010534706653094853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7617953347379608870793137 5713465010534706653094853)
                  ·
                    refine ⟨1071274689475257497455285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5713465010534706653094853 1071274689475257497455285)
                    ·
                      rfl

theorem cell22_3129450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_3129450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129450 prefixEnd_3129450 := by exact prefixLift 3129450
  have htrace : WordTrace (prefixWord ++ tailWord_3129450) baseStart_3129450 baseEnd_3129450 := by
    simpa [prefixWord, tailWord_3129450, baseEnd_3129450] using wordTrace_append hprefix tailTrace_3129450
  have hstable : (prefixWord ++ tailWord_3129450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129450).length < 2 ^ (prefixWord ++ tailWord_3129450).sum := by decide
  have hdescent : baseEnd_3129450 < baseStart_3129450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129491 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 4, 5]
def baseStart_3129491 : Nat := 118140960795 + 3129491 * 2 ^ 59
def prefixEnd_3129491 : Nat := 4983230072969 + 3 ^ 40 * 3129491 * 2
def baseEnd_3129491 : Nat := 1071288724613147057180159

theorem tailTrace_3129491 : CollatzResearch.WordTrace tailWord_3129491 prefixEnd_3129491 1071288724613147057180159 := by
  unfold tailWord_3129491
  simp only [CollatzResearch.WordTrace]
  refine ⟨114141913905396056356220327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76094609270264037570813551 114141913905396056356220327)
  ·
    refine ⟨171212870858094084534330491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114141913905396056356220327 171212870858094084534330491)
    ·
      refine ⟨256819306287141126801495737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171212870858094084534330491 256819306287141126801495737)
      ·
        refine ⟨192614479715355845101121803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256819306287141126801495737 192614479715355845101121803)
        ·
          refine ⟨288921719573033767651682705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192614479715355845101121803 288921719573033767651682705)
          ·
            refine ⟨216691289679775325738762029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288921719573033767651682705 216691289679775325738762029)
            ·
              refine ⟨81259233629915747152035761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216691289679775325738762029 81259233629915747152035761)
              ·
                refine ⟨60944425222436810364026821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81259233629915747152035761 60944425222436810364026821)
                ·
                  refine ⟨11427079729206901943255029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60944425222436810364026821 11427079729206901943255029)
                  ·
                    refine ⟨1071288724613147057180159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11427079729206901943255029 1071288724613147057180159)
                    ·
                      rfl

theorem cell22_3129491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 5].length) (baseStart_3129491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129491 prefixEnd_3129491 := by exact prefixLift 3129491
  have htrace : WordTrace (prefixWord ++ tailWord_3129491) baseStart_3129491 baseEnd_3129491 := by
    simpa [prefixWord, tailWord_3129491, baseEnd_3129491] using wordTrace_append hprefix tailTrace_3129491
  have hstable : (prefixWord ++ tailWord_3129491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129491).length < 2 ^ (prefixWord ++ tailWord_3129491).sum := by decide
  have hdescent : baseEnd_3129491 < baseStart_3129491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129540 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_3129540 : Nat := 118140960795 + 3129540 * 2 ^ 59
def prefixEnd_3129540 : Nat := 4983230072969 + 3 ^ 40 * 3129540 * 2
def baseEnd_3129540 : Nat := 1071305498314527262705009

theorem tailTrace_3129540 : CollatzResearch.WordTrace tailWord_3129540 prefixEnd_3129540 1071305498314527262705009 := by
  unfold tailWord_3129540
  simp only [CollatzResearch.WordTrace]
  refine ⟨57071850541109268862377037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76095800721479025149836049 57071850541109268862377037)
  ·
    refine ⟨21401943952915975823391389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57071850541109268862377037 21401943952915975823391389)
    ·
      refine ⟨8025728982343490933771771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21401943952915975823391389 8025728982343490933771771)
      ·
        refine ⟨12038593473515236400657657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8025728982343490933771771 12038593473515236400657657)
        ·
          refine ⟨9028945105136427300493243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12038593473515236400657657 9028945105136427300493243)
          ·
            refine ⟨13543417657704640950739865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9028945105136427300493243 13543417657704640950739865)
            ·
              refine ⟨10157563243278480713054899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13543417657704640950739865 10157563243278480713054899)
              ·
                refine ⟨15236344864917721069582349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10157563243278480713054899 15236344864917721069582349)
                ·
                  refine ⟨5713629324344145401093381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15236344864917721069582349 5713629324344145401093381)
                  ·
                    refine ⟨1071305498314527262705009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5713629324344145401093381 1071305498314527262705009)
                    ·
                      rfl

theorem cell22_3129540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_3129540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129540 prefixEnd_3129540 := by exact prefixLift 3129540
  have htrace : WordTrace (prefixWord ++ tailWord_3129540) baseStart_3129540 baseEnd_3129540 := by
    simpa [prefixWord, tailWord_3129540, baseEnd_3129540] using wordTrace_append hprefix tailTrace_3129540
  have hstable : (prefixWord ++ tailWord_3129540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129540).length < 2 ^ (prefixWord ++ tailWord_3129540).sum := by decide
  have hdescent : baseEnd_3129540 < baseStart_3129540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129553 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 1, 5]
def baseStart_3129553 : Nat := 118140960795 + 3129553 * 2 ^ 59
def prefixEnd_3129553 : Nat := 4983230072969 + 3 ^ 40 * 3129553 * 2
def baseEnd_3129553 : Nat := 1071309948480199562129969

theorem tailTrace_3129553 : CollatzResearch.WordTrace tailWord_3129553 prefixEnd_3129553 1071309948480199562129969 := by
  unfold tailWord_3129553
  simp only [CollatzResearch.WordTrace]
  refine ⟨114144175231171440944977313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76096116820780960629984875 114144175231171440944977313)
  ·
    refine ⟨85608131423378580708732985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114144175231171440944977313 85608131423378580708732985)
    ·
      refine ⟨64206098567533935531549739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85608131423378580708732985 64206098567533935531549739)
      ·
        refine ⟨96309147851300903297324609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64206098567533935531549739 96309147851300903297324609)
        ·
          refine ⟨72231860888475677472993457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96309147851300903297324609 72231860888475677472993457)
          ·
            refine ⟨54173895666356758104745093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72231860888475677472993457 54173895666356758104745093)
            ·
              refine ⟨10157605437441892144639705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54173895666356758104745093 10157605437441892144639705)
              ·
                refine ⟨7618204078081419108479779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10157605437441892144639705 7618204078081419108479779)
                ·
                  refine ⟨11427306117122128662719669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7618204078081419108479779 11427306117122128662719669)
                  ·
                    refine ⟨1071309948480199562129969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11427306117122128662719669 1071309948480199562129969)
                    ·
                      rfl

theorem cell22_3129553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_3129553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129553 prefixEnd_3129553 := by exact prefixLift 3129553
  have htrace : WordTrace (prefixWord ++ tailWord_3129553) baseStart_3129553 baseEnd_3129553 := by
    simpa [prefixWord, tailWord_3129553, baseEnd_3129553] using wordTrace_append hprefix tailTrace_3129553
  have hstable : (prefixWord ++ tailWord_3129553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129553).length < 2 ^ (prefixWord ++ tailWord_3129553).sum := by decide
  have hdescent : baseEnd_3129553 < baseStart_3129553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129557 : List Nat := [1, 3, 2, 4, 2, 1, 1, 3, 1, 4]
def baseStart_3129557 : Nat := 118140960795 + 3129557 * 2 ^ 59
def prefixEnd_3129557 : Nat := 4983230072969 + 3 ^ 40 * 3129557 * 2
def baseEnd_3129557 : Nat := 1071311317761944885029957

theorem tailTrace_3129557 : CollatzResearch.WordTrace tailWord_3129557 prefixEnd_3129557 1071311317761944885029957 := by
  unfold tailWord_3129557
  simp only [CollatzResearch.WordTrace]
  refine ⟨114144321123156949628122925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76096214082104633085415283 114144321123156949628122925)
  ·
    refine ⟨42804120421183856110546097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114144321123156949628122925 42804120421183856110546097)
    ·
      refine ⟨32103090315887892082909573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42804120421183856110546097 32103090315887892082909573)
      ·
        refine ⟨6019329434228979765545545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32103090315887892082909573 6019329434228979765545545)
        ·
          refine ⟨4514497075671734824159159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6019329434228979765545545 4514497075671734824159159)
          ·
            refine ⟨6771745613507602236238739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514497075671734824159159 6771745613507602236238739)
            ·
              refine ⟨10157618420261403354358109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6771745613507602236238739 10157618420261403354358109)
              ·
                refine ⟨3809106907598026257884291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10157618420261403354358109 3809106907598026257884291)
                ·
                  refine ⟨5713660361397039386826437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3809106907598026257884291 5713660361397039386826437)
                  ·
                    refine ⟨1071311317761944885029957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5713660361397039386826437 1071311317761944885029957)
                    ·
                      rfl

theorem cell22_3129557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_3129557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129557 prefixEnd_3129557 := by exact prefixLift 3129557
  have htrace : WordTrace (prefixWord ++ tailWord_3129557) baseStart_3129557 baseEnd_3129557 := by
    simpa [prefixWord, tailWord_3129557, baseEnd_3129557] using wordTrace_append hprefix tailTrace_3129557
  have hstable : (prefixWord ++ tailWord_3129557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129557).length < 2 ^ (prefixWord ++ tailWord_3129557).sum := by decide
  have hdescent : baseEnd_3129557 < baseStart_3129557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129568 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 4, 4]
def baseStart_3129568 : Nat := 118140960795 + 3129568 * 2 ^ 59
def prefixEnd_3129568 : Nat := 4983230072969 + 3 ^ 40 * 3129568 * 2
def baseEnd_3129568 : Nat := 1071315083286744523004923

theorem tailTrace_3129568 : CollatzResearch.WordTrace tailWord_3129568 prefixEnd_3129568 1071315083286744523004923 := by
  unfold tailWord_3129568
  simp only [CollatzResearch.WordTrace]
  refine ⟨57072361163058549253386679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76096481550744732337848905 57072361163058549253386679)
  ·
    refine ⟨85608541744587823880080019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57072361163058549253386679 85608541744587823880080019)
    ·
      refine ⟨128412812616881735820120029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85608541744587823880080019 128412812616881735820120029)
      ·
        refine ⟨48154804731330650932545011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128412812616881735820120029 48154804731330650932545011)
        ·
          refine ⟨72232207096995976398817517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48154804731330650932545011 72232207096995976398817517)
          ·
            refine ⟨27087077661373491149556569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72232207096995976398817517 27087077661373491149556569)
            ·
              refine ⟨20315308246030118362167427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27087077661373491149556569 20315308246030118362167427)
              ·
                refine ⟨30472962369045177543251141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20315308246030118362167427 30472962369045177543251141)
                ·
                  refine ⟨5713680444195970789359589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30472962369045177543251141 5713680444195970789359589)
                  ·
                    refine ⟨1071315083286744523004923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5713680444195970789359589 1071315083286744523004923)
                    ·
                      rfl

theorem cell22_3129568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_3129568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129568 prefixEnd_3129568 := by exact prefixLift 3129568
  have htrace : WordTrace (prefixWord ++ tailWord_3129568) baseStart_3129568 baseEnd_3129568 := by
    simpa [prefixWord, tailWord_3129568, baseEnd_3129568] using wordTrace_append hprefix tailTrace_3129568
  have hstable : (prefixWord ++ tailWord_3129568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129568).length < 2 ^ (prefixWord ++ tailWord_3129568).sum := by decide
  have hdescent : baseEnd_3129568 < baseStart_3129568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129587 : List Nat := [1, 1, 1, 2, 2, 4, 5, 1, 2, 3]
def baseStart_3129587 : Nat := 118140960795 + 3129587 * 2 ^ 59
def prefixEnd_3129587 : Nat := 4983230072969 + 3 ^ 40 * 3129587 * 2
def baseEnd_3129587 : Nat := 1071321587375034806779865

theorem tailTrace_3129587 : CollatzResearch.WordTrace tailWord_3129587 prefixEnd_3129587 1071321587375034806779865 := by
  unfold tailWord_3129587
  simp only [CollatzResearch.WordTrace]
  refine ⟨114145415313048264751715015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76096943542032176501143343 114145415313048264751715015)
  ·
    refine ⟨171218122969572397127572523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114145415313048264751715015 171218122969572397127572523)
    ·
      refine ⟨256827184454358595691358785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171218122969572397127572523 256827184454358595691358785)
      ·
        refine ⟨192620388340768946768519089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256827184454358595691358785 192620388340768946768519089)
        ·
          refine ⟨144465291255576710076389317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192620388340768946768519089 144465291255576710076389317)
          ·
            refine ⟨27087242110420633139322997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144465291255576710076389317 27087242110420633139322997)
            ·
              refine ⟨2539428947851934356811531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27087242110420633139322997 2539428947851934356811531)
              ·
                refine ⟨3809143421777901535217297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2539428947851934356811531 3809143421777901535217297)
                ·
                  refine ⟨2856857566333426151412973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3809143421777901535217297 2856857566333426151412973)
                  ·
                    refine ⟨1071321587375034806779865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2856857566333426151412973 1071321587375034806779865)
                    ·
                      rfl

theorem cell22_3129587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 2, 3].length) (baseStart_3129587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129587 prefixEnd_3129587 := by exact prefixLift 3129587
  have htrace : WordTrace (prefixWord ++ tailWord_3129587) baseStart_3129587 baseEnd_3129587 := by
    simpa [prefixWord, tailWord_3129587, baseEnd_3129587] using wordTrace_append hprefix tailTrace_3129587
  have hstable : (prefixWord ++ tailWord_3129587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129587).length < 2 ^ (prefixWord ++ tailWord_3129587).sum := by decide
  have hdescent : baseEnd_3129587 < baseStart_3129587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129632 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 3, 3]
def baseStart_3129632 : Nat := 118140960795 + 3129632 * 2 ^ 59
def prefixEnd_3129632 : Nat := 4983230072969 + 3 ^ 40 * 3129632 * 2
def baseEnd_3129632 : Nat := 1071336991794669689404727

theorem tailTrace_3129632 : CollatzResearch.WordTrace tailWord_3129632 prefixEnd_3129632 1071336991794669689404727 := by
  unfold tailWord_3129632
  simp only [CollatzResearch.WordTrace]
  refine ⟨57073528298942618718551575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76098037731923491624735433 57073528298942618718551575)
  ·
    refine ⟨85610292448413928077827363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57073528298942618718551575 85610292448413928077827363)
    ·
      refine ⟨128415438672620892116741045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85610292448413928077827363 128415438672620892116741045)
      ·
        refine ⟨12038947375558208635944473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128415438672620892116741045 12038947375558208635944473)
        ·
          refine ⟨9029210531668656476958355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12038947375558208635944473 9029210531668656476958355)
          ·
            refine ⟨13543815797502984715437533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9029210531668656476958355 13543815797502984715437533)
            ·
              refine ⟨5078930924063619268289075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13543815797502984715437533 5078930924063619268289075)
              ·
                refine ⟨7618396386095428902433613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5078930924063619268289075 7618396386095428902433613)
                ·
                  refine ⟨2856898644785785838412605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7618396386095428902433613 2856898644785785838412605)
                  ·
                    refine ⟨1071336991794669689404727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2856898644785785838412605 1071336991794669689404727)
                    ·
                      rfl

theorem cell22_3129632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 3, 3].length) (baseStart_3129632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129632 prefixEnd_3129632 := by exact prefixLift 3129632
  have htrace : WordTrace (prefixWord ++ tailWord_3129632) baseStart_3129632 baseEnd_3129632 := by
    simpa [prefixWord, tailWord_3129632, baseEnd_3129632] using wordTrace_append hprefix tailTrace_3129632
  have hstable : (prefixWord ++ tailWord_3129632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129632).length < 2 ^ (prefixWord ++ tailWord_3129632).sum := by decide
  have hdescent : baseEnd_3129632 < baseStart_3129632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129705 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 1, 5]
def baseStart_3129705 : Nat := 118140960795 + 3129705 * 2 ^ 59
def prefixEnd_3129705 : Nat := 4983230072969 + 3 ^ 40 * 3129705 * 2
def baseEnd_3129705 : Nat := 1071361981186521832329503

theorem tailTrace_3129705 : CollatzResearch.WordTrace tailWord_3129705 prefixEnd_3129705 1071361981186521832329503 := by
  unfold tailWord_3129705
  simp only [CollatzResearch.WordTrace]
  refine ⟨114149719126620770904510569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76099812751080513936340379 114149719126620770904510569)
  ·
    refine ⟨85612289344965578178382927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114149719126620770904510569 85612289344965578178382927)
    ·
      refine ⟨128418434017448367267574391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85612289344965578178382927 128418434017448367267574391)
      ·
        refine ⟨192627651026172550901361587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128418434017448367267574391 192627651026172550901361587)
        ·
          refine ⟨288941476539258826352042381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192627651026172550901361587 288941476539258826352042381)
          ·
            refine ⟨108353053702222059882015893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288941476539258826352042381 108353053702222059882015893)
            ·
              refine ⟨5079049392291659056969495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108353053702222059882015893 5079049392291659056969495)
              ·
                refine ⟨7618574088437488585454243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5079049392291659056969495 7618574088437488585454243)
                ·
                  refine ⟨11427861132656232878181365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7618574088437488585454243 11427861132656232878181365)
                  ·
                    refine ⟨1071361981186521832329503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11427861132656232878181365 1071361981186521832329503)
                    ·
                      rfl

theorem cell22_3129705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_3129705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129705 prefixEnd_3129705 := by exact prefixLift 3129705
  have htrace : WordTrace (prefixWord ++ tailWord_3129705) baseStart_3129705 baseEnd_3129705 := by
    simpa [prefixWord, tailWord_3129705, baseEnd_3129705] using wordTrace_append hprefix tailTrace_3129705
  have hstable : (prefixWord ++ tailWord_3129705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129705).length < 2 ^ (prefixWord ++ tailWord_3129705).sum := by decide
  have hdescent : baseEnd_3129705 < baseStart_3129705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129739 : List Nat := [1, 1, 1, 1, 4, 6, 1, 2, 2, 3]
def baseStart_3129739 : Nat := 118140960795 + 3129739 * 2 ^ 59
def prefixEnd_3129739 : Nat := 4983230072969 + 3 ^ 40 * 3129739 * 2
def baseEnd_3129739 : Nat := 1071373620081357076979399

theorem tailTrace_3129739 : CollatzResearch.WordTrace tailWord_3129739 prefixEnd_3129739 1071373620081357076979399 := by
  unfold tailWord_3129739
  simp only [CollatzResearch.WordTrace]
  refine ⟨114150959208497594711248271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76100639472331729807498847 114150959208497594711248271)
  ·
    refine ⟨171226438812746392066872407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114150959208497594711248271 171226438812746392066872407)
    ·
      refine ⟨256839658219119588100308611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171226438812746392066872407 256839658219119588100308611)
      ·
        refine ⟨385259487328679382150462917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256839658219119588100308611 385259487328679382150462917)
        ·
          refine ⟨72236153874127384153211797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 385259487328679382150462917 72236153874127384153211797)
          ·
            refine ⟨3386069712849721132181803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72236153874127384153211797 3386069712849721132181803)
            ·
              refine ⟨5079104569274581698272705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3386069712849721132181803 5079104569274581698272705)
              ·
                refine ⟨3809328426955936273704529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5079104569274581698272705 3809328426955936273704529)
                ·
                  refine ⟨2856996320216952205278397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3809328426955936273704529 2856996320216952205278397)
                  ·
                    refine ⟨1071373620081357076979399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2856996320216952205278397 1071373620081357076979399)
                    ·
                      rfl

theorem cell22_3129739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 3].length) (baseStart_3129739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129739 prefixEnd_3129739 := by exact prefixLift 3129739
  have htrace : WordTrace (prefixWord ++ tailWord_3129739) baseStart_3129739 baseEnd_3129739 := by
    simpa [prefixWord, tailWord_3129739, baseEnd_3129739] using wordTrace_append hprefix tailTrace_3129739
  have hstable : (prefixWord ++ tailWord_3129739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129739).length < 2 ^ (prefixWord ++ tailWord_3129739).sum := by decide
  have hdescent : baseEnd_3129739 < baseStart_3129739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129814 : List Nat := [5, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_3129814 : Nat := 118140960795 + 3129814 * 2 ^ 59
def prefixEnd_3129814 : Nat := 4983230072969 + 3 ^ 40 * 3129814 * 2
def baseEnd_3129814 : Nat := 357133098038027293784723

theorem tailTrace_3129814 : CollatzResearch.WordTrace tailWord_3129814 prefixEnd_3129814 357133098038027293784723 := by
  unfold tailWord_3129814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7134605917701617657514281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76102463122150588346818997 7134605917701617657514281)
  ·
    refine ⟨5350954438276213243135711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7134605917701617657514281 5350954438276213243135711)
    ·
      refine ⟨8026431657414319864703567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5350954438276213243135711 8026431657414319864703567)
      ·
        refine ⟨12039647486121479797055351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8026431657414319864703567 12039647486121479797055351)
        ·
          refine ⟨18059471229182219695583027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12039647486121479797055351 18059471229182219695583027)
          ·
            refine ⟨27089206843773329543374541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18059471229182219695583027 27089206843773329543374541)
            ·
              refine ⟨10158452566414998578765453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27089206843773329543374541 10158452566414998578765453)
              ·
                refine ⟨3809419712405624467037045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10158452566414998578765453 3809419712405624467037045)
                ·
                  refine ⟨357133098038027293784723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3809419712405624467037045 357133098038027293784723)
                  ·
                    rfl

theorem cell22_3129814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_3129814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129814 prefixEnd_3129814 := by exact prefixLift 3129814
  have htrace : WordTrace (prefixWord ++ tailWord_3129814) baseStart_3129814 baseEnd_3129814 := by
    simpa [prefixWord, tailWord_3129814, baseEnd_3129814] using wordTrace_append hprefix tailTrace_3129814
  have hstable : (prefixWord ++ tailWord_3129814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129814).length < 2 ^ (prefixWord ++ tailWord_3129814).sum := by decide
  have hdescent : baseEnd_3129814 < baseStart_3129814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129825 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 8]
def baseStart_3129825 : Nat := 118140960795 + 3129825 * 2 ^ 59
def prefixEnd_3129825 : Nat := 4983230072969 + 3 ^ 40 * 3129825 * 2
def baseEnd_3129825 : Nat := 357134353212960506443045

theorem tailTrace_3129825 : CollatzResearch.WordTrace tailWord_3129825 prefixEnd_3129825 357134353212960506443045 := by
  unfold tailWord_3129825
  simp only [CollatzResearch.WordTrace]
  refine ⟨114154095886186031398878929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76102730590790687599252619 114154095886186031398878929)
  ·
    refine ⟨85615571914639523549159197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114154095886186031398878929 85615571914639523549159197)
    ·
      refine ⟨32105839467989821330934699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85615571914639523549159197 32105839467989821330934699)
      ·
        refine ⟨48158759201984731996402049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32105839467989821330934699 48158759201984731996402049)
        ·
          refine ⟨36119069401488548997301537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48158759201984731996402049 36119069401488548997301537)
          ·
            refine ⟨27089302051116411747976153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36119069401488548997301537 27089302051116411747976153)
            ·
              refine ⟨20316976538337308810982115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27089302051116411747976153 20316976538337308810982115)
              ·
                refine ⟨30475464807505963216473173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20316976538337308810982115 30475464807505963216473173)
                ·
                  refine ⟨357134353212960506443045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30475464807505963216473173 357134353212960506443045)
                  ·
                    rfl

theorem cell22_3129825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 8].length) (baseStart_3129825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129825 prefixEnd_3129825 := by exact prefixLift 3129825
  have htrace : WordTrace (prefixWord ++ tailWord_3129825) baseStart_3129825 baseEnd_3129825 := by
    simpa [prefixWord, tailWord_3129825, baseEnd_3129825] using wordTrace_append hprefix tailTrace_3129825
  have hstable : (prefixWord ++ tailWord_3129825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129825).length < 2 ^ (prefixWord ++ tailWord_3129825).sum := by decide
  have hdescent : baseEnd_3129825 < baseStart_3129825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129895 : List Nat := [1, 1, 7, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3129895 : Nat := 118140960795 + 3129895 * 2 ^ 59
def prefixEnd_3129895 : Nat := 4983230072969 + 3 ^ 40 * 3129895 * 2
def baseEnd_3129895 : Nat := 1071427022069424670078921

theorem tailTrace_3129895 : CollatzResearch.WordTrace tailWord_3129895 prefixEnd_3129895 1071427022069424670078921 := by
  unfold tailWord_3129895
  simp only [CollatzResearch.WordTrace]
  refine ⟨114156648995932433353927139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76104432663954955569284759 114156648995932433353927139)
  ·
    refine ⟨171234973493898650030890709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114156648995932433353927139 171234973493898650030890709)
    ·
      refine ⟨4013319691263249610099001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 171234973493898650030890709 4013319691263249610099001)
      ·
        refine ⟨3009989768447437207574251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4013319691263249610099001 3009989768447437207574251)
        ·
          refine ⟨4514984652671155811361377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3009989768447437207574251 4514984652671155811361377)
          ·
            refine ⟨3386238489503366858521033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4514984652671155811361377 3386238489503366858521033)
            ·
              refine ⟨2539678867127525143890775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3386238489503366858521033 2539678867127525143890775)
              ·
                refine ⟨3809518300691287715836163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2539678867127525143890775 3809518300691287715836163)
                ·
                  refine ⟨5714277451036931573754245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3809518300691287715836163 5714277451036931573754245)
                  ·
                    refine ⟨1071427022069424670078921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5714277451036931573754245 1071427022069424670078921)
                    ·
                      rfl

theorem cell22_3129895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3129895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129895 prefixEnd_3129895 := by exact prefixLift 3129895
  have htrace : WordTrace (prefixWord ++ tailWord_3129895) baseStart_3129895 baseEnd_3129895 := by
    simpa [prefixWord, tailWord_3129895, baseEnd_3129895] using wordTrace_append hprefix tailTrace_3129895
  have hstable : (prefixWord ++ tailWord_3129895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129895).length < 2 ^ (prefixWord ++ tailWord_3129895).sum := by decide
  have hdescent : baseEnd_3129895 < baseStart_3129895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129908 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_3129908 : Nat := 118140960795 + 3129908 * 2 ^ 59
def prefixEnd_3129908 : Nat := 4983230072969 + 3 ^ 40 * 3129908 * 2
def baseEnd_3129908 : Nat := 1071431472235096969503881

theorem tailTrace_3129908 : CollatzResearch.WordTrace tailWord_3129908 prefixEnd_3129908 1071431472235096969503881 := by
  unfold tailWord_3129908
  simp only [CollatzResearch.WordTrace]
  refine ⟨57078561572442668287075189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76104748763256891049433585 57078561572442668287075189)
  ·
    refine ⟨5351115147416500151913299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57078561572442668287075189 5351115147416500151913299)
    ·
      refine ⟨8026672721124750227869949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5351115147416500151913299 8026672721124750227869949)
      ·
        refine ⟨3010002270421781335451231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8026672721124750227869949 3010002270421781335451231)
        ·
          refine ⟨4515003405632672003176847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3010002270421781335451231 4515003405632672003176847)
          ·
            refine ⟨6772505108449008004765271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4515003405632672003176847 6772505108449008004765271)
            ·
              refine ⟨10158757662673512007147907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6772505108449008004765271 10158757662673512007147907)
              ·
                refine ⟨15238136494010268010721861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10158757662673512007147907 15238136494010268010721861)
                ·
                  refine ⟨2857150592626925252010349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15238136494010268010721861 2857150592626925252010349)
                  ·
                    refine ⟨1071431472235096969503881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2857150592626925252010349 1071431472235096969503881)
                    ·
                      rfl

theorem cell22_3129908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_3129908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129908 prefixEnd_3129908 := by exact prefixLift 3129908
  have htrace : WordTrace (prefixWord ++ tailWord_3129908) baseStart_3129908 baseEnd_3129908 := by
    simpa [prefixWord, tailWord_3129908, baseEnd_3129908] using wordTrace_append hprefix tailTrace_3129908
  have hstable : (prefixWord ++ tailWord_3129908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129908).length < 2 ^ (prefixWord ++ tailWord_3129908).sum := by decide
  have hdescent : baseEnd_3129908 < baseStart_3129908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129919 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 3, 3]
def baseStart_3129919 : Nat := 118140960795 + 3129919 * 2 ^ 59
def prefixEnd_3129919 : Nat := 4983230072969 + 3 ^ 40 * 3129919 * 2
def baseEnd_3129919 : Nat := 1071435237759896607478847

theorem tailTrace_3129919 : CollatzResearch.WordTrace tailWord_3129919 prefixEnd_3129919 1071435237759896607478847 := by
  unfold tailWord_3129919
  simp only [CollatzResearch.WordTrace]
  refine ⟨114157524347845485452800811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76105016231896990301867207 114157524347845485452800811)
  ·
    refine ⟨171236286521768228179201217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114157524347845485452800811 171236286521768228179201217)
    ·
      refine ⟨128427214891326171134400913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171236286521768228179201217 128427214891326171134400913)
      ·
        refine ⟨96320411168494628350800685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128427214891326171134400913 96320411168494628350800685)
        ·
          refine ⟨36120154188185485631550257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96320411168494628350800685 36120154188185485631550257)
          ·
            refine ⟨27090115641139114223662693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36120154188185485631550257 27090115641139114223662693)
            ·
              refine ⟨5079396682713583916936755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27090115641139114223662693 5079396682713583916936755)
              ·
                refine ⟨7619095024070375875405133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5079396682713583916936755 7619095024070375875405133)
                ·
                  refine ⟨2857160634026390953276925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7619095024070375875405133 2857160634026390953276925)
                  ·
                    refine ⟨1071435237759896607478847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2857160634026390953276925 1071435237759896607478847)
                    ·
                      rfl

theorem cell22_3129919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 3].length) (baseStart_3129919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129919 prefixEnd_3129919 := by exact prefixLift 3129919
  have htrace : WordTrace (prefixWord ++ tailWord_3129919) baseStart_3129919 baseEnd_3129919 := by
    simpa [prefixWord, tailWord_3129919, baseEnd_3129919] using wordTrace_append hprefix tailTrace_3129919
  have hstable : (prefixWord ++ tailWord_3129919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129919).length < 2 ^ (prefixWord ++ tailWord_3129919).sum := by decide
  have hdescent : baseEnd_3129919 < baseStart_3129919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129953 : List Nat := [1, 2, 3, 1, 1, 6, 1, 3, 1, 3]
def baseStart_3129953 : Nat := 118140960795 + 3129953 * 2 ^ 59
def prefixEnd_3129953 : Nat := 4983230072969 + 3 ^ 40 * 3129953 * 2
def baseEnd_3129953 : Nat := 1071446876654731852128743

theorem tailTrace_3129953 : CollatzResearch.WordTrace tailWord_3129953 prefixEnd_3129953 1071446876654731852128743 := by
  unfold tailWord_3129953
  simp only [CollatzResearch.WordTrace]
  refine ⟨114158764429722309259538513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76105842953148206173025675 114158764429722309259538513)
  ·
    refine ⟨85619073322291731944653885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114158764429722309259538513 85619073322291731944653885)
    ·
      refine ⟨32107152495859399479245207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85619073322291731944653885 32107152495859399479245207)
      ·
        refine ⟨48160728743789099218867811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32107152495859399479245207 48160728743789099218867811)
        ·
          refine ⟨72241093115683648828301717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48160728743789099218867811 72241093115683648828301717)
          ·
            refine ⟨3386301239797671038826643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72241093115683648828301717 3386301239797671038826643)
            ·
              refine ⟨5079451859696506558239965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3386301239797671038826643 5079451859696506558239965)
              ·
                refine ⟨1904794447386189959339987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5079451859696506558239965 1904794447386189959339987)
                ·
                  refine ⟨2857191671079284939009981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1904794447386189959339987 2857191671079284939009981)
                  ·
                    refine ⟨1071446876654731852128743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2857191671079284939009981 1071446876654731852128743)
                    ·
                      rfl

theorem cell22_3129953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_3129953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129953 prefixEnd_3129953 := by exact prefixLift 3129953
  have htrace : WordTrace (prefixWord ++ tailWord_3129953) baseStart_3129953 baseEnd_3129953 := by
    simpa [prefixWord, tailWord_3129953, baseEnd_3129953] using wordTrace_append hprefix tailTrace_3129953
  have hstable : (prefixWord ++ tailWord_3129953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129953).length < 2 ^ (prefixWord ++ tailWord_3129953).sum := by decide
  have hdescent : baseEnd_3129953 < baseStart_3129953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3129970 : List Nat := [3, 2, 1, 2, 4, 1, 3, 2, 1, 3]
def baseStart_3129970 : Nat := 118140960795 + 3129970 * 2 ^ 59
def prefixEnd_3129970 : Nat := 4983230072969 + 3 ^ 40 * 3129970 * 2
def baseEnd_3129970 : Nat := 1071452696102149474453691

theorem tailTrace_3129970 : CollatzResearch.WordTrace tailWord_3129970 prefixEnd_3129970 1071452696102149474453691 := by
  unfold tailWord_3129970
  simp only [CollatzResearch.WordTrace]
  refine ⟨28539846117665180290726841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76106256313773814108604909 28539846117665180290726841)
  ·
    refine ⟨21404884588248885218045131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28539846117665180290726841 21404884588248885218045131)
    ·
      refine ⟨32107326882373327827067697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21404884588248885218045131 32107326882373327827067697)
      ·
        refine ⟨24080495161779995870300773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32107326882373327827067697 24080495161779995870300773)
        ·
          refine ⟨4515092842833749225681395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24080495161779995870300773 4515092842833749225681395)
          ·
            refine ⟨6772639264250623838522093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4515092842833749225681395 6772639264250623838522093)
            ·
              refine ⟨2539739724093983939445785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6772639264250623838522093 2539739724093983939445785)
              ·
                refine ⟨1904804793070487954584339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2539739724093983939445785 1904804793070487954584339)
                ·
                  refine ⟨2857207189605731931876509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1904804793070487954584339 2857207189605731931876509)
                  ·
                    refine ⟨1071452696102149474453691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2857207189605731931876509 1071452696102149474453691)
                    ·
                      rfl

theorem cell22_3129970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_3129970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3129970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3129970 prefixEnd_3129970 := by exact prefixLift 3129970
  have htrace : WordTrace (prefixWord ++ tailWord_3129970) baseStart_3129970 baseEnd_3129970 := by
    simpa [prefixWord, tailWord_3129970, baseEnd_3129970] using wordTrace_append hprefix tailTrace_3129970
  have hstable : (prefixWord ++ tailWord_3129970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3129970).length < 2 ^ (prefixWord ++ tailWord_3129970).sum := by decide
  have hdescent : baseEnd_3129970 < baseStart_3129970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3129970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130084 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 7]
def baseStart_3130084 : Nat := 118140960795 + 3130084 * 2 ^ 59
def prefixEnd_3130084 : Nat := 4983230072969 + 3 ^ 40 * 3130084 * 2
def baseEnd_3130084 : Nat := 357163906877297059034447

theorem tailTrace_3130084 : CollatzResearch.WordTrace tailWord_3130084 prefixEnd_3130084 357163906877297059034447 := by
  unfold tailWord_3130084
  simp only [CollatzResearch.WordTrace]
  refine ⟨57081771196123859316278653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76109028261498479088371537 57081771196123859316278653)
  ·
    refine ⟨21405664198546447243604495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57081771196123859316278653 21405664198546447243604495)
    ·
      refine ⟨32108496297819670865406743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21405664198546447243604495 32108496297819670865406743)
      ·
        refine ⟨48162744446729506298110115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32108496297819670865406743 48162744446729506298110115)
        ·
          refine ⟨72244116670094259447165173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48162744446729506298110115 72244116670094259447165173)
          ·
            refine ⟨6772885937821336823171735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72244116670094259447165173 6772885937821336823171735)
            ·
              refine ⟨10159328906732005234757603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6772885937821336823171735 10159328906732005234757603)
              ·
                refine ⟨15238993360098007852136405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10159328906732005234757603 15238993360098007852136405)
                ·
                  refine ⟨357163906877297059034447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15238993360098007852136405 357163906877297059034447)
                  ·
                    rfl

theorem cell22_3130084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_3130084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130084 prefixEnd_3130084 := by exact prefixLift 3130084
  have htrace : WordTrace (prefixWord ++ tailWord_3130084) baseStart_3130084 baseEnd_3130084 := by
    simpa [prefixWord, tailWord_3130084, baseEnd_3130084] using wordTrace_append hprefix tailTrace_3130084
  have hstable : (prefixWord ++ tailWord_3130084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130084).length < 2 ^ (prefixWord ++ tailWord_3130084).sum := by decide
  have hdescent : baseEnd_3130084 < baseStart_3130084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130088 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 3, 3]
def baseStart_3130088 : Nat := 118140960795 + 3130088 * 2 ^ 59
def prefixEnd_3130088 : Nat := 4983230072969 + 3 ^ 40 * 3130088 * 2
def baseEnd_3130088 : Nat := 1071493089913636500003329

theorem tailTrace_3130088 : CollatzResearch.WordTrace tailWord_3130088 prefixEnd_3130088 1071493089913636500003329 := by
  unfold tailWord_3130088
  simp only [CollatzResearch.WordTrace]
  refine ⟨57081844142116613657851459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76109125522822151543801945 57081844142116613657851459)
  ·
    refine ⟨85622766213174920486777189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57081844142116613657851459 85622766213174920486777189)
    ·
      refine ⟨16054268664970297591270723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85622766213174920486777189 16054268664970297591270723)
      ·
        refine ⟨24081402997455446386906085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16054268664970297591270723 24081402997455446386906085)
        ·
          refine ⟨4515263062022896197544891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24081402997455446386906085 4515263062022896197544891)
          ·
            refine ⟨6772894593034344296317337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4515263062022896197544891 6772894593034344296317337)
            ·
              refine ⟨5079670944775758222238003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6772894593034344296317337 5079670944775758222238003)
              ·
                refine ⟨7619506417163637333357005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5079670944775758222238003 7619506417163637333357005)
                ·
                  refine ⟨2857314906436364000008877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7619506417163637333357005 2857314906436364000008877)
                  ·
                    refine ⟨1071493089913636500003329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2857314906436364000008877 1071493089913636500003329)
                    ·
                      rfl

theorem cell22_3130088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_3130088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130088 prefixEnd_3130088 := by exact prefixLift 3130088
  have htrace : WordTrace (prefixWord ++ tailWord_3130088) baseStart_3130088 baseEnd_3130088 := by
    simpa [prefixWord, tailWord_3130088, baseEnd_3130088] using wordTrace_append hprefix tailTrace_3130088
  have hstable : (prefixWord ++ tailWord_3130088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130088).length < 2 ^ (prefixWord ++ tailWord_3130088).sum := by decide
  have hdescent : baseEnd_3130088 < baseStart_3130088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130146 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 6]
def baseStart_3130146 : Nat := 118140960795 + 3130146 * 2 ^ 59
def prefixEnd_3130146 : Nat := 4983230072969 + 3 ^ 40 * 3130146 * 2
def baseEnd_3130146 : Nat := 357170981499647894017717

theorem tailTrace_3130146 : CollatzResearch.WordTrace tailWord_3130146 prefixEnd_3130146 357170981499647894017717 := by
  unfold tailWord_3130146
  simp only [CollatzResearch.WordTrace]
  refine ⟨28541450929505775805328573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76110535812015402147542861 28541450929505775805328573)
  ·
    refine ⟨10703044098564665926998215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28541450929505775805328573 10703044098564665926998215)
    ·
      refine ⟨16054566147846998890497323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10703044098564665926998215 16054566147846998890497323)
      ·
        refine ⟨24081849221770498335745985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16054566147846998890497323 24081849221770498335745985)
        ·
          refine ⟨18061386916327873751809489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24081849221770498335745985 18061386916327873751809489)
          ·
            refine ⟨13546040187245905313857117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18061386916327873751809489 13546040187245905313857117)
            ·
              refine ⟨5079765070217214492696419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13546040187245905313857117 5079765070217214492696419)
              ·
                refine ⟨7619647605325821739044629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5079765070217214492696419 7619647605325821739044629)
                ·
                  refine ⟨357170981499647894017717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7619647605325821739044629 357170981499647894017717)
                  ·
                    rfl

theorem cell22_3130146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_3130146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130146 prefixEnd_3130146 := by exact prefixLift 3130146
  have htrace : WordTrace (prefixWord ++ tailWord_3130146) baseStart_3130146 baseEnd_3130146 := by
    simpa [prefixWord, tailWord_3130146, baseEnd_3130146] using wordTrace_append hprefix tailTrace_3130146
  have hstable : (prefixWord ++ tailWord_3130146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130146).length < 2 ^ (prefixWord ++ tailWord_3130146).sum := by decide
  have hdescent : baseEnd_3130146 < baseStart_3130146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130234 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 3, 7]
def baseStart_3130234 : Nat := 118140960795 + 3130234 * 2 ^ 59
def prefixEnd_3130234 : Nat := 4983230072969 + 3 ^ 40 * 3130234 * 2
def baseEnd_3130234 : Nat := 1071543068697340785852881

theorem tailTrace_3130234 : CollatzResearch.WordTrace tailWord_3130234 prefixEnd_3130234 1071543068697340785852881 := by
  unfold tailWord_3130234
  simp only [CollatzResearch.WordTrace]
  refine ⟨28542253335426073562629439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76112675561136196167011837 28542253335426073562629439)
  ·
    refine ⟨42813380003139110343944159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28542253335426073562629439 42813380003139110343944159)
    ·
      refine ⟨64220070004708665515916239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42813380003139110343944159 64220070004708665515916239)
      ·
        refine ⟨96330105007062998273874359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64220070004708665515916239 96330105007062998273874359)
        ·
          refine ⟨144495157510594497410811539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96330105007062998273874359 144495157510594497410811539)
          ·
            refine ⟨216742736265891746116217309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144495157510594497410811539 216742736265891746116217309)
            ·
              refine ⟨81278526099709404793581491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216742736265891746116217309 81278526099709404793581491)
              ·
                refine ⟨121917789149564107190372237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81278526099709404793581491 121917789149564107190372237)
                ·
                  refine ⟨45719170931086540196389589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121917789149564107190372237 45719170931086540196389589)
                  ·
                    refine ⟨1071543068697340785852881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45719170931086540196389589 1071543068697340785852881)
                    ·
                      rfl

theorem cell22_3130234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_3130234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130234 prefixEnd_3130234 := by exact prefixLift 3130234
  have htrace : WordTrace (prefixWord ++ tailWord_3130234) baseStart_3130234 baseEnd_3130234 := by
    simpa [prefixWord, tailWord_3130234, baseEnd_3130234] using wordTrace_append hprefix tailTrace_3130234
  have hstable : (prefixWord ++ tailWord_3130234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130234).length < 2 ^ (prefixWord ++ tailWord_3130234).sum := by decide
  have hdescent : baseEnd_3130234 < baseStart_3130234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130311 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 4, 4]
def baseStart_3130311 : Nat := 118140960795 + 3130311 * 2 ^ 59
def prefixEnd_3130311 : Nat := 4983230072969 + 3 ^ 40 * 3130311 * 2
def baseEnd_3130311 : Nat := 1071569427370938251677645

theorem tailTrace_3130311 : CollatzResearch.WordTrace tailWord_3130311 prefixEnd_3130311 1071569427370938251677645 := by
  unfold tailWord_3130311
  simp only [CollatzResearch.WordTrace]
  refine ⟨114171821762425336401070787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76114547841616890934047191 114171821762425336401070787)
  ·
    refine ⟨171257732643638004601606181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114171821762425336401070787 171257732643638004601606181)
    ·
      refine ⟨32110824870682125862801159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171257732643638004601606181 32110824870682125862801159)
      ·
        refine ⟨48166237306023188794201739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32110824870682125862801159 48166237306023188794201739)
        ·
          refine ⟨72249355959034783191302609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48166237306023188794201739 72249355959034783191302609)
          ·
            refine ⟨54187016969276087393476957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72249355959034783191302609 54187016969276087393476957)
            ·
              refine ⟨20320131363478532772553859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54187016969276087393476957 20320131363478532772553859)
              ·
                refine ⟨30480197045217799158830789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20320131363478532772553859 30480197045217799158830789)
                ·
                  refine ⟨5715036945978337342280773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30480197045217799158830789 5715036945978337342280773)
                  ·
                    refine ⟨1071569427370938251677645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5715036945978337342280773 1071569427370938251677645)
                    ·
                      rfl

theorem cell22_3130311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_3130311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130311 prefixEnd_3130311 := by exact prefixLift 3130311
  have htrace : WordTrace (prefixWord ++ tailWord_3130311) baseStart_3130311 baseEnd_3130311 := by
    simpa [prefixWord, tailWord_3130311, baseEnd_3130311] using wordTrace_append hprefix tailTrace_3130311
  have hstable : (prefixWord ++ tailWord_3130311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130311).length < 2 ^ (prefixWord ++ tailWord_3130311).sum := by decide
  have hdescent : baseEnd_3130311 < baseStart_3130311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130315 : List Nat := [1, 1, 1, 1, 3, 6, 3, 2, 4]
def baseStart_3130315 : Nat := 118140960795 + 3130315 * 2 ^ 59
def prefixEnd_3130315 : Nat := 4983230072969 + 3 ^ 40 * 3130315 * 2
def baseEnd_3130315 : Nat := 357190265550894524859211

theorem tailTrace_3130315 : CollatzResearch.WordTrace tailWord_3130315 prefixEnd_3130315 357190265550894524859211 := by
  unfold tailWord_3130315
  simp only [CollatzResearch.WordTrace]
  refine ⟨114171967654410845084216399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76114645102940563389477599 114171967654410845084216399)
  ·
    refine ⟨171257951481616267626324599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114171967654410845084216399 171257951481616267626324599)
    ·
      refine ⟨256886927222424401439486899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171257951481616267626324599 256886927222424401439486899)
      ·
        refine ⟨385330390833636602159230349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256886927222424401439486899 385330390833636602159230349)
        ·
          refine ⟨144498896562613725809711381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385330390833636602159230349 144498896562613725809711381)
          ·
            refine ⟨6773385776372518397330221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 144498896562613725809711381 6773385776372518397330221)
            ·
              refine ⟨2540019666139694398998833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6773385776372518397330221 2540019666139694398998833)
              ·
                refine ⟨1905014749604770799249125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2540019666139694398998833 1905014749604770799249125)
                ·
                  refine ⟨357190265550894524859211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1905014749604770799249125 357190265550894524859211)
                  ·
                    rfl

theorem cell22_3130315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 4].length) (baseStart_3130315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130315 prefixEnd_3130315 := by exact prefixLift 3130315
  have htrace : WordTrace (prefixWord ++ tailWord_3130315) baseStart_3130315 baseEnd_3130315 := by
    simpa [prefixWord, tailWord_3130315, baseEnd_3130315] using wordTrace_append hprefix tailTrace_3130315
  have hstable : (prefixWord ++ tailWord_3130315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130315).length < 2 ^ (prefixWord ++ tailWord_3130315).sum := by decide
  have hdescent : baseEnd_3130315 < baseStart_3130315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130330 : List Nat := [3, 1, 1, 2, 4, 2, 1, 3, 2, 3]
def baseStart_3130330 : Nat := 118140960795 + 3130330 * 2 ^ 59
def prefixEnd_3130330 : Nat := 4983230072969 + 3 ^ 40 * 3130330 * 2
def baseEnd_3130330 : Nat := 1071575931459228535452587

theorem tailTrace_3130330 : CollatzResearch.WordTrace tailWord_3130330 prefixEnd_3130330 1071575931459228535452587 := by
  unfold tailWord_3130330
  simp only [CollatzResearch.WordTrace]
  refine ⟨28543128687339125661503111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76115009832904335097341629 28543128687339125661503111)
  ·
    refine ⟨42814693031008688492254667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28543128687339125661503111 42814693031008688492254667)
    ·
      refine ⟨64222039546513032738382001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42814693031008688492254667 64222039546513032738382001)
      ·
        refine ⟨48166529659884774553786501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64222039546513032738382001 48166529659884774553786501)
        ·
          refine ⟨9031224311228395228834969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48166529659884774553786501 9031224311228395228834969)
          ·
            refine ⟨6773418233421296421626227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9031224311228395228834969 6773418233421296421626227)
            ·
              refine ⟨10160127350131944632439341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6773418233421296421626227 10160127350131944632439341)
              ·
                refine ⟨3810047756299479237164753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10160127350131944632439341 3810047756299479237164753)
                ·
                  refine ⟨2857535817224609427873565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3810047756299479237164753 2857535817224609427873565)
                  ·
                    refine ⟨1071575931459228535452587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2857535817224609427873565 1071575931459228535452587)
                    ·
                      rfl

theorem cell22_3130330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_3130330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130330 prefixEnd_3130330 := by exact prefixLift 3130330
  have htrace : WordTrace (prefixWord ++ tailWord_3130330) baseStart_3130330 baseEnd_3130330 := by
    simpa [prefixWord, tailWord_3130330, baseEnd_3130330] using wordTrace_append hprefix tailTrace_3130330
  have hstable : (prefixWord ++ tailWord_3130330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130330).length < 2 ^ (prefixWord ++ tailWord_3130330).sum := by decide
  have hdescent : baseEnd_3130330 < baseStart_3130330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130366 : List Nat := [4, 2, 2, 2, 3, 1, 2, 2, 4]
def baseStart_3130366 : Nat := 118140960795 + 3130366 * 2 ^ 59
def prefixEnd_3130366 : Nat := 4983230072969 + 3 ^ 40 * 3130366 * 2
def baseEnd_3130366 : Nat := 357196084998312147184159

theorem tailTrace_3130366 : CollatzResearch.WordTrace tailWord_3130366 prefixEnd_3130366 357196084998312147184159 := by
  unfold tailWord_3130366
  simp only [CollatzResearch.WordTrace]
  refine ⟨14271728472153260099290369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76115885184817387196215301 14271728472153260099290369)
  ·
    refine ⟨10703796354114945074467777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14271728472153260099290369 10703796354114945074467777)
    ·
      refine ⟨8027847265586208805850833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10703796354114945074467777 8027847265586208805850833)
      ·
        refine ⟨6020885449189656604388125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8027847265586208805850833 6020885449189656604388125)
        ·
          refine ⟨2257832043446121226645547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6020885449189656604388125 2257832043446121226645547)
          ·
            refine ⟨3386748065169181839968321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2257832043446121226645547 3386748065169181839968321)
            ·
              refine ⟨2540061048876886379976241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3386748065169181839968321 2540061048876886379976241)
              ·
                refine ⟨1905045786657664784982181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2540061048876886379976241 1905045786657664784982181)
                ·
                  refine ⟨357196084998312147184159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1905045786657664784982181 357196084998312147184159)
                  ·
                    rfl

theorem cell22_3130366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_3130366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130366 prefixEnd_3130366 := by exact prefixLift 3130366
  have htrace : WordTrace (prefixWord ++ tailWord_3130366) baseStart_3130366 baseEnd_3130366 := by
    simpa [prefixWord, tailWord_3130366, baseEnd_3130366] using wordTrace_append hprefix tailTrace_3130366
  have hstable : (prefixWord ++ tailWord_3130366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130366).length < 2 ^ (prefixWord ++ tailWord_3130366).sum := by decide
  have hdescent : baseEnd_3130366 < baseStart_3130366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130416 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 8]
def baseStart_3130416 : Nat := 118140960795 + 3130416 * 2 ^ 59
def prefixEnd_3130416 : Nat := 4983230072969 + 3 ^ 40 * 3130416 * 2
def baseEnd_3130416 : Nat := 357201790338917659267441

theorem tailTrace_3130416 : CollatzResearch.WordTrace tailWord_3130416 prefixEnd_3130416 357201790338917659267441 := by
  unfold tailWord_3130416
  simp only [CollatzResearch.WordTrace]
  refine ⟨57087825713522469666821551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76117100951363292889095401 57087825713522469666821551)
  ·
    refine ⟨85631738570283704500232327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57087825713522469666821551 85631738570283704500232327)
    ·
      refine ⟨128447607855425556750348491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85631738570283704500232327 128447607855425556750348491)
      ·
        refine ⟨192671411783138335125522737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128447607855425556750348491 192671411783138335125522737)
        ·
          refine ⟨144503558837353751344142053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192671411783138335125522737 144503558837353751344142053)
          ·
            refine ⟨27094417282003828377026635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144503558837353751344142053 27094417282003828377026635)
            ·
              refine ⟨40641625923005742565539953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27094417282003828377026635 40641625923005742565539953)
              ·
                refine ⟨30481219442254306924154965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40641625923005742565539953 30481219442254306924154965)
                ·
                  refine ⟨357201790338917659267441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30481219442254306924154965 357201790338917659267441)
                  ·
                    rfl

theorem cell22_3130416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 8].length) (baseStart_3130416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130416 prefixEnd_3130416 := by exact prefixLift 3130416
  have htrace : WordTrace (prefixWord ++ tailWord_3130416) baseStart_3130416 baseEnd_3130416 := by
    simpa [prefixWord, tailWord_3130416, baseEnd_3130416] using wordTrace_append hprefix tailTrace_3130416
  have hstable : (prefixWord ++ tailWord_3130416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130416).length < 2 ^ (prefixWord ++ tailWord_3130416).sum := by decide
  have hdescent : baseEnd_3130416 < baseStart_3130416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130420 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_3130420 : Nat := 118140960795 + 3130420 * 2 ^ 59
def prefixEnd_3130420 : Nat := 4983230072969 + 3 ^ 40 * 3130420 * 2
def baseEnd_3130420 : Nat := 1071606740298498300702311

theorem tailTrace_3130420 : CollatzResearch.WordTrace tailWord_3130420 prefixEnd_3130420 1071606740298498300702311 := by
  unfold tailWord_3130420
  simp only [CollatzResearch.WordTrace]
  refine ⟨57087898659515224008394357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76117198212686965344525809 57087898659515224008394357)
  ·
    refine ⟨5351990499329552250786971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57087898659515224008394357 5351990499329552250786971)
    ·
      refine ⟨8027985748994328376180457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5351990499329552250786971 8027985748994328376180457)
      ·
        refine ⟨6020989311745746282135343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8027985748994328376180457 6020989311745746282135343)
        ·
          refine ⟨9031483967618619423203015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6020989311745746282135343 9031483967618619423203015)
          ·
            refine ⟨13547225951427929134804523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9031483967618619423203015 13547225951427929134804523)
            ·
              refine ⟨20320838927141893702206785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13547225951427929134804523 20320838927141893702206785)
              ·
                refine ⟨15240629195356420276655089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20320838927141893702206785 15240629195356420276655089)
                ·
                  refine ⟨11430471896517315207491317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15240629195356420276655089 11430471896517315207491317)
                  ·
                    refine ⟨1071606740298498300702311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11430471896517315207491317 1071606740298498300702311)
                    ·
                      rfl

theorem cell22_3130420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_3130420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130420 prefixEnd_3130420 := by exact prefixLift 3130420
  have htrace : WordTrace (prefixWord ++ tailWord_3130420) baseStart_3130420 baseEnd_3130420 := by
    simpa [prefixWord, tailWord_3130420, baseEnd_3130420] using wordTrace_append hprefix tailTrace_3130420
  have hstable : (prefixWord ++ tailWord_3130420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130420).length < 2 ^ (prefixWord ++ tailWord_3130420).sum := by decide
  have hdescent : baseEnd_3130420 < baseStart_3130420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130422 : List Nat := [5, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_3130422 : Nat := 118140960795 + 3130422 * 2 ^ 59
def prefixEnd_3130422 : Nat := 4983230072969 + 3 ^ 40 * 3130422 * 2
def baseEnd_3130422 : Nat := 357202474979790320717435

theorem tailTrace_3130422 : CollatzResearch.WordTrace tailWord_3130422 prefixEnd_3130422 357202474979790320717435 := by
  unfold tailWord_3130422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7135991891563950147397595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76117246843348801572241013 7135991891563950147397595)
  ·
    refine ⟨10703987837345925221096393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7135991891563950147397595 10703987837345925221096393)
    ·
      refine ⟨8027990878009443915822295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10703987837345925221096393 8027990878009443915822295)
      ·
        refine ⟨12041986317014165873733443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8027990878009443915822295 12041986317014165873733443)
        ·
          refine ⟨18062979475521248810600165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12041986317014165873733443 18062979475521248810600165)
          ·
            refine ⟨3386808651660234151987531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18062979475521248810600165 3386808651660234151987531)
            ·
              refine ⟨5080212977490351227981297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3386808651660234151987531 5080212977490351227981297)
              ·
                refine ⟨3810159733117763420985973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5080212977490351227981297 3810159733117763420985973)
                ·
                  refine ⟨357202474979790320717435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3810159733117763420985973 357202474979790320717435)
                  ·
                    rfl

theorem cell22_3130422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_3130422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130422 prefixEnd_3130422 := by exact prefixLift 3130422
  have htrace : WordTrace (prefixWord ++ tailWord_3130422) baseStart_3130422 baseEnd_3130422 := by
    simpa [prefixWord, tailWord_3130422, baseEnd_3130422] using wordTrace_append hprefix tailTrace_3130422
  have hstable : (prefixWord ++ tailWord_3130422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130422).length < 2 ^ (prefixWord ++ tailWord_3130422).sum := by decide
  have hdescent : baseEnd_3130422 < baseStart_3130422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130463 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 2, 4]
def baseStart_3130463 : Nat := 118140960795 + 3130463 * 2 ^ 59
def prefixEnd_3130463 : Nat := 4983230072969 + 3 ^ 40 * 3130463 * 2
def baseEnd_3130463 : Nat := 1071621460077260521877179

theorem tailTrace_3130463 : CollatzResearch.WordTrace tailWord_3130463 prefixEnd_3130463 1071621460077260521877179 := by
  unfold tailWord_3130463
  simp only [CollatzResearch.WordTrace]
  refine ⟨114177365657874666360604043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76118243771916444240402695 114177365657874666360604043)
  ·
    refine ⟨171266048486811999540906065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114177365657874666360604043 171266048486811999540906065)
    ·
      refine ⟨128449536365108999655679549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171266048486811999540906065 128449536365108999655679549)
      ·
        refine ⟨48168576136915874870879831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128449536365108999655679549 48168576136915874870879831)
        ·
          refine ⟨72252864205373812306319747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48168576136915874870879831 72252864205373812306319747)
          ·
            refine ⟨108379296308060718459479621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72252864205373812306319747 108379296308060718459479621)
            ·
              refine ⟨20321118057761384711152429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108379296308060718459479621 20321118057761384711152429)
              ·
                refine ⟨7620419271660519266682161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20321118057761384711152429 7620419271660519266682161)
                ·
                  refine ⟨5715314453745389450011621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7620419271660519266682161 5715314453745389450011621)
                  ·
                    refine ⟨1071621460077260521877179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5715314453745389450011621 1071621460077260521877179)
                    ·
                      rfl

theorem cell22_3130463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_3130463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130463 prefixEnd_3130463 := by exact prefixLift 3130463
  have htrace : WordTrace (prefixWord ++ tailWord_3130463) baseStart_3130463 baseEnd_3130463 := by
    simpa [prefixWord, tailWord_3130463, baseEnd_3130463] using wordTrace_append hprefix tailTrace_3130463
  have hstable : (prefixWord ++ tailWord_3130463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130463).length < 2 ^ (prefixWord ++ tailWord_3130463).sum := by decide
  have hdescent : baseEnd_3130463 < baseStart_3130463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130478 : List Nat := [4, 1, 2, 2, 1, 2, 10]
def baseStart_3130478 : Nat := 118140960795 + 3130478 * 2 ^ 59
def prefixEnd_3130478 : Nat := 4983230072969 + 3 ^ 40 * 3130478 * 2
def baseEnd_3130478 : Nat := 39689873884585388250079

theorem tailTrace_3130478 : CollatzResearch.WordTrace tailWord_3130478 prefixEnd_3130478 39689873884585388250079 := by
  unfold tailWord_3130478
  simp only [CollatzResearch.WordTrace]
  refine ⟨14272239094102540490300011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76118608501880215948266725 14272239094102540490300011)
  ·
    refine ⟨21408358641153810735450017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14272239094102540490300011 21408358641153810735450017)
    ·
      refine ⟨16056268980865358051587513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21408358641153810735450017 16056268980865358051587513)
      ·
        refine ⟨12042201735649018538690635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16056268980865358051587513 12042201735649018538690635)
        ·
          refine ⟨18063302603473527808035953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12042201735649018538690635 18063302603473527808035953)
          ·
            refine ⟨13547476952605145856026965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18063302603473527808035953 13547476952605145856026965)
            ·
              refine ⟨39689873884585388250079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13547476952605145856026965 39689873884585388250079)
              ·
                rfl

theorem cell22_3130478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 10].length) (baseStart_3130478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130478 prefixEnd_3130478 := by exact prefixLift 3130478
  have htrace : WordTrace (prefixWord ++ tailWord_3130478) baseStart_3130478 baseEnd_3130478 := by
    simpa [prefixWord, tailWord_3130478, baseEnd_3130478] using wordTrace_append hprefix tailTrace_3130478
  have hstable : (prefixWord ++ tailWord_3130478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130478).length < 2 ^ (prefixWord ++ tailWord_3130478).sum := by decide
  have hdescent : baseEnd_3130478 < baseStart_3130478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130568 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 8]
def baseStart_3130568 : Nat := 118140960795 + 3130568 * 2 ^ 59
def prefixEnd_3130568 : Nat := 4983230072969 + 3 ^ 40 * 3130568 * 2
def baseEnd_3130568 : Nat := 357219134574358416000619

theorem tailTrace_3130568 : CollatzResearch.WordTrace tailWord_3130568 prefixEnd_3130568 357219134574358416000619 := by
  unfold tailWord_3130568
  simp only [CollatzResearch.WordTrace]
  refine ⟨57090597661247134646588179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76120796881662846195450905 57090597661247134646588179)
  ·
    refine ⟨85635896491870701969882269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57090597661247134646588179 85635896491870701969882269)
    ·
      refine ⟨32113461184451513238705851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85635896491870701969882269 32113461184451513238705851)
      ·
        refine ⟨48170191776677269858058777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32113461184451513238705851 48170191776677269858058777)
        ·
          refine ⟨36127643832507952393544083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48170191776677269858058777 36127643832507952393544083)
          ·
            refine ⟨54191465748761928590316125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36127643832507952393544083 54191465748761928590316125)
            ·
              refine ⟨20321799655785723221368547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54191465748761928590316125 20321799655785723221368547)
              ·
                refine ⟨30482699483678584832052821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20321799655785723221368547 30482699483678584832052821)
                ·
                  refine ⟨357219134574358416000619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30482699483678584832052821 357219134574358416000619)
                  ·
                    rfl

theorem cell22_3130568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 8].length) (baseStart_3130568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130568 prefixEnd_3130568 := by exact prefixLift 3130568
  have htrace : WordTrace (prefixWord ++ tailWord_3130568) baseStart_3130568 baseEnd_3130568 := by
    simpa [prefixWord, tailWord_3130568, baseEnd_3130568] using wordTrace_append hprefix tailTrace_3130568
  have hstable : (prefixWord ++ tailWord_3130568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130568).length < 2 ^ (prefixWord ++ tailWord_3130568).sum := by decide
  have hdescent : baseEnd_3130568 < baseStart_3130568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130570 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 3, 4]
def baseStart_3130570 : Nat := 118140960795 + 3130570 * 2 ^ 59
def prefixEnd_3130570 : Nat := 4983230072969 + 3 ^ 40 * 3130570 * 2
def baseEnd_3130570 : Nat := 1071658088363947909451851

theorem tailTrace_3130570 : CollatzResearch.WordTrace tailWord_3130570 prefixEnd_3130570 1071658088363947909451851 := by
  unfold tailWord_3130570
  simp only [CollatzResearch.WordTrace]
  refine ⟨28545317067121755908687291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76120845512324682423166109 28545317067121755908687291)
  ·
    refine ⟨42817975600682633863030937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28545317067121755908687291 42817975600682633863030937)
    ·
      refine ⟨32113481700511975397273203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42817975600682633863030937 32113481700511975397273203)
      ·
        refine ⟨48170222550767963095909805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32113481700511975397273203 48170222550767963095909805)
        ·
          refine ⟨18063833456537986160966177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48170222550767963095909805 18063833456537986160966177)
          ·
            refine ⟨13547875092403489620724633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18063833456537986160966177 13547875092403489620724633)
            ·
              refine ⟨10160906319302617215543475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13547875092403489620724633 10160906319302617215543475)
              ·
                refine ⟨15241359478953925823315213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10160906319302617215543475 15241359478953925823315213)
                ·
                  refine ⟨5715509804607722183743205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15241359478953925823315213 5715509804607722183743205)
                  ·
                    refine ⟨1071658088363947909451851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5715509804607722183743205 1071658088363947909451851)
                    ·
                      rfl

theorem cell22_3130570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_3130570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130570 prefixEnd_3130570 := by exact prefixLift 3130570
  have htrace : WordTrace (prefixWord ++ tailWord_3130570) baseStart_3130570 baseEnd_3130570 := by
    simpa [prefixWord, tailWord_3130570, baseEnd_3130570] using wordTrace_append hprefix tailTrace_3130570
  have hstable : (prefixWord ++ tailWord_3130570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130570).length < 2 ^ (prefixWord ++ tailWord_3130570).sum := by decide
  have hdescent : baseEnd_3130570 < baseStart_3130570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130602 : List Nat := [3, 1, 3, 1, 1, 3, 2, 4, 4]
def baseStart_3130602 : Nat := 118140960795 + 3130602 * 2 ^ 59
def prefixEnd_3130602 : Nat := 4983230072969 + 3 ^ 40 * 3130602 * 2
def baseEnd_3130602 : Nat := 357223014205970164217251

theorem tailTrace_3130602 : CollatzResearch.WordTrace tailWord_3130602 prefixEnd_3130602 357223014205970164217251 := by
  unfold tailWord_3130602
  simp only [CollatzResearch.WordTrace]
  refine ⟨28545608851092773274978515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76121623602914062066609373 28545608851092773274978515)
  ·
    refine ⟨42818413276639159912467773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28545608851092773274978515 42818413276639159912467773)
    ·
      refine ⟨16056904978739684967175415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42818413276639159912467773 16056904978739684967175415)
      ·
        refine ⟨24085357468109527450763123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16056904978739684967175415 24085357468109527450763123)
        ·
          refine ⟨36128036202164291176144685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24085357468109527450763123 36128036202164291176144685)
          ·
            refine ⟨13548013575811609191054257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36128036202164291176144685 13548013575811609191054257)
            ·
              refine ⟨10161010181858706893290693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13548013575811609191054257 10161010181858706893290693)
              ·
                refine ⟨1905189409098507542492005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10161010181858706893290693 1905189409098507542492005)
                ·
                  refine ⟨357223014205970164217251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1905189409098507542492005 357223014205970164217251)
                  ·
                    rfl

theorem cell22_3130602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_3130602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130602 prefixEnd_3130602 := by exact prefixLift 3130602
  have htrace : WordTrace (prefixWord ++ tailWord_3130602) baseStart_3130602 baseEnd_3130602 := by
    simpa [prefixWord, tailWord_3130602, baseEnd_3130602] using wordTrace_append hprefix tailTrace_3130602
  have hstable : (prefixWord ++ tailWord_3130602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130602).length < 2 ^ (prefixWord ++ tailWord_3130602).sum := by decide
  have hdescent : baseEnd_3130602 < baseStart_3130602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130643 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 3, 8]
def baseStart_3130643 : Nat := 118140960795 + 3130643 * 2 ^ 59
def prefixEnd_3130643 : Nat := 4983230072969 + 3 ^ 40 * 3130643 * 2
def baseEnd_3130643 : Nat := 1071683077755800052376627

theorem tailTrace_3130643 : CollatzResearch.WordTrace tailWord_3130643 prefixEnd_3130643 1071683077755800052376627 := by
  unfold tailWord_3130643
  simp only [CollatzResearch.WordTrace]
  refine ⟨114183930797222557102156583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76122620531481704734771055 114183930797222557102156583)
  ·
    refine ⟨171275896195833835653234875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114183930797222557102156583 171275896195833835653234875)
    ·
      refine ⟨256913844293750753479852313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171275896195833835653234875 256913844293750753479852313)
      ·
        refine ⟨192685383220313065109889235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256913844293750753479852313 192685383220313065109889235)
        ·
          refine ⟨289028074830469597664833853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192685383220313065109889235 289028074830469597664833853)
          ·
            refine ⟨108385528061426099124312695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289028074830469597664833853 108385528061426099124312695)
            ·
              refine ⟨162578292092139148686469043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108385528061426099124312695 162578292092139148686469043)
              ·
                refine ⟨243867438138208723029703565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162578292092139148686469043 243867438138208723029703565)
                ·
                  refine ⟨91450289301828271136138837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243867438138208723029703565 91450289301828271136138837)
                  ·
                    refine ⟨1071683077755800052376627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91450289301828271136138837 1071683077755800052376627)
                    ·
                      rfl

theorem cell22_3130643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 8].length) (baseStart_3130643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130643 prefixEnd_3130643 := by exact prefixLift 3130643
  have htrace : WordTrace (prefixWord ++ tailWord_3130643) baseStart_3130643 baseEnd_3130643 := by
    simpa [prefixWord, tailWord_3130643, baseEnd_3130643] using wordTrace_append hprefix tailTrace_3130643
  have hstable : (prefixWord ++ tailWord_3130643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130643).length < 2 ^ (prefixWord ++ tailWord_3130643).sum := by decide
  have hdescent : baseEnd_3130643 < baseStart_3130643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130660 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_3130660 : Nat := 118140960795 + 3130660 * 2 ^ 59
def prefixEnd_3130660 : Nat := 4983230072969 + 3 ^ 40 * 3130660 * 2
def baseEnd_3130660 : Nat := 1071688897203217674701575

theorem tailTrace_3130660 : CollatzResearch.WordTrace tailWord_3130660 prefixEnd_3130660 1071688897203217674701575 := by
  unfold tailWord_3130660
  simp only [CollatzResearch.WordTrace]
  refine ⟨57092275419080484502762717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76123033892107312670350289 57092275419080484502762717)
  ·
    refine ⟨21409603282155181688536019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57092275419080484502762717 21409603282155181688536019)
    ·
      refine ⟨32114404923232772532804029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21409603282155181688536019 32114404923232772532804029)
      ·
        refine ⟨12042901846212289699801511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32114404923232772532804029 12042901846212289699801511)
        ·
          refine ⟨18064352769318434549702267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12042901846212289699801511 18064352769318434549702267)
          ·
            refine ⟨27096529153977651824553401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18064352769318434549702267 27096529153977651824553401)
            ·
              refine ⟨20322396865483238868415051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27096529153977651824553401 20322396865483238868415051)
              ·
                refine ⟨30483595298224858302622577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20322396865483238868415051 30483595298224858302622577)
                ·
                  refine ⟨22862696473668643726966933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30483595298224858302622577 22862696473668643726966933)
                  ·
                    refine ⟨1071688897203217674701575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22862696473668643726966933 1071688897203217674701575)
                    ·
                      rfl

theorem cell22_3130660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_3130660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130660 prefixEnd_3130660 := by exact prefixLift 3130660
  have htrace : WordTrace (prefixWord ++ tailWord_3130660) baseStart_3130660 baseEnd_3130660 := by
    simpa [prefixWord, tailWord_3130660, baseEnd_3130660] using wordTrace_append hprefix tailTrace_3130660
  have hstable : (prefixWord ++ tailWord_3130660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130660).length < 2 ^ (prefixWord ++ tailWord_3130660).sum := by decide
  have hdescent : baseEnd_3130660 < baseStart_3130660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130722 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_3130722 : Nat := 118140960795 + 3130722 * 2 ^ 59
def prefixEnd_3130722 : Nat := 4983230072969 + 3 ^ 40 * 3130722 * 2
def baseEnd_3130722 : Nat := 1071710121070270179651385

theorem tailTrace_3130722 : CollatzResearch.WordTrace tailWord_3130722 prefixEnd_3130722 1071710121070270179651385 := by
  unfold tailWord_3130722
  simp only [CollatzResearch.WordTrace]
  refine ⟨28546703040984088398570605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76124541442624235729521613 28546703040984088398570605)
  ·
    refine ⟨10705013640369033149463977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28546703040984088398570605 10705013640369033149463977)
    ·
      refine ⟨8028760230276774862097983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10705013640369033149463977 8028760230276774862097983)
      ·
        refine ⟨12043140345415162293146975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8028760230276774862097983 12043140345415162293146975)
        ·
          refine ⟨18064710518122743439720463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12043140345415162293146975 18064710518122743439720463)
          ·
            refine ⟨27097065777184115159580695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18064710518122743439720463 27097065777184115159580695)
            ·
              refine ⟨40645598665776172739371043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27097065777184115159580695 40645598665776172739371043)
              ·
                refine ⟨60968397998664259109056565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40645598665776172739371043 60968397998664259109056565)
                ·
                  refine ⟨5715787312374774291474053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60968397998664259109056565 5715787312374774291474053)
                  ·
                    refine ⟨1071710121070270179651385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5715787312374774291474053 1071710121070270179651385)
                    ·
                      rfl

theorem cell22_3130722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_3130722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130722 prefixEnd_3130722 := by exact prefixLift 3130722
  have htrace : WordTrace (prefixWord ++ tailWord_3130722) baseStart_3130722 baseEnd_3130722 := by
    simpa [prefixWord, tailWord_3130722, baseEnd_3130722] using wordTrace_append hprefix tailTrace_3130722
  have hstable : (prefixWord ++ tailWord_3130722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130722).length < 2 ^ (prefixWord ++ tailWord_3130722).sum := by decide
  have hdescent : baseEnd_3130722 < baseStart_3130722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130756 : List Nat := [2, 3, 2, 1, 1, 5, 2, 1, 1, 4]
def baseStart_3130756 : Nat := 118140960795 + 3130756 * 2 ^ 59
def prefixEnd_3130756 : Nat := 4983230072969 + 3 ^ 40 * 3130756 * 2
def baseEnd_3130756 : Nat := 1071721759965105424301281

theorem tailTrace_3130756 : CollatzResearch.WordTrace tailWord_3130756 prefixEnd_3130756 1071721759965105424301281 := by
  unfold tailWord_3130756
  simp only [CollatzResearch.WordTrace]
  refine ⟨57094026122906588700510061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76125368163875451600680081 57094026122906588700510061)
  ·
    refine ⟨21410259796089970762691273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57094026122906588700510061 21410259796089970762691273)
    ·
      refine ⟨16057694847067478072018455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21410259796089970762691273 16057694847067478072018455)
      ·
        refine ⟨24086542270601217108027683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16057694847067478072018455 24086542270601217108027683)
        ·
          refine ⟨36129813405901825662041525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24086542270601217108027683 36129813405901825662041525)
          ·
            refine ⟨3387170006803296155816393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36129813405901825662041525 3387170006803296155816393)
            ·
              refine ⟨2540377505102472116862295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3387170006803296155816393 2540377505102472116862295)
              ·
                refine ⟨3810566257653708175293443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540377505102472116862295 3810566257653708175293443)
                ·
                  refine ⟨5715849386480562262940165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3810566257653708175293443 5715849386480562262940165)
                  ·
                    refine ⟨1071721759965105424301281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5715849386480562262940165 1071721759965105424301281)
                    ·
                      rfl

theorem cell22_3130756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_3130756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130756 prefixEnd_3130756 := by exact prefixLift 3130756
  have htrace : WordTrace (prefixWord ++ tailWord_3130756) baseStart_3130756 baseEnd_3130756 := by
    simpa [prefixWord, tailWord_3130756, baseEnd_3130756] using wordTrace_append hprefix tailTrace_3130756
  have hstable : (prefixWord ++ tailWord_3130756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130756).length < 2 ^ (prefixWord ++ tailWord_3130756).sum := by decide
  have hdescent : baseEnd_3130756 < baseStart_3130756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130878 : List Nat := [4, 2, 2, 3, 1, 1, 2, 2, 5]
def baseStart_3130878 : Nat := 118140960795 + 3130878 * 2 ^ 59
def prefixEnd_3130878 : Nat := 4983230072969 + 3 ^ 40 * 3130878 * 2
def baseEnd_3130878 : Nat := 357254507686112590916969

theorem tailTrace_3130878 : CollatzResearch.WordTrace tailWord_3130878 prefixEnd_3130878 357254507686112590916969 := by
  unfold tailWord_3130878
  simp only [CollatzResearch.WordTrace]
  refine ⟨14274062743921399029620161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76128334634247461491307525 14274062743921399029620161)
  ·
    refine ⟨10705547057941049272215121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14274062743921399029620161 10705547057941049272215121)
    ·
      refine ⟨8029160293455786954161341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10705547057941049272215121 8029160293455786954161341)
      ·
        refine ⟨3010935110045920107810503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8029160293455786954161341 3010935110045920107810503)
        ·
          refine ⟨4516402665068880161715755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3010935110045920107810503 4516402665068880161715755)
          ·
            refine ⟨6774603997603320242573633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4516402665068880161715755 6774603997603320242573633)
            ·
              refine ⟨5080952998202490181930225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6774603997603320242573633 5080952998202490181930225)
              ·
                refine ⟨3810714748651867636447669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5080952998202490181930225 3810714748651867636447669)
                ·
                  refine ⟨357254507686112590916969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3810714748651867636447669 357254507686112590916969)
                  ·
                    rfl

theorem cell22_3130878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_3130878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130878 prefixEnd_3130878 := by exact prefixLift 3130878
  have htrace : WordTrace (prefixWord ++ tailWord_3130878) baseStart_3130878 baseEnd_3130878 := by
    simpa [prefixWord, tailWord_3130878, baseEnd_3130878] using wordTrace_append hprefix tailTrace_3130878
  have hstable : (prefixWord ++ tailWord_3130878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130878).length < 2 ^ (prefixWord ++ tailWord_3130878).sum := by decide
  have hdescent : baseEnd_3130878 < baseStart_3130878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3130882 : List Nat := [3, 4, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_3130882 : Nat := 118140960795 + 3130882 * 2 ^ 59
def prefixEnd_3130882 : Nat := 4983230072969 + 3 ^ 40 * 3130882 * 2
def baseEnd_3130882 : Nat := 1071764892340083095650895

theorem tailTrace_3130882 : CollatzResearch.WordTrace tailWord_3130882 prefixEnd_3130882 1071764892340083095650895 := by
  unfold tailWord_3130882
  simp only [CollatzResearch.WordTrace]
  refine ⟨28548161960839175230026725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76128431895571133946737933 28548161960839175230026725)
  ·
    refine ⟨5352780367657345355630011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28548161960839175230026725 5352780367657345355630011)
    ·
      refine ⟨8029170551486018033445017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5352780367657345355630011 8029170551486018033445017)
      ·
        refine ⟨6021877913614513525083763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8029170551486018033445017 6021877913614513525083763)
        ·
          refine ⟨9032816870421770287625645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6021877913614513525083763 9032816870421770287625645)
          ·
            refine ⟨3387306326408163857859617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9032816870421770287625645 3387306326408163857859617)
            ·
              refine ⟨2540479744806122893394713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3387306326408163857859617 2540479744806122893394713)
              ·
                refine ⟨1905359808604592170046035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2540479744806122893394713 1905359808604592170046035)
                ·
                  refine ⟨2858039712906888255069053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905359808604592170046035 2858039712906888255069053)
                  ·
                    refine ⟨1071764892340083095650895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2858039712906888255069053 1071764892340083095650895)
                    ·
                      rfl

theorem cell22_3130882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_3130882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3130882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3130882 prefixEnd_3130882 := by exact prefixLift 3130882
  have htrace : WordTrace (prefixWord ++ tailWord_3130882) baseStart_3130882 baseEnd_3130882 := by
    simpa [prefixWord, tailWord_3130882, baseEnd_3130882] using wordTrace_append hprefix tailTrace_3130882
  have hstable : (prefixWord ++ tailWord_3130882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3130882).length < 2 ^ (prefixWord ++ tailWord_3130882).sum := by decide
  have hdescent : baseEnd_3130882 < baseStart_3130882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3130882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
